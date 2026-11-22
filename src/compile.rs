//! The compiler: [`compile`], the tree ([`crate::expr`]) to classic BPF, a fixed template per
//! node kind with holes for its children, no optimisation across nodes.
//!
//! **The fragments and their contracts.** The program is emitted backwards: a node's code is
//! built after the code that follows it, so every jump's target, which is forward, is known.
//! Each node's code is a fragment, entered at its first instruction in any machine state:
//! - a condition's, built for its exits `t` and `f` (instructions past its end): goes to `t`
//!   if the condition holds, else to `f`;
//! - a value's, built for a half (low or high 32 bits) and a depth `k`: falls through its end,
//!   the half of the value in A, scratch slots `M[0..k]` unchanged (it uses `M[k..]`);
//! - a statement's: returns the statement's value.
//! - a pattern list's (a `match` arm's), entered with A = `d.nr`: goes to `t` if `d.nr` is
//!   one of the patterns, else to `f`.
//!
//! A template is a function of its node's own scalars, its children's facts (a condition's
//! [`stat`], a value's [`Val::as_const`], [`hi_zero`]) and its children as generators (a
//! closure from exits, or half and depth, to the child's code). It never sees a child itself, so
//! a proof of the template for every child meeting its contract is a proof for every tree
//! (`proof.rs`: each child an opaque block, its size, exits and value symbolic).
//!
//! The code type is [`Code`]: the program's `Vec<sock_filter>`, or the proofs' fragments
//! with holes.

use crate::bpf::*;
use crate::expr::*;
use libc::sock_filter;

/// Code a template builds: instructions, and (in a proof) its children's holes.
pub trait Code: Sized {
    /// The compiler refuses the tree (`why`): the program's code panics. (Not a `Result`: a
    /// proof's fragment in one costs Kani's symbolic execution 10x, through its layout.)
    fn refuse(why: &'static str) -> Self;
    fn empty() -> Self;
    /// `jump(n)`: nothing if `n` is 0, else `JA n` (its own method: a proof's fragment keeps
    /// one shape for both, a JA that may be absent)
    fn ja(n: u32) -> Self;
    fn len(&self) -> usize;
    /// [`jcond`]'s code (a method: a proof's fragment holds it as one jump, by its contract,
    /// which `proof::jcond_k` proves of this, the code itself)
    fn jcond(code: u16, k: u32, t: usize, f: usize) -> Self {
        jcond_insns(code, k, t, f)
    }
    fn insn(code: u16, jt: u8, jf: u8, k: u32) -> Self;
    /// [`cmp_half`]'s code (a method, as `jcond`: `proof::half_*` prove it, the other proofs
    /// hold it by its contract)
    fn cmp_half(kb: Option<u64>, a: ValGen<Self>, b: ValGen<Self>, hi: bool, j: Jumps) -> Self {
        cmp_half_insns(kb, a, b, hi, j)
    }
    /// `self`, refused (`why`) if `c`: a refusal of code already built, so that a proof's
    /// fragment keeps one shape either way.
    fn refuse_if(self, c: bool, why: &'static str) -> Self;
    /// `self` then `next`
    fn then(self, next: Self) -> Self;
}

impl Code for Vec<sock_filter> {
    fn refuse(why: &'static str) -> Self {
        panic!("seccomp_fn_verify::compile: {why}")
    }
    fn empty() -> Self {
        vec![]
    }
    fn ja(n: u32) -> Self {
        if n == 0 { vec![] } else { Self::insn(JA, 0, 0, n) }
    }
    fn len(&self) -> usize {
        <[sock_filter]>::len(self)
    }
    fn insn(code: u16, jt: u8, jf: u8, k: u32) -> Self {
        vec![sock_filter { code, jt, jf, k }]
    }
    fn refuse_if(self, c: bool, why: &'static str) -> Self {
        if c {
            panic!("seccomp_fn_verify::compile: {why}")
        }
        self
    }
    fn then(mut self, mut next: Self) -> Self {
        self.append(&mut next);
        self
    }
}

/// Exits within a fragment's reach: past it, a jump's target is at most this far (the
/// program's length bounds all of them; `compile` checks the program against it).
fn far(n: usize) -> Option<u32> {
    if n < MAX_INSNS { Some(n as u32) } else { None }
}

/// To `n` instructions past the end: nothing if `n` is 0, else a JA.
pub fn jump<C: Code>(n: usize) -> C {
    C::ja(far(n).unwrap_or(0)).refuse_if(far(n).is_none(), "a program longer than the kernel's limit")
}

/// A conditional jump `code` (JEQ, JGT, JGE; by K or X) to `t` if it holds, else `f` (past the
/// returned code's end). A target past 253 is reached through a JA after the jump (a
/// trampoline: `jt`, `jf` are 8 bits; 253 leaves room for two).
pub fn jcond<C: Code>(code: u16, k: u32, t: usize, f: usize) -> C {
    C::jcond(code, k, t, f)
}

/// [`jcond`]'s instructions.
pub fn jcond_insns<C: Code>(code: u16, k: u32, t: usize, f: usize) -> C {
    const NEAR: usize = 253;
    // the jump, then up to two JAs (one shape for every case: the proofs' fragments stay one
    // shape, which keeps them fast)
    let (jt, jf, ja1, ja2) = match (t > NEAR, f > NEAR) {
        (false, false) => (t, f, 0, 0),
        (true, false) => (0, f + 1, t, 0),
        (false, true) => (t + 1, 0, f, 0),
        (true, true) => (0, 1, t + 1, f),
    };
    C::insn(code, jt as u8, jf as u8, k).then(jump(ja1)).then(jump(ja2))
}

// ---- conditions ----

/// A condition's value if it has no `d`: decided when the program is built.
pub fn stat(c: &Cond) -> Option<bool> {
    stat_by(c, stat)
}

/// `stat`'s line for `c`, its children's by `s` (as `eval_by`).
pub fn stat_by(c: &Cond, s: impl Fn(&Cond) -> Option<bool>) -> Option<bool> {
    match c {
        Cond::Static(l) => Some(l.value),
        Cond::Cmp(..) => None,
        Cond::And(a, b) => stat_and(s(a), s(b)),
        Cond::Or(a, b) => stat_and(s(a).map(|v| !v), s(b).map(|v| !v)).map(|v| !v),
        Cond::Not(a) => s(a).map(|v| !v),
        Cond::Paren(a) | Cond::Let(_, a) | Cond::Block(a) => s(a),
        Cond::Call { body, .. } | Cond::Apply { body, .. } => s(body),
        // every arm dead: the default's (its code is the default's); else its code loads nr
        Cond::Match(arms, default) => stat_match(arms, s(default), &s),
    }
}

/// A `match` of conditions, its default's stat given: each arm then the rest, from the last.
pub fn stat_match(arms: &[Arm<Cond>], default: Option<bool>, s: impl Fn(&Cond) -> Option<bool>) -> Option<bool> {
    arms.iter().rev().fold(default, |rest, a| stat_arm(dead(a, &s), s(&a.body), rest))
}

/// A `match` arm that can't match: no pattern is an i32, or its guard is decided false.
pub fn dead<B>(a: &Arm<B>, s: impl Fn(&Cond) -> Option<bool>) -> bool {
    !a.pats.iter().any(|p| fits(p.value)) || a.guard.as_ref().and_then(s) == Some(false)
}

/// An arm then the rest (of conditions): the rest's if the arm is dead, or its body decided the
/// rest's value (either way the value is the rest's, and the code the rest's); else undecided.
pub fn stat_arm(dead: bool, body: Option<bool>, rest: Option<bool>) -> Option<bool> {
    if dead || (body.is_some() && body == rest) { rest } else { None }
}

pub fn stat_and(a: Option<bool>, b: Option<bool>) -> Option<bool> {
    match (a, b) {
        (Some(false), _) | (_, Some(false)) => Some(false),
        (Some(true), s) | (s, Some(true)) => s,
        (None, None) => None,
    }
}

/// `!a`: `a` to the other exits.
pub fn t_not<C: Code>(a: impl FnOnce(usize, usize) -> C, t: usize, f: usize) -> C {
    a(f, t)
}

/// `(a)`, `let …; a`, a call (`f(d, …)`, `g(x)`), a `match` with no arm left: `a`'s code.
pub fn t_same<C: Code>(a: impl FnOnce(usize, usize) -> C, t: usize, f: usize) -> C {
    a(t, f)
}

/// `Static`
pub fn t_static<C: Code>(v: bool, t: usize, f: usize) -> C {
    jump(if v { t } else { f })
}

/// `a && b` (and `a || b`: `!(!a && !b)`, the exits swapped, [`t_or`]). A side decided when
/// the program is built leaves only the other's code, or none.
pub fn t_and<C: Code>(
    sa: Option<bool>,
    sb: Option<bool>,
    a: impl FnOnce(usize, usize) -> C,
    b: impl FnOnce(usize, usize) -> C,
    t: usize,
    f: usize,
) -> C {
    match (sa, sb) {
        (Some(false), _) | (_, Some(false)) => jump(f),
        (Some(true), _) => b(t, f),
        (_, Some(true)) => a(t, f),
        (None, None) => {
            let cb = b(t, f);
            let ca = a(0, cb.len() + f);
            ca.then(cb)
        }
    }
}

pub fn t_or<C: Code>(
    sa: Option<bool>,
    sb: Option<bool>,
    a: impl FnOnce(usize, usize) -> C,
    b: impl FnOnce(usize, usize) -> C,
    t: usize,
    f: usize,
) -> C {
    match (sa, sb) {
        (Some(true), _) | (_, Some(true)) => jump(t),
        (Some(false), _) => b(t, f),
        (_, Some(false)) => a(t, f),
        (None, None) => {
            let cb = b(t, f);
            let ca = a(cb.len() + t, 0);
            ca.then(cb)
        }
    }
}

/// A value child: its code for a half (`true`: the high one) at a depth.
pub type ValGen<'a, C> = &'a mut dyn FnMut(bool, usize) -> C;

/// A value's high half is 0 (it is a u32, or a leaf below 2^32, …): a 64-bit comparison of two
/// such is of their low halves.
pub fn hi_zero(v: &Val) -> bool {
    match v {
        Val::Field(f) => !f.wide(),
        Val::Const(l) => l.value >> 32 == 0,
        Val::Bit(op, a, b) => hz_bit(*op, hi_zero(a), hi_zero(b)),
        Val::Shift(..) | Val::Param(..) => false,
        Val::Paren(a) => hi_zero(a),
    }
}

pub fn hz_bit(op: BitOp, a: bool, b: bool) -> bool {
    match op {
        BitOp::And => a || b,
        BitOp::Or => a && b,
    }
}

/// The halves of `a` and `b` for a 32-bit operation: A = `a`'s half and the operand `b`'s, by
/// K (a leaf: its half) or X (computed: at `M[k]`, `a` above it). The source bit to or into an
/// opcode, and K.
pub fn operands<C: Code>(kb: Option<u64>, a: ValGen<C>, b: ValGen<C>, hi: bool, k: usize) -> (C, u16, u32) {
    match kb {
        Some(v) => (a(hi, k), 0, if hi { (v >> 32) as u32 } else { v as u32 }),
        None => {
            let cb = b(hi, k);
            let ca = a(hi, k + 1);
            let c = cb.then(C::insn(ST, 0, 0, k as u32)).then(ca).then(C::insn(LDX_MEM, 0, 0, k as u32));
            (c.refuse_if(k >= MEMWORDS, "a value nested past the scratch memory's 16 slots"), 0x08, 0) // BPF_X
        }
    }
}

/// A comparison's jumps on one half of each side (unsigned, 32 bits): `One(code, t, f)`, to
/// `t` if A `code` B holds, else `f`; `Order(gt, eq, lt)`, to `gt` if A > B, `eq` if A = B,
/// else `lt`.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Jumps {
    One(u16, usize, usize),
    Order(usize, usize, usize),
}

/// A half of `a` and of `b` (a leaf: K), then the jumps.
pub fn cmp_half<C: Code>(kb: Option<u64>, a: ValGen<C>, b: ValGen<C>, hi: bool, j: Jumps) -> C {
    C::cmp_half(kb, a, b, hi, j)
}

/// [`cmp_half`]'s instructions.
pub fn cmp_half_insns<C: Code>(kb: Option<u64>, a: ValGen<C>, b: ValGen<C>, hi: bool, j: Jumps) -> C {
    let (c, src, k) = operands(kb, a, b, hi, 0);
    match j {
        Jumps::One(code, t, f) => c.then(jcond(code | src, k, t, f)),
        Jumps::Order(gt, eq, lt) => {
            let e: C = jcond(JEQ_K | src, k, eq, lt);
            let g = jcond(JGT_K | src, k, gt + e.len(), 0);
            c.then(g).then(e)
        }
    }
}

/// `a op b`. A leaf on the left only (`5 < d.args[0]`) is swapped to the right, the op mirrored.
/// Ne, Lt, Le are Eq, Ge, Gt with the exits swapped. Both high halves 0: the low halves'.
/// Else the high halves decide (Eq: equal and the low halves equal; Gt, Ge: above, or equal and
/// the low halves decide).
#[allow(clippy::too_many_arguments)]
pub fn t_cmp<C: Code>(
    op: CmpOp,
    ka: Option<u64>,
    kb: Option<u64>,
    hz: bool,
    a: ValGen<C>,
    b: ValGen<C>,
    t: usize,
    f: usize,
) -> C {
    if ka.is_some() && kb.is_none() {
        let op = match op {
            CmpOp::Lt => CmpOp::Gt,
            CmpOp::Le => CmpOp::Ge,
            CmpOp::Gt => CmpOp::Lt,
            CmpOp::Ge => CmpOp::Le,
            o => o,
        };
        return t_cmp(op, kb, ka, hz, b, a, t, f);
    }
    let (code, t, f) = match op {
        CmpOp::Eq => (JEQ_K, t, f),
        CmpOp::Ne => (JEQ_K, f, t),
        CmpOp::Gt => (JGT_K, t, f),
        CmpOp::Ge => (JGE_K, t, f),
        CmpOp::Lt => (JGE_K, f, t),
        CmpOp::Le => (JGT_K, f, t),
    };
    let low = cmp_half(kb, a, b, false, Jumps::One(code, t, f));
    if hz {
        return low;
    }
    let n = low.len();
    let j = if code == JEQ_K { Jumps::One(JEQ_K, 0, f + n) } else { Jumps::Order(t + n, 0, f + n) };
    cmp_half(kb, a, b, true, j).then(low)
}

// ---- values ----

/// `d.field`'s half: a load; a u32's high half, 0.
pub fn t_field<C: Code>(f: Field, hi: bool) -> C {
    let (lo_off, hi_off) = match f {
        Field::Nr => (OFF_NR, OFF_NR),
        Field::Arch => (OFF_ARCH, OFF_ARCH),
        Field::Ip => OFF_IP,
        Field::Arg(i) => off_arg(i.min(5) as usize),
    };
    let past = matches!(f, Field::Arg(i) if i > 5);
    match (hi, f.wide()) {
        (false, _) => C::insn(LD_W_ABS, 0, 0, lo_off),
        (true, true) => C::insn(LD_W_ABS, 0, 0, hi_off),
        (true, false) => C::insn(LD_W_IMM, 0, 0, 0),
    }
    .refuse_if(past, "d.args[i] with i past 5")
}

/// A leaf's half: an immediate.
pub fn t_const<C: Code>(v: u64, hi: bool) -> C {
    C::insn(LD_W_IMM, 0, 0, if hi { (v >> 32) as u32 } else { v as u32 })
}

/// `a & b`, `a | b`, a half at a time (each half the halves'). A leaf on the left only is
/// swapped to the right (both commute).
pub fn t_bit<C: Code>(op: BitOp, ka: Option<u64>, kb: Option<u64>, a: ValGen<C>, b: ValGen<C>, hi: bool, k: usize) -> C {
    if ka.is_some() && kb.is_none() {
        return t_bit(op, kb, ka, b, a, hi, k);
    }
    let (c, src, imm) = operands(kb, a, b, hi, k);
    let alu = match op {
        BitOp::And => AND_K,
        BitOp::Or => OR_K,
    };
    c.then(C::insn(alu | src, 0, 0, imm))
}

/// `(a)`: `a`'s code.
pub fn t_vsame<C: Code>(a: ValGen<C>, hi: bool, k: usize) -> C {
    a(hi, k)
}

/// `a << s`, `a >> s`, `s` a leaf below the width (Rust panics past it: refused). `wide`: `a`
/// is a u64 (else a u32: its low half alone, the high half 0). The half's code by its case
/// ([`shift_case`], [`t_shift_case`]).
pub fn t_shift<C: Code>(op: ShiftOp, wide: bool, s: u32, a: ValGen<C>, hi: bool, k: usize) -> C {
    t_shift_case(shift_case(op, wide, s, hi), a, k)
}

/// A shift's half, by case: refused; 0; one of `a`'s halves as it is (`Copy`), or shifted by an
/// op and an amount (`Shifted`); or (`Mixed`) the other half's bits moved in (by `back`, `32 -
/// s`) or-ed with this half's own shifted (by `sh`, `s`), through `M[k]`.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum ShiftCase {
    Refused,
    Zero,
    Copy(bool),
    Shifted(bool, u16, u32),
    Mixed(bool, u16, u16, u32),
}

/// The case of the half `hi` of `a op s`.
pub fn shift_case(op: ShiftOp, wide: bool, s: u32, hi: bool) -> ShiftCase {
    let shl = op == ShiftOp::Shl;
    let (sh, back) = if shl { (LSH_K, RSH_K) } else { (RSH_K, LSH_K) };
    if !wide {
        return match (s < 32, hi) {
            (false, _) => ShiftCase::Refused,
            (true, false) => ShiftCase::Shifted(false, sh, s),
            (true, true) => ShiftCase::Zero,
        };
    }
    if s >= 64 {
        return ShiftCase::Refused;
    }
    // the half the bits move toward (Shl: the high one), or the one they leave
    match (hi == shl, s) {
        (false, s) if s < 32 => ShiftCase::Shifted(hi, sh, s),
        (false, _) => ShiftCase::Zero,
        (true, 0) => ShiftCase::Copy(hi),
        (true, s) if s < 32 => ShiftCase::Mixed(hi, back, sh, s),
        // by 32 or more: the other half's, shifted by the rest
        (true, s) => ShiftCase::Shifted(!hi, sh, s - 32),
    }
}

/// A shift case's code.
pub fn t_shift_case<C: Code>(c: ShiftCase, a: ValGen<C>, k: usize) -> C {
    match c {
        ShiftCase::Refused => C::refuse("a shift by its type's width or more"),
        ShiftCase::Zero => C::insn(LD_W_IMM, 0, 0, 0),
        ShiftCase::Copy(h) => a(h, k),
        ShiftCase::Shifted(h, op, by) => a(h, k).then(C::insn(op, 0, 0, by)),
        ShiftCase::Mixed(h, back, sh, s) => a(!h, k)
            .then(C::insn(back, 0, 0, 32 - s))
            .then(C::insn(ST, 0, 0, k as u32))
            .then(a(h, k + 1))
            .then(C::insn(sh, 0, 0, s))
            .then(C::insn(LDX_MEM, 0, 0, k as u32))
            .then(C::insn(OR_X, 0, 0, 0))
            .refuse_if(k >= MEMWORDS, "a value nested past the scratch memory's 16 slots"),
    }
}

/// A closure's parameter outside its closure: refused (`Cond::Apply` holds its body with each
/// replaced).
pub fn t_param<C: Code>() -> C {
    C::refuse("a closure's parameter outside its closure")
}

/// `let …; s`, `{ s }`, a `match` with no arm left: `s`'s code.
pub fn t_ssame<C: Code>(s: impl FnOnce() -> C) -> C {
    s()
}

// ---- statements ----

/// `v`, `return v;`
pub fn t_ret<C: Code>(v: u32) -> C {
    C::insn(RET_K, 0, 0, v)
}

/// `if c { a } else { b }` (and `if c { a } b`): the condition, to `a` or past it to `b`. A
/// condition decided when the program is built leaves only its branch.
pub fn t_if<C: Code>(sc: Option<bool>, c: impl FnOnce(usize, usize) -> C, a: impl FnOnce() -> C, b: impl FnOnce() -> C) -> C {
    match sc {
        Some(true) => a(),
        Some(false) => b(),
        None => {
            let cb = b();
            let ca = a();
            let cc = c(0, ca.len());
            cc.then(ca).then(cb)
        }
    }
}

/// A `match` arm then the arms after it (`rest`): `d.nr` loaded, its patterns (to the guard or
/// past the body to `rest`), its guard (to the body or past it), its body. `fit`: one of the
/// patterns is an `i32` (`d.nr`'s type: one that isn't never matches); `sg`: the guard's
/// [`stat`] (`Some(true)` for none).
pub fn t_arm<C: Code>(
    fit: bool,
    sg: Option<bool>,
    pats: impl FnOnce(usize, usize) -> C,
    guard: impl FnOnce(usize, usize) -> C,
    body: impl FnOnce() -> C,
    rest: impl FnOnce() -> C,
) -> C {
    let cr = rest();
    if !fit || sg == Some(false) {
        return cr;
    }
    let cb = body();
    let cg = if sg == Some(true) { C::empty() } else { guard(0, cb.len()) };
    let cp = pats(0, cg.len() + cb.len());
    C::insn(LD_W_ABS, 0, 0, OFF_NR).then(cp).then(cg).then(cb).then(cr)
}

/// A `match` arm of conditions then the arms after it (`rest`), to `t` or `f`: as
/// [`t_arm`], the body's exits past the rest. A body decided when the program is built (`sb`,
/// `true` the common one) is no code: the guard's (or the patterns') exit is the body's; decided
/// the rest's value (`sr`, the rest's stat), the arm is the rest's code.
#[allow(clippy::too_many_arguments)]
pub fn t_carm<C: Code>(
    fit: bool,
    sg: Option<bool>,
    sb: Option<bool>,
    sr: Option<bool>,
    pats: impl FnOnce(usize, usize) -> C,
    guard: impl FnOnce(usize, usize) -> C,
    body: impl FnOnce(usize, usize) -> C,
    rest: impl FnOnce(usize, usize) -> C,
    t: usize,
    f: usize,
) -> C {
    let cr = rest(t, f);
    // dead, or the body decided the rest's value: the rest's code (`stat_arm`)
    if !fit || sg == Some(false) || (sb.is_some() && sb == sr) {
        return cr;
    }
    let r = cr.len();
    // where the body is: its code, and the exit to it from the guard (0: next), or the body's
    // own exit when it has no code
    let (cb, into) = match sb {
        Some(v) => (C::empty(), r + if v { t } else { f }),
        None => (body(r + t, r + f), 0),
    };
    let nb = cb.len();
    let (cg, into) = if sg == Some(true) { (C::empty(), into) } else { (guard(into, nb), 0) };
    let cp = pats(into, cg.len() + nb);
    C::insn(LD_W_ABS, 0, 0, OFF_NR).then(cp).then(cg).then(cb).then(cr)
}

/// `d.nr` (as `i64`) is `p`, an `i32`.
pub fn fits(p: i64) -> bool {
    p as i32 as i64 == p
}

/// A pattern `p` then the patterns after it (`rest`, of which `rest_fit` says one fits), A
/// being `d.nr`. `p` not an `i32`: only the rest's.
pub fn t_pats<C: Code>(p: i64, rest_fit: bool, rest: impl FnOnce(usize, usize) -> C, t: usize, f: usize) -> C {
    match (fits(p), rest_fit) {
        (false, true) => rest(t, f),
        (false, false) => C::refuse("a pattern list with no i32"),
        (true, false) => jcond(JEQ_K, p as i32 as u32, t, f),
        (true, true) => {
            let cr = rest(t, f);
            jcond::<C>(JEQ_K, p as i32 as u32, cr.len() + t, 0).then(cr)
        }
    }
}

// ---- the recursion: each node's template, its children by this ----

pub fn cond(c: &Cond, t: usize, f: usize) -> Vec<sock_filter> {
    match c {
        Cond::Static(l) => t_static(l.value, t, f),
        Cond::Cmp(op, a, b) => {
            t_cmp(*op, a.as_const(), b.as_const(), hi_zero(a) && hi_zero(b), &mut |h, k| val(a, h, k), &mut |h, k| val(b, h, k), t, f)
        }
        Cond::And(a, b) => t_and(stat(a), stat(b), |t, f| cond(a, t, f), |t, f| cond(b, t, f), t, f),
        Cond::Or(a, b) => t_or(stat(a), stat(b), |t, f| cond(a, t, f), |t, f| cond(b, t, f), t, f),
        Cond::Not(a) => t_not(|t, f| cond(a, t, f), t, f),
        Cond::Paren(a) | Cond::Let(_, a) | Cond::Block(a) => t_same(|t, f| cond(a, t, f), t, f),
        Cond::Call { body, .. } | Cond::Apply { body, .. } => t_same(|t, f| cond(body, t, f), t, f),
        Cond::Match(arms, default) => carms_code(arms, default, t, f),
    }
}

pub fn val(v: &Val, hi: bool, k: usize) -> Vec<sock_filter> {
    match v {
        Val::Field(f) => t_field(*f, hi),
        Val::Const(l) => t_const(l.value, hi),
        Val::Bit(op, a, b) => t_bit(*op, a.as_const(), b.as_const(), &mut |h, k| val(a, h, k), &mut |h, k| val(b, h, k), hi, k),
        Val::Shift(op, a, s) => t_shift(*op, a.wide(), s.value, &mut |h, k| val(a, h, k), hi, k),
        Val::Paren(a) => t_vsame(&mut |h, k| val(a, h, k), hi, k),
        Val::Param(..) => t_param(),
    }
}

pub fn stmt(s: &Stmt) -> Vec<sock_filter> {
    match s {
        Stmt::Verdict(v) | Stmt::Return(v) => t_ret(v.value),
        Stmt::Let(_, s) | Stmt::Block(s) => t_ssame(|| stmt(s)),
        Stmt::If(c, a, b) | Stmt::IfThen(c, a, b) => t_if(stat(c), |t, f| cond(c, t, f), || stmt(a), || stmt(b)),
        Stmt::Match(arms, default) => arms_code(arms, default),
    }
}

fn arms_code(arms: &[Arm<Stmt>], default: &Stmt) -> Vec<sock_filter> {
    let Some((a, rest)) = arms.split_first() else { return t_ssame(|| stmt(default)) };
    let sg = a.guard.as_ref().map_or(Some(true), stat);
    t_arm(
        a.pats.iter().any(|p| fits(p.value)),
        sg,
        |t, f| pats(&a.pats, t, f),
        |t, f| cond(a.guard.as_ref().expect("a guard: t_arm calls this only if sg isn't Some(true)"), t, f),
        || stmt(&a.body),
        || arms_code(rest, default),
    )
}

fn carms_code(arms: &[Arm<Cond>], default: &Cond, t: usize, f: usize) -> Vec<sock_filter> {
    let Some((a, rest)) = arms.split_first() else { return t_same(|t, f| cond(default, t, f), t, f) };
    let sg = a.guard.as_ref().map_or(Some(true), stat);
    t_carm(
        a.pats.iter().any(|p| fits(p.value)),
        sg,
        stat(&a.body),
        stat_match(rest, stat(default), stat),
        |t, f| pats(&a.pats, t, f),
        |t, f| cond(a.guard.as_ref().expect("a guard: t_carm calls this only if sg isn't Some(true)"), t, f),
        |t, f| cond(&a.body, t, f),
        |t, f| carms_code(rest, default, t, f),
        t,
        f,
    )
}

fn pats(ps: &[Leaf<i64>], t: usize, f: usize) -> Vec<sock_filter> {
    let Some((p, rest)) = ps.split_first() else { return Code::refuse("an arm without a pattern") };
    t_pats(p.value, rest.iter().any(|p| fits(p.value)), |t, f| pats(rest, t, f), t, f)
}

/// The policy's program: its body's statement code, checked as the kernel checks it (so
/// a program this returns is one the kernel takes). Panics if the compiler refuses the tree.
pub fn compile(p: &Policy) -> Vec<sock_filter> {
    if let Err(e) = p.check() {
        panic!("seccomp_fn_verify::compile: {e}");
    }
    let prog = stmt(&p.body);
    check(&prog);
    prog
}
