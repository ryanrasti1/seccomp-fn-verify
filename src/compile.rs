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
    match far(n) {
        Some(k) => C::ja(k),
        None => C::refuse("a program longer than the kernel's limit"),
    }
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
    match c {
        Cond::Static(l) => Some(l.value),
        Cond::Cmp(..) => None,
        Cond::And(a, b) => stat_and(stat(a), stat(b)),
        Cond::Or(a, b) => stat_and(stat(a).map(|v| !v), stat(b).map(|v| !v)).map(|v| !v),
        Cond::Not(a) => stat(a).map(|v| !v),
        Cond::Paren(a) => stat(a),
    }
}

pub fn stat_and(a: Option<bool>, b: Option<bool>) -> Option<bool> {
    match (a, b) {
        (Some(false), _) | (_, Some(false)) => Some(false),
        (Some(true), s) | (s, Some(true)) => s,
        (None, None) => None,
    }
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
        Val::Shift(..) => false,
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
            if k >= MEMWORDS {
                return (C::refuse("a value nested past the scratch memory's 16 slots"), 0, 0);
            }
            let cb = b(hi, k);
            let ca = a(hi, k + 1);
            let c = cb.then(C::insn(ST, 0, 0, k as u32)).then(ca).then(C::insn(LDX_MEM, 0, 0, k as u32));
            (c, 0x08, 0) // BPF_X
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
        Field::Arg(i) if i < 6 => off_arg(i as usize),
        Field::Arg(_) => return C::refuse("d.args[i] with i past 5"),
    };
    match (hi, f.wide()) {
        (false, _) => C::insn(LD_W_ABS, 0, 0, lo_off),
        (true, true) => C::insn(LD_W_ABS, 0, 0, hi_off),
        (true, false) => C::insn(LD_W_IMM, 0, 0, 0),
    }
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
        Cond::Not(a) => cond(a, f, t),
        Cond::Paren(a) => cond(a, t, f),
    }
}

pub fn val(v: &Val, hi: bool, k: usize) -> Vec<sock_filter> {
    match v {
        Val::Field(f) => t_field(*f, hi),
        Val::Const(l) => t_const(l.value, hi),
        Val::Bit(op, a, b) => t_bit(*op, a.as_const(), b.as_const(), &mut |h, k| val(a, h, k), &mut |h, k| val(b, h, k), hi, k),
        Val::Shift(..) => Code::refuse("a shift (not yet)"),
        Val::Paren(a) => val(a, hi, k),
    }
}

pub fn stmt(s: &Stmt) -> Vec<sock_filter> {
    match s {
        Stmt::Verdict(v) | Stmt::Return(v) => t_ret(v.value),
        Stmt::Let(_, s) | Stmt::Block(s) => stmt(s),
        Stmt::If(c, a, b) | Stmt::IfThen(c, a, b) => t_if(stat(c), |t, f| cond(c, t, f), || stmt(a), || stmt(b)),
        Stmt::Match(arms, default) => arms_code(arms, default),
    }
}

fn arms_code(arms: &[Arm], default: &Stmt) -> Vec<sock_filter> {
    let Some((a, rest)) = arms.split_first() else { return stmt(default) };
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

fn pats(ps: &[Leaf<i64>], t: usize, f: usize) -> Vec<sock_filter> {
    let Some((p, rest)) = ps.split_first() else { return Code::refuse("an arm without a pattern") };
    t_pats(p.value, rest.iter().any(|p| fits(p.value)), |t, f| pats(rest, t, f), t, f)
}

/// The policy's program: its body's statement code, checked as the kernel checks it (so
/// a program this returns is one the kernel takes). Panics if the compiler refuses the tree.
pub fn compile(p: &Policy) -> Vec<sock_filter> {
    let prog = stmt(&p.body);
    check(&prog);
    prog
}
