//! The compiler's proofs (Kani): each template meets its node's contract (`compile.rs`) for
//! every child meeting its own. A child is a hole: an opaque block of symbolic length that,
//! entered, does what its contract says and nothing more (its exit chosen by its symbolic
//! value; A, X and the scratch slots it may use havocked). The template's own instructions are
//! run by `bpf::step`, `run_bpf`'s, and each is checked as the kernel checks one
//! (`bpf::insn_ok`), its jumps inside the fragment or onto its exits.
//!
//! The induction (every tree, from these): by the tree's height. A leaf's template has no hole:
//! its proof is its contract. A node's real code is its template's with each hole replaced by
//! the child's code for the exits (or half and depth) the template asked for; by the
//! hypothesis that code meets the hole's contract, from any state; seccomp's jumps go only
//! forward, so a run of the real code is, hole by hole, a run of the proof's (entering a hole
//! at its start, leaving at one of its exits with a state the hole's havoc covers), and a jump
//! into a hole's middle is refused by the proof. A child's value in the proof is any value, and
//! its facts (`stat`, `as_const`, `hi_zero`) any consistent with it; the node's `eval` is its
//! line of `expr.rs` with the child a leaf of that value (each line uses a child only through
//! its value). So the node's code meets its contract.

use crate::bpf::*;
use crate::compile::*;
use crate::expr::*;
use kani::any;
use libc::{seccomp_data, sock_filter};

#[derive(Clone, Copy)]
enum Hole {
    /// a condition's: to `t` if `v`, else `f`
    Cond { t: usize, f: usize, v: bool },
    /// a pattern list's: requires A = `d.nr`; to `t` if `v`, else `f`
    Pats { t: usize, f: usize, v: bool },
    /// a value's half `v`, at depth `k`
    Val { v: u32, k: usize },
    /// a statement's: returns `v`
    Stmt { v: u32 },
}

#[derive(Clone, Copy)]
enum Seg {
    I(sock_filter),
    H(Hole, usize),
    /// nothing (`Code::empty`: a segment, so that every fragment of a template has one shape)
    Skip,
    /// `Code::ja`: JA `k`, absent if `k` is 0
    Ja(u32),
    /// `Code::jcond`, `len` long: by its contract, to `t` if A `code` (K or X) holds, else `f`
    J { code: u16, k: u32, t: usize, f: usize, len: usize },
    /// `Code::cmp_half`, `len` long: by its contract, the jumps on halves `a`, `b`
    Half { j: Jumps, a: u32, b: u32, len: usize },
}

/// A fragment: instructions and holes, at most `SEGS` (each template's are fewer). Plain
/// index loops, no iterator adapters: they are what Kani's symbolic execution is slow on.
const PAD: Seg = Seg::Skip;
/// `N`: the template's most segments (a harness's own: each copy of a fragment costs the
/// solver its size).
struct Frag<const N: usize> {
    segs: [Seg; N],
    n: usize,
    /// the compiler refused the node: no claim
    refused: bool,
}

impl<const N: usize> Frag<N> {
    fn one(s: Seg) -> Self {
        let mut f = Frag { segs: [PAD; N], n: 1, refused: false };
        f.segs[0] = s;
        f
    }
    /// A child's hole: its code at least one instruction (a child is built only if its node
    /// isn't decided when the program is built, and then its code isn't empty: each node's
    /// proof checks its own).
    fn hole(h: Hole) -> Self {
        let len: u16 = any();
        Frag::one(Seg::H(h, len as usize + 1))
    }
}

fn seg_len(s: &Seg) -> usize {
    match s {
        Seg::I(_) => 1,
        Seg::H(_, n) => *n,
        Seg::Skip => 0,
        Seg::Ja(k) => (*k != 0) as usize,
        Seg::J { len, .. } | Seg::Half { len, .. } => *len,
    }
}

impl<const N: usize> Code for Frag<N> {
    fn refuse(_: &'static str) -> Self {
        let mut f = Frag::one(Seg::Skip);
        f.refused = true;
        f
    }
    fn empty() -> Self {
        Frag::one(Seg::Skip)
    }
    fn ja(n: u32) -> Self {
        Frag::one(Seg::Ja(n))
    }
    fn cmp_half(kb: Option<u64>, a: ValGen<Self>, b: ValGen<Self>, hi: bool, j: Jumps) -> Self {
        // the halves the holes hold (a proof's value generators make one hole each)
        let half = |g: ValGen<Self>| match g(hi, 0).segs[0] {
            Seg::H(Hole::Val { v, .. }, _) => v,
            _ => unreachable!(),
        };
        let va = half(&mut *a);
        let vb = match kb {
            Some(v) => (if hi { v >> 32 } else { v }) as u32,
            None => half(&mut *b),
        };
        // any length: the template uses it only for its offsets (the real one is one of them)
        Frag::one(Seg::Half { j, a: va, b: vb, len: any::<u16>() as usize + 1 })
    }
    fn jcond(code: u16, k: u32, t: usize, f: usize) -> Self {
        // any length (as `cmp_half`'s)
        Frag::one(Seg::J { code, k, t, f, len: any::<u16>() as usize + 1 })
    }
    fn len(&self) -> usize {
        let (mut l, mut i) = (0, 0);
        while i < self.n {
            l += seg_len(&self.segs[i]);
            i += 1;
        }
        l
    }
    fn insn(code: u16, jt: u8, jf: u8, k: u32) -> Self {
        Frag::one(Seg::I(sock_filter { code, jt, jf, k }))
    }
    fn then(mut self, next: Self) -> Self {
        assert!(self.n + next.n <= N);
        self.refused |= next.refused;
        let mut i = 0;
        while i < next.n {
            self.segs[self.n + i] = next.segs[i];
            i += 1;
        }
        self.n += next.n;
        self
    }
}

#[derive(PartialEq, Eq, Debug)]
enum Out {
    Ret(u32),
    /// past the fragment's end by this much
    Exit(usize),
}

/// `i` with its opcode a constant, one of the templates' (any other fails the proof): the
/// solver then sees `step` and `insn_ok` for that opcode only. (A fragment's instructions are
/// chosen by symbolic sizes and exits, so an opcode can reach `step` as a choice among several,
/// and `step` for a symbolic opcode includes division: 19 s for one JA.)
fn constant_code(i: sock_filter) -> sock_filter {
    macro_rules! one_of {
        ($($c:ident),*) => {
            match i.code {
                $($c => sock_filter { code: $c, ..i },)*
                _ => panic!("an opcode no template emits"),
            }
        };
    }
    one_of!(LD_W_ABS, LD_W_IMM, LDX_MEM, ST, JA, JEQ_K, JGT_K, JGE_K, JEQ_X, JGT_X, JGE_X, RET_K, AND_K, OR_K, AND_X, OR_X, LSH_K, RSH_K)
}

/// A conditional jump's condition: A against K or X (`jcond`'s contract; `jcond_k` proves the
/// instructions, run by `step`, meet it).
fn holds(code: u16, s: &State, k: u32) -> bool {
    let src = if code & 0x08 != 0 { s.x } else { k };
    match code & !0x08 {
        JEQ_K => s.a == src,
        JGT_K => s.a > src,
        JGE_K => s.a >= src,
        _ => panic!("a jump no template emits"),
    }
}

fn havoc(s: &mut State, k: usize) {
    s.a = any();
    s.x = any();
    let mut i = k;
    while i < MEMWORDS {
        s.mem[i] = any();
        i += 1;
    }
}

/// A run of a fragment: where control is, where the segment being run starts, the verdict.
struct Run {
    pc: usize,
    pos: usize,
    out: Option<Out>,
}

/// One of the template's instructions at `r.pos`, checked as the kernel checks it (`left`
/// instructions after it), run if control is there.
fn insn(r: &mut Run, i: sock_filter, total: usize, reach: usize, s: &mut State, d: &seccomp_data) {
    let left = total - r.pos + reach;
    let i = constant_code(i);
    assert!(insn_ok(i, left), "an instruction the kernel refuses");
    if r.out.is_none() && r.pc == r.pos {
        match step(s, i, d) {
            Step::Next(skip) => r.pc = r.pos + 1 + skip,
            Step::Return(v) => r.out = Some(Out::Ret(v)),
        }
    }
    r.pos += 1;
}

/// Runs `fr` from its start in `s`; checks every instruction of it as the kernel would, its
/// jumps at most `reach` past the fragment's end (where an instruction is: `reach + 1` after
/// the end).
fn exec<const N: usize>(fr: &Frag<N>, s: &mut State, d: &seccomp_data, reach: usize) -> Out {
    let total = fr.len();
    let mut r = Run { pc: 0, pos: 0, out: None };
    let mut idx = 0;
    while idx < fr.n {
        let seg = fr.segs[idx];
        idx += 1;
        match seg {
            Seg::Skip => {}
            Seg::I(i) => insn(&mut r, i, total, reach, s, d),
            Seg::Ja(k) => {
                if k != 0 {
                    insn(&mut r, sock_filter { code: JA, jt: 0, jf: 0, k }, total, reach, s, d)
                }
            }
            Seg::J { code, k, t, f, len } => {
                let (pos, room) = (r.pos, total - r.pos - len + reach);
                assert!(t <= room && f <= room);
                if r.out.is_none() && r.pc == pos {
                    r.pc = pos + len + if holds(code, s, k) { t } else { f };
                } else {
                    assert!(r.out.is_some() || r.pc <= pos || r.pc >= pos + len, "a jump into a jump's trampolines");
                }
                r.pos += len;
            }
            Seg::Half { j, a, b, len } => {
                let (pos, room) = (r.pos, total - r.pos - len + reach);
                let exit = match j {
                    Jumps::One(code, t, f) => {
                        assert!(t <= room && f <= room);
                        let st = State { a, x: b, mem: [0; MEMWORDS] };
                        if holds(code | 0x08, &st, 0) { t } else { f }
                    }
                    Jumps::Order(gt, eq, lt) => {
                        assert!(gt <= room && eq <= room && lt <= room);
                        if a > b { gt } else if a == b { eq } else { lt }
                    }
                };
                if r.out.is_none() && r.pc == pos {
                    havoc(s, 0);
                    r.pc = pos + len + exit;
                } else {
                    assert!(r.out.is_some() || r.pc <= pos || r.pc >= pos + len, "a jump into a comparison");
                }
                r.pos += len;
            }
            Seg::H(h, len) => {
                let (pos, room) = (r.pos, total - r.pos - len + reach);
                if r.out.is_none() && r.pc == pos {
                    match h {
                        Hole::Cond { t, f, v } => {
                            assert!(t <= room && f <= room);
                            havoc(s, 0);
                            r.pc = pos + len + if v { t } else { f };
                        }
                        Hole::Pats { t, f, v } => {
                            assert!(s.a == d.nr as u32, "a pattern list entered without A = d.nr");
                            assert!(t <= room && f <= room);
                            havoc(s, 0);
                            r.pc = pos + len + if v { t } else { f };
                        }
                        Hole::Val { v, k } => {
                            havoc(s, k);
                            s.a = v;
                            r.pc = pos + len;
                        }
                        Hole::Stmt { v } => r.out = Some(Out::Ret(v)),
                    }
                } else {
                    assert!(r.out.is_some() || r.pc <= pos || r.pc >= pos + len, "a jump into a hole");
                }
                r.pos += len;
            }
        }
    }
    match r.out {
        Some(o) => o,
        None => {
            assert!(r.pc >= total);
            Out::Exit(r.pc - total)
        }
    }
}

fn data() -> seccomp_data {
    seccomp_data { nr: any(), arch: any(), instruction_pointer: any(), args: any() }
}

fn state() -> State {
    State { a: any(), x: any(), mem: any() }
}

fn exit() -> usize {
    any::<u16>() as usize
}

fn leaf<T>(value: T) -> Leaf<T> {
    Leaf { value, src: "" }
}

/// A `stat`, given: each harness takes the discrete facts of its children as constants (one
/// harness, or one call, per combination) and their values symbolic, consistent with them.
#[derive(Clone, Copy)]
enum St {
    No,
    Yes(bool),
}

/// A condition child of `stat` `st`: its value (the stat's, if it has one).
fn cond_val(st: St) -> (bool, Option<bool>) {
    match st {
        St::No => (any(), None),
        St::Yes(v) => (v, Some(v)),
    }
}

const STATS: [St; 3] = [St::No, St::Yes(false), St::Yes(true)];

/// The condition contract: from any state, to `t` iff `eval`; its code not empty if its `stat`
/// is None.
fn cond_contract<const N: usize>(code: Frag<N>, stat: Option<bool>, eval: bool, t: usize, f: usize) {
    if let Some(v) = stat {
        assert!(v == eval, "a stat that isn't the condition's value");
    }
    if !code.refused {
        assert!(stat.is_some() || code.len() > 0);
        let d = data();
        let mut s = state();
        assert!(exec(&code, &mut s, &d, t.max(f)) == Out::Exit(if eval { t } else { f }));
    }
}

/// A node's two condition children's values, by which child: `va` for its first.
fn two(node: &Cond, va: bool, vb: bool) -> impl Fn(&Cond) -> bool + '_ {
    move |c| match node {
        Cond::And(a, _) | Cond::Or(a, _) if core::ptr::eq(c, &**a) => va,
        _ => vb,
    }
}

/// A node's two value children's values: `va` for its first.
fn two_vals(node: &Cond, va: u64, vb: u64) -> impl Fn(&Val) -> u64 + '_ {
    move |v| match node {
        Cond::Cmp(_, a, _) if core::ptr::eq(v, &**a) => va,
        _ => vb,
    }
}

fn cond_hole<const N: usize>(v: bool) -> impl FnOnce(usize, usize) -> Frag<N> {
    move |t, f| Frag::hole(Hole::Cond { t, f, v })
}

/// `jcond`'s instructions meet its contract (`holds`), as `step` runs them; their length is the
/// one the other proofs' jump segment takes (it is theirs: `Frag::jcond`).
fn jcond_with(code: u16) {
    let (t, f, k) = (exit(), exit(), any::<u32>());
    let c = jcond_insns::<Frag<3>>(code, k, t, f);
    if !c.refused {
        let d = data();
        let mut s = state();
        let want = Out::Exit(if holds(code, &s, k) { t } else { f });
        assert!(exec(&c, &mut s, &d, t.max(f)) == want);
    }
}

macro_rules! jcond_harness {
    ($($name:ident: $code:ident;)*) => {$(
        #[kani::proof]
        #[kani::unwind(17)]
        fn $name() {
            jcond_with($code);
        }
    )*};
}
jcond_harness! {
    jcond_jeq_k: JEQ_K;
    jcond_jgt_k: JGT_K;
    jcond_jge_k: JGE_K;
    jcond_jeq_x: JEQ_X;
    jcond_jgt_x: JGT_X;
    jcond_jge_x: JGE_X;
}

#[kani::proof]
#[kani::unwind(17)]
fn static_() {
    let (v, t, f) = (any(), exit(), exit());
    cond_contract(t_static::<Frag<1>>(v, t, f), Some(v), Cond::Static(leaf(v)).eval_by(|_| false, |_| 0), t, f);
}

fn and_or(or: bool, sa: St, sb: St) {
    let ((va, sa), (vb, sb), t, f) = (cond_val(sa), cond_val(sb), exit(), exit());
    let (a, b) = (Box::new(Cond::Static(leaf(va))), Box::new(Cond::Static(leaf(vb))));
    let (node, code, stat) = if or {
        (Cond::Or(a, b), t_or::<Frag<2>>(sa, sb, cond_hole(va), cond_hole(vb), t, f), stat_and(sa.map(|v| !v), sb.map(|v| !v)).map(|v| !v))
    } else {
        (Cond::And(a, b), t_and::<Frag<2>>(sa, sb, cond_hole(va), cond_hole(vb), t, f), stat_and(sa, sb))
    };
    cond_contract(code, stat, node.eval_by(two(&node, va, vb), |_| 0), t, f);
    // (no drop: a tree's drop glue is recursive, and Kani would unwind it)
    core::mem::forget(node);
}

macro_rules! and_or_harness {
    ($($name:ident: $or:literal $sa:expr;)*) => {$(
        #[kani::proof]
        #[kani::unwind(17)]
        fn $name() {
            for sb in STATS {
                and_or($or, $sa, sb);
            }
        }
    )*};
}
and_or_harness! {
    and_no: false St::No;
    and_false: false St::Yes(false);
    and_true: false St::Yes(true);
    or_no: true St::No;
    or_false: true St::Yes(false);
    or_true: true St::Yes(true);
}

/// A value child's hole generator, for its value `v`.
fn val_hole<const N: usize>(v: u64) -> impl FnMut(bool, usize) -> Frag<N> {
    move |hi, k| Frag::hole(Hole::Val { v: if hi { (v >> 32) as u32 } else { v as u32 }, k })
}

/// A value child: `hz` its `hi_zero`, `leaf` its `as_const`'s being Some. Its value.
fn val_val(hz: bool) -> u64 {
    if hz { any::<u32>() as u64 } else { any() }
}

/// `a op b`, the children's facts given.
fn cmp_with(op: CmpOp, la: bool, lb: bool, hz: bool) {
    let (va, vb, t, f) = (val_val(hz), val_val(hz), exit(), exit());
    let (ka, kb) = (if la { Some(va) } else { None }, if lb { Some(vb) } else { None });
    let node = Cond::Cmp(op, Box::new(Val::Const(leaf(va))), Box::new(Val::Const(leaf(vb))));
    let code = t_cmp::<Frag<2>>(op, ka, kb, hz, &mut val_hole(va), &mut val_hole(vb), t, f);
    cond_contract(code, None, node.eval_by(|_| false, two_vals(&node, va, vb)), t, f);
    core::mem::forget(node);
}

macro_rules! cmp_harness {
    ($($name:ident: $op:ident $la:literal $lb:literal $hz:literal;)*) => {$(
        #[kani::proof]
        #[kani::unwind(17)]
        fn $name() {
            cmp_with(CmpOp::$op, $la, $lb, $hz);
        }
    )*};
}
/// `cmp_half`'s instructions meet its contract: A, B the halves (B a leaf's, or computed into
/// X through `M[0]`), the jumps by them.
fn half_with(leaf_b: bool, j: Jumps) {
    let (va, vb, hi) = (any::<u64>(), any::<u64>(), any::<bool>());
    let kb = if leaf_b { Some(vb) } else { None };
    let c = cmp_half_insns::<Frag<8>>(kb, &mut val_hole(va), &mut val_hole(vb), hi, j);
    let (a, b) = if hi { ((va >> 32) as u32, (vb >> 32) as u32) } else { (va as u32, vb as u32) };
    let (exit, reach) = match j {
        Jumps::One(code, t, f) => {
            let st = State { a, x: b, mem: [0; MEMWORDS] };
            (if holds(code | 0x08, &st, 0) { t } else { f }, t.max(f))
        }
        Jumps::Order(gt, eq, lt) => (if a > b { gt } else if a == b { eq } else { lt }, gt.max(eq).max(lt)),
    };
    if !c.refused {
        let d = data();
        let mut s = state();
        assert!(exec(&c, &mut s, &d, reach) == Out::Exit(exit));
    }
}

macro_rules! half_harness {
    ($($name:ident: $leaf:literal $j:ident;)*) => {$(
        #[kani::proof]
        #[kani::unwind(17)]
        fn $name() {
            half_with($leaf, $j());
        }
    )*};
}
fn jeq() -> Jumps {
    Jumps::One(JEQ_K, exit(), exit())
}
fn jgt() -> Jumps {
    Jumps::One(JGT_K, exit(), exit())
}
fn jge() -> Jumps {
    Jumps::One(JGE_K, exit(), exit())
}
fn order() -> Jumps {
    Jumps::Order(exit(), exit(), exit())
}
half_harness! {
    half_k_jeq: true jeq;
    half_k_jgt: true jgt;
    half_k_jge: true jge;
    half_k_order: true order;
    half_x_jeq: false jeq;
    half_x_jgt: false jgt;
    half_x_jge: false jge;
    half_x_order: false order;
}

// Every op, each side a leaf or computed, the high halves known 0 or not: one harness each.
cmp_harness! {
    cmp_eq_xx: Eq false false false;
    cmp_eq_xx_32: Eq false false true;
    cmp_eq_xk: Eq false true false;
    cmp_eq_xk_32: Eq false true true;
    cmp_eq_kx: Eq true false false;
    cmp_eq_kx_32: Eq true false true;
    cmp_eq_kk: Eq true true false;
    cmp_eq_kk_32: Eq true true true;
    cmp_ne_xx: Ne false false false;
    cmp_ne_xx_32: Ne false false true;
    cmp_ne_xk: Ne false true false;
    cmp_ne_xk_32: Ne false true true;
    cmp_ne_kx: Ne true false false;
    cmp_ne_kx_32: Ne true false true;
    cmp_ne_kk: Ne true true false;
    cmp_ne_kk_32: Ne true true true;
    cmp_lt_xx: Lt false false false;
    cmp_lt_xx_32: Lt false false true;
    cmp_lt_xk: Lt false true false;
    cmp_lt_xk_32: Lt false true true;
    cmp_lt_kx: Lt true false false;
    cmp_lt_kx_32: Lt true false true;
    cmp_lt_kk: Lt true true false;
    cmp_lt_kk_32: Lt true true true;
    cmp_le_xx: Le false false false;
    cmp_le_xx_32: Le false false true;
    cmp_le_xk: Le false true false;
    cmp_le_xk_32: Le false true true;
    cmp_le_kx: Le true false false;
    cmp_le_kx_32: Le true false true;
    cmp_le_kk: Le true true false;
    cmp_le_kk_32: Le true true true;
    cmp_gt_xx: Gt false false false;
    cmp_gt_xx_32: Gt false false true;
    cmp_gt_xk: Gt false true false;
    cmp_gt_xk_32: Gt false true true;
    cmp_gt_kx: Gt true false false;
    cmp_gt_kx_32: Gt true false true;
    cmp_gt_kk: Gt true true false;
    cmp_gt_kk_32: Gt true true true;
    cmp_ge_xx: Ge false false false;
    cmp_ge_xx_32: Ge false false true;
    cmp_ge_xk: Ge false true false;
    cmp_ge_xk_32: Ge false true true;
    cmp_ge_kx: Ge true false false;
    cmp_ge_kx_32: Ge true false true;
    cmp_ge_kk: Ge true true false;
    cmp_ge_kk_32: Ge true true true;
}

#[kani::proof]
#[kani::unwind(17)]
fn if_() {
    for sc in STATS {
        let (vc, sc) = cond_val(sc);
        let (va, vb): (u32, u32) = (any(), any());
        let node = Stmt::If(Cond::Static(leaf(vc)), Box::new(Stmt::Verdict(leaf(va))), Box::new(Stmt::Verdict(leaf(vb))));
        let code = t_if::<Frag<3>>(sc, cond_hole(vc), || Frag::hole(Hole::Stmt { v: va }), || Frag::hole(Hole::Stmt { v: vb }));
        if !code.refused {
            assert!(code.len() > 0);
            let d = data();
            let mut s = state();
            let Stmt::If(_, a, _) = &node else { unreachable!() };
            let a: &Stmt = a;
            let ev = node.eval_by(&d, |_| vc, |x: &Stmt| if core::ptr::eq(x, a) { va } else { vb });
            assert!(exec(&code, &mut s, &d, 0) == Out::Ret(ev));
        }
        core::mem::forget(node);
    }
}
