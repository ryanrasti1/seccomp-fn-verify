//! The compiler's proofs (Kani), once for every policy: each node kind's template meets its
//! node's contract for every child meeting its own. A reviewer reads the prelude (to
//! `// ===== the nodes`): the model, the contracts, the induction; then the coverage list
//! (`nodes!`), a `match` over every node kind with no wildcard, each kind's harnesses beside it.
//! What follows the list is each harness's body: a node built, its template run.
//!
//! # The model
//! A child is a **hole**: an opaque block of symbolic length that, entered at its start, does
//! what its contract says and nothing more. Its value is symbolic, and its facts (`stat`,
//! `as_const`, `hi_zero`) are given consistent with it. A condition's hole goes to its exit by
//! its value; a value's sets A to its half; a statement's returns its value; a pattern list's
//! requires A = `d.nr` and goes to its exit. Each havocs A, X and the scratch slots its contract
//! lets it use. A child is at least one instruction long unless it is decided when the program
//! is built (`stat`), and a template calls a decided child only as its whole code: every
//! contract below checks its node's code isn't empty when undecided.
//!
//! The template's own instructions are run by `bpf::step` (`run_bpf`'s) and each is checked as
//! the kernel checks one (`bpf::insn_ok`): its jumps inside the fragment or onto its exits,
//! never into a hole's middle. Two of the compiler's parts are lemmas: `jcond` (a conditional
//! jump and its trampolines) and `cmp_half` (one half of each side and the jumps), proven of
//! their instructions here and held by their contracts in the other proofs, at any length (a
//! template uses a part's length only for its offsets, so any length covers the real one).
//!
//! # The contracts (entered in any state)
//! - a condition's code, for exits `t`, `f` past its end: goes to `t` if it holds, else `f`;
//!   its `stat`, if any, is its value;
//! - a pattern list's, entered with A = `d.nr`: to `t` if `d.nr` is one of them, else `f`;
//! - a value's half at depth `k`: falls through its end, the half in A, `M[0..k]` unchanged;
//! - a statement's: returns its value, its jumps inside it.
//!
//! # The induction (every tree, from these)
//! By the tree's height. A leaf's template has no hole: its proof is its contract. A node's
//! real code is its template's with each hole replaced by the child's code for the exits (or
//! half and depth) the template asked for; by the hypothesis that code meets the hole's
//! contract, from any state. Seccomp's jumps go only forward, so a run of the real code is,
//! hole by hole, a run of the proof's: control enters a child only at its start (a jump into a
//! hole's middle fails the proof), and leaves at one of its exits in a state the hole's havoc
//! covers. A node's `eval` (`expr.rs`, `eval_by`) uses a child only through its value, and its
//! `stat` (`compile.rs`, `stat_by`) only through the child's; a harness gives both as the
//! child's symbolic ones. So the node's code meets its contract, for every value of its leaves
//! (every param). The root is a statement: its code returns `eval`, from the machine's first
//! state; `compile` checks the whole program as the kernel does.

use crate::bpf::*;
use crate::calls::Ty;
use crate::compile::*;
use crate::expr::*;
use core::mem::{ManuallyDrop, forget};
use core::ptr;
use kani::any;
use libc::{seccomp_data, sock_filter};

// ===== the model =====

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
    /// nothing (`Code::empty`: a segment, so that a template's fragment has one shape)
    Skip,
    /// `Code::ja`: JA `k`, absent if `k` is 0
    Ja(u32),
    /// `Code::jcond`, `len` long: by its contract, to `t` if A `code` (K or X) holds, else `f`
    J { code: u16, k: u32, t: usize, f: usize, len: usize },
    /// `Code::cmp_half`, `len` long: by its contract, the jumps on halves `a`, `b`
    Half { j: Jumps, a: u32, b: u32, len: usize },
}

/// A fragment of at most `N` segments (the harness's template's most). Plain index loops, no
/// iterator adapters, and one shape per template: what Kani's symbolic execution is fast on.
struct Frag<const N: usize> {
    segs: [Seg; N],
    n: usize,
    /// the compiler refused the node: no claim
    refused: bool,
}

impl<const N: usize> Frag<N> {
    fn one(s: Seg) -> Self {
        let mut f = Frag { segs: [Seg::Skip; N], n: 1, refused: false };
        f.segs[0] = s;
        f
    }
    /// A child's hole, at least one instruction long (an undecided child's code isn't empty; a
    /// decided one's is its jump, not a hole).
    fn hole(h: Hole, _: bool) -> Self {
        Frag::one(Seg::H(h, any::<u16>() as usize + 1))
    }
}

fn seg_len(s: &Seg) -> usize {
    match s {
        Seg::I(_) => 1,
        Seg::H(_, n) | Seg::J { len: n, .. } | Seg::Half { len: n, .. } => *n,
        Seg::Skip => 0,
        Seg::Ja(k) => (*k != 0) as usize,
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
    fn refuse_if(mut self, c: bool, _: &'static str) -> Self {
        self.refused |= c;
        self
    }
    fn ja(n: u32) -> Self {
        Frag::one(Seg::Ja(n))
    }
    fn jcond(code: u16, k: u32, t: usize, f: usize) -> Self {
        Frag::one(Seg::J { code, k, t, f, len: any::<u16>() as usize + 1 })
    }
    fn cmp_half(kb: Option<u64>, a: ValGen<Self>, b: ValGen<Self>, hi: bool, j: Jumps) -> Self {
        // the halves the holes hold (a proof's value generators make one hole each)
        let half = |g: ValGen<Self>| match g(hi, 0).segs[0] {
            Seg::H(Hole::Val { v, .. }, _) => v,
            _ => unreachable!(),
        };
        let a = half(a);
        let b = match kb {
            Some(v) => (if hi { v >> 32 } else { v }) as u32,
            None => half(b),
        };
        Frag::one(Seg::Half { j, a, b, len: any::<u16>() as usize + 1 })
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
        let mut i = 0;
        while i < next.n {
            self.segs[self.n + i] = next.segs[i];
            i += 1;
        }
        self.n += next.n;
        self.refused |= next.refused;
        self
    }
}

#[derive(PartialEq, Eq)]
enum Out {
    Ret(u32),
    /// past the fragment's end by this much
    Exit(usize),
}

/// `i` with its opcode a constant, one of the templates' (any other fails the proof): the
/// solver then sees `step` and `insn_ok` for that opcode alone.
fn constant_code(i: sock_filter) -> sock_filter {
    macro_rules! one_of {
        ($($c:ident),*) => {
            match i.code {
                $($c => sock_filter { code: $c, ..i },)*
                _ => panic!("an opcode no template emits"),
            }
        };
    }
    one_of!(LD_W_ABS, LD_W_IMM, LDX_MEM, ST, JA, JEQ_K, JGT_K, JGE_K, JEQ_X, JGT_X, JGE_X, RET_K, AND_K, OR_K, AND_X, OR_X, LSH_K, RSH_K, XOR_K)
}

/// A conditional jump's condition: A against K or X (`jcond`'s contract).
fn holds(code: u16, s: &State, k: u32) -> bool {
    let src = if code & 0x08 != 0 { s.x } else { k };
    match code & !0x08 {
        JEQ_K => s.a == src,
        JGT_K => s.a > src,
        JGE_K => s.a >= src,
        _ => panic!("a jump no template emits"),
    }
}

/// `cmp_half`'s contract: the exit its jumps take on halves `a`, `b`.
fn half_exit(j: Jumps, a: u32, b: u32) -> usize {
    match j {
        Jumps::One(code, t, f) => {
            if holds(code | 0x08, &State { a, x: b, mem: [0; MEMWORDS] }, 0) { t } else { f }
        }
        Jumps::Order(gt, eq, lt) => {
            if a > b {
                gt
            } else if a == b {
                eq
            } else {
                lt
            }
        }
    }
}

fn exits_of(j: Jumps) -> usize {
    match j {
        Jumps::One(_, t, f) => t.max(f),
        Jumps::Order(gt, eq, lt) => gt.max(eq).max(lt),
    }
}

/// What a hole may change: A, X, and `M[k..]`.
fn havoc(s: &mut State, k: usize) {
    s.a = any();
    s.x = any();
    let mut i = k;
    while i < MEMWORDS {
        s.mem[i] = any();
        i += 1;
    }
}

/// A run: where control is, where the segment being run starts, the verdict.
struct Run {
    pc: usize,
    pos: usize,
    out: Option<Out>,
}

/// One of the template's instructions at `r.pos`: checked as the kernel checks it (`left`
/// instructions after it, the fragment's and the `after` past it), run if control is there.
fn insn(r: &mut Run, i: sock_filter, left: usize, s: &mut State, d: &seccomp_data) {
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

/// A segment of `len` at `r.pos`, its exits at most `exits` past it and below `avail` (the
/// instructions after it): left by exit `e` if control is there; else no jump lands inside it.
fn leave(r: &mut Run, len: usize, exits: usize, avail: usize, e: Option<usize>) {
    assert!(exits < avail, "an exit past the program");
    match e {
        Some(e) => r.pc = r.pos + len + e,
        None => assert!(r.out.is_some() || r.pc <= r.pos || r.pc >= r.pos + len, "a jump into a child"),
    }
    r.pos += len;
}

/// Runs `fr` from its start in `s`, `after` instructions known past its end (a condition's:
/// its farthest exit's and one; a value's, one; a statement's, none).
fn exec<const N: usize>(fr: &Frag<N>, s: &mut State, d: &seccomp_data, after: usize) -> Out {
    let total = fr.len();
    let mut r = Run { pc: 0, pos: 0, out: None };
    let mut idx = 0;
    while idx < fr.n {
        let seg = fr.segs[idx];
        idx += 1;
        let at = r.out.is_none() && r.pc == r.pos;
        let here = total - r.pos + after; // instructions from here on
        match seg {
            Seg::Skip => {}
            Seg::I(i) => insn(&mut r, i, here - 1, s, d),
            Seg::Ja(k) => {
                if k != 0 {
                    insn(&mut r, sock_filter { code: JA, jt: 0, jf: 0, k }, here - 1, s, d)
                }
            }
            Seg::J { code, k, t, f, len } => {
                let e = if holds(code, s, k) { t } else { f };
                leave(&mut r, len, t.max(f), here - len, if at { Some(e) } else { None });
            }
            Seg::Half { j, a, b, len } => {
                if at {
                    havoc(s, 0);
                }
                let e = if at { Some(half_exit(j, a, b)) } else { None };
                leave(&mut r, len, exits_of(j), here - len, e);
            }
            Seg::H(h, len) => {
                let avail = here - len;
                match h {
                    Hole::Cond { t, f, v } | Hole::Pats { t, f, v } => {
                        if at {
                            if matches!(h, Hole::Pats { .. }) {
                                assert!(s.a == d.nr as u32, "a pattern list entered without A = d.nr");
                            }
                            havoc(s, 0);
                        }
                        leave(&mut r, len, t.max(f), avail, if at { Some(if v { t } else { f }) } else { None });
                    }
                    Hole::Val { v, k } => {
                        if at {
                            havoc(s, k);
                            s.a = v;
                        }
                        leave(&mut r, len, 0, avail, if at { Some(0) } else { None });
                    }
                    Hole::Stmt { v } => {
                        if at {
                            r.out = Some(Out::Ret(v));
                        }
                        // no exit: its jumps are inside it
                        leave(&mut r, len, 0, avail + 1, None);
                    }
                }
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

// ===== the contracts =====

/// A condition's: to `t` iff `eval`; not empty if undecided; decided (`stat`), `stat` is
/// `eval` and the code is the jump to its exit (nothing for 0, else one instruction).
fn cond_contract<const N: usize>(code: Frag<N>, d: &seccomp_data, stat: Option<bool>, eval: bool, t: usize, f: usize) {
    let e = if eval { t } else { f };
    if let Some(v) = stat {
        assert!(v == eval, "a stat that isn't the condition's value");
    }
    if !code.refused {
        match stat {
            Some(_) => assert!(code.len() == (e != 0) as usize, "a decided condition's code isn't its jump"),
            None => assert!(code.len() > 0),
        }
        assert!(exec(&code, &mut state(), d, t.max(f) + 1) == Out::Exit(e));
    }
}

/// A pattern list's: entered with A = `d.nr`, to `t` iff `eval`; not empty.
fn pats_contract<const N: usize>(code: Frag<N>, d: &seccomp_data, eval: bool, t: usize, f: usize) {
    if !code.refused {
        assert!(code.len() > 0);
        let mut s = state();
        s.a = d.nr as u32;
        assert!(exec(&code, &mut s, d, t.max(f) + 1) == Out::Exit(if eval { t } else { f }));
    }
}

/// A value's half at depth `k`: falls through, the half of `eval` in A, `M[..k]` kept; not
/// empty. (`eval` is called only if the compiler took the node: Rust panics where it refuses.)
fn val_contract<const N: usize>(code: Frag<N>, d: &seccomp_data, eval: impl FnOnce() -> u64, hi: bool, k: usize) {
    if !code.refused {
        let v = eval();
        assert!(code.len() > 0);
        let mut s = state();
        let before = s.mem;
        assert!(exec(&code, &mut s, d, 1) == Out::Exit(0));
        assert!(s.a == if hi { (v >> 32) as u32 } else { v as u32 });
        let mut i = 0;
        while i < k.min(MEMWORDS) {
            assert!(s.mem[i] == before[i], "a slot below the depth changed");
            i += 1;
        }
    }
}

/// A statement's: returns `eval`, its jumps inside it; not empty.
fn stmt_contract<const N: usize>(code: Frag<N>, d: &seccomp_data, eval: u32) {
    if !code.refused {
        assert!(code.len() > 0);
        assert!(exec(&code, &mut state(), d, 0) == Out::Ret(eval));
    }
}

// ===== symbolic inputs =====

fn data() -> seccomp_data {
    seccomp_data { nr: any(), arch: any(), instruction_pointer: any(), args: any() }
}

fn state() -> State {
    State { a: any(), x: any(), mem: any() }
}

fn exit() -> usize {
    any::<u16>() as usize
}

/// A depth: any slot. (At 16, past the last, a template that stores refuses: no claim. A
/// symbolic choice between refusing and not would merge two shapes, which Kani is slow on.)
fn depth() -> usize {
    any::<u8>() as usize % MEMWORDS
}

fn leaf<T>(value: T) -> Leaf<T> {
    Leaf { value, src: "" }
}

/// A child's `stat`, given: a harness takes its children's discrete facts as constants (one
/// harness, or one call, per combination) and their values symbolic, consistent with them.
#[derive(Clone, Copy)]
enum St {
    No,
    Yes(bool),
}
const STATS: [St; 3] = [St::No, St::Yes(false), St::Yes(true)];

/// A condition child of `stat` `st`: placeholder node, value, stat, hole generator.
#[allow(clippy::type_complexity)]
fn cond_child<const N: usize>(st: St) -> (Box<Cond>, bool, Option<bool>, impl FnOnce(usize, usize) -> Frag<N>) {
    let (v, s) = match st {
        St::No => (any(), None),
        St::Yes(v) => (v, Some(v)),
    };
    // decided: its code is the jump to its exit (the contract's), else a hole
    (Box::new(Cond::Static(leaf(v))), v, s, move |t, f| match s {
        Some(_) => jump(if v { t } else { f }),
        None => Frag::hole(Hole::Cond { t, f, v }, false),
    })
}

fn val_hole<const N: usize>(v: u64) -> impl FnMut(bool, usize) -> Frag<N> {
    move |hi, k| Frag::hole(Hole::Val { v: if hi { (v >> 32) as u32 } else { v as u32 }, k }, false)
}

fn stmt_hole<const N: usize>(v: u32) -> impl FnOnce() -> Frag<N> {
    move || Frag::hole(Hole::Stmt { v }, false)
}

fn pats_hole<const N: usize>(v: bool) -> impl FnOnce(usize, usize) -> Frag<N> {
    move |t, f| Frag::hole(Hole::Pats { t, f, v }, false)
}

/// `Some(*g)`, or none, `g` not dropped (a tree's drop glue is recursive, and Kani would unwind
/// it).
fn keep(some: bool, g: Box<Cond>) -> Option<Cond> {
    if some {
        Some(*g)
    } else {
        forget(g);
        None
    }
}

/// A child's value (or stat) by which child it is (pointer): the last pair is the default.
fn by<'a, T, V: Copy + 'a, const M: usize>(m: [(&'a T, V); M]) -> impl Fn(&T) -> V + 'a {
    move |x| {
        let mut i = 0;
        while i + 1 < M {
            if ptr::eq(x, m[i].0) {
                return m[i].1;
            }
            i += 1;
        }
        m[M - 1].1
    }
}

// ===== the nodes: the coverage list =====

/// Each part of the compiler a harness proves, by kind: every variant of the tree's enums, and
/// the lemmas.
#[allow(dead_code)]
enum Part<'a> {
    Cond(&'a Cond),
    Val(&'a Val),
    Stmt(&'a Stmt),
    Field(&'a Field),
    CmpOp(&'a CmpOp),
    BitOp(&'a BitOp),
    ShiftOp(&'a ShiftOp),
    Lemma(&'a Lemma),
}

#[allow(dead_code)]
enum Lemma {
    Jcond,
    CmpHalf,
    Pats,
}

/// `kind::variant => { harness => body; … }`: each harness, and `covered`, a `match` over
/// every kind's variants with no wildcard (a variant without harnesses doesn't compile).
macro_rules! nodes {
    ($($kind:ident :: $var:ident => { $($name:ident => $body:expr;)+ })*) => {
        $($(
            #[kani::proof]
            #[kani::unwind(17)]
            fn $name() {
                $body
            }
        )+)*
        #[allow(dead_code)]
        fn covered(p: Part) {
            match p {
                $(Part::$kind($kind::$var { .. }) => {})*
            }
        }
    };
}

nodes! {
    Lemma::Jcond => {
        jcond_jeq_k => jcond_with(JEQ_K); jcond_jgt_k => jcond_with(JGT_K); jcond_jge_k => jcond_with(JGE_K);
        jcond_jeq_x => jcond_with(JEQ_X); jcond_jgt_x => jcond_with(JGT_X); jcond_jge_x => jcond_with(JGE_X);
    }
    Lemma::CmpHalf => {
        half_k_jeq => half_with(true, Jumps::One(JEQ_K, exit(), exit()));
        half_k_jgt => half_with(true, Jumps::One(JGT_K, exit(), exit()));
        half_k_jge => half_with(true, Jumps::One(JGE_K, exit(), exit()));
        half_k_order => half_with(true, Jumps::Order(exit(), exit(), exit()));
        half_x_jeq => half_with(false, Jumps::One(JEQ_K, exit(), exit()));
        half_x_jgt => half_with(false, Jumps::One(JGT_K, exit(), exit()));
        half_x_jge => half_with(false, Jumps::One(JGE_K, exit(), exit()));
        half_x_order => half_with(false, Jumps::Order(exit(), exit(), exit()));
    }
    Lemma::Pats => { pats_ff => pats_node(false, false); pats_ft => pats_node(false, true); pats_tf => pats_node(true, false); pats_tt => pats_node(true, true); }
    Cond::Static => { static_ => static_node(); }
    Cond::Cmp => { cmp_eq_kk => cmp_node(CmpOp::Eq, true, true, false); cmp_eq_kk_32 => cmp_node(CmpOp::Eq, true, true, true); }
    Cond::And => { and_no => and_or(false, St::No); and_false => and_or(false, St::Yes(false)); and_true => and_or(false, St::Yes(true)); }
    Cond::Or => { or_no => and_or(true, St::No); or_false => and_or(true, St::Yes(false)); or_true => and_or(true, St::Yes(true)); }
    Cond::Not => { not => for st in STATS { not_node(st) }; }
    Cond::Paren => { cparen => for st in STATS { same_node(0, st) }; }
    Cond::Let => { clet => for st in STATS { same_node(1, st) }; }
    Cond::Call => { call => for st in STATS { same_node(2, st) }; }
    Cond::Apply => { apply => for st in STATS { same_node(3, st) }; }
    Cond::Block => { cblock => for st in STATS { same_node(5, st) }; }
    Cond::Match => {
        cmatch_nil => for st in STATS { same_node(4, st) };
        // a dead arm (no pattern an i32): its code the rest's, whatever its guard and body
        carm_dead_no => carm_fit(false, Some(St::No), St::No, St::No);
        carm_dead_false => carm_fit(false, Some(St::No), St::No, St::Yes(false));
        carm_dead_true => carm_fit(false, Some(St::No), St::No, St::Yes(true));
        carm_none_no_no => carm_fit(true, None, St::No, St::No);
        carm_none_no_false => carm_fit(true, None, St::No, St::Yes(false));
        carm_none_no_true => carm_fit(true, None, St::No, St::Yes(true));
        carm_none_false_no => carm_fit(true, None, St::Yes(false), St::No);
        carm_none_false_false => carm_fit(true, None, St::Yes(false), St::Yes(false));
        carm_none_false_true => carm_fit(true, None, St::Yes(false), St::Yes(true));
        carm_none_true_no => carm_fit(true, None, St::Yes(true), St::No);
        carm_none_true_false => carm_fit(true, None, St::Yes(true), St::Yes(false));
        carm_none_true_true => carm_fit(true, None, St::Yes(true), St::Yes(true));
        carm_no_no_no => carm_fit(true, Some(St::No), St::No, St::No);
        carm_no_no_false => carm_fit(true, Some(St::No), St::No, St::Yes(false));
        carm_no_no_true => carm_fit(true, Some(St::No), St::No, St::Yes(true));
        carm_no_false_no => carm_fit(true, Some(St::No), St::Yes(false), St::No);
        carm_no_false_false => carm_fit(true, Some(St::No), St::Yes(false), St::Yes(false));
        carm_no_false_true => carm_fit(true, Some(St::No), St::Yes(false), St::Yes(true));
        carm_no_true_no => carm_fit(true, Some(St::No), St::Yes(true), St::No);
        carm_no_true_false => carm_fit(true, Some(St::No), St::Yes(true), St::Yes(false));
        carm_no_true_true => carm_fit(true, Some(St::No), St::Yes(true), St::Yes(true));
        carm_false_no => carm_fit(true, Some(St::Yes(false)), St::No, St::No);
        carm_false_false => carm_fit(true, Some(St::Yes(false)), St::No, St::Yes(false));
        carm_false_true => carm_fit(true, Some(St::Yes(false)), St::No, St::Yes(true));
        carm_true_no_no => carm_fit(true, Some(St::Yes(true)), St::No, St::No);
        carm_true_no_false => carm_fit(true, Some(St::Yes(true)), St::No, St::Yes(false));
        carm_true_no_true => carm_fit(true, Some(St::Yes(true)), St::No, St::Yes(true));
        carm_true_false_no => carm_fit(true, Some(St::Yes(true)), St::Yes(false), St::No);
        carm_true_false_false => carm_fit(true, Some(St::Yes(true)), St::Yes(false), St::Yes(false));
        carm_true_false_true => carm_fit(true, Some(St::Yes(true)), St::Yes(false), St::Yes(true));
        carm_true_true_no => carm_fit(true, Some(St::Yes(true)), St::Yes(true), St::No);
        carm_true_true_false => carm_fit(true, Some(St::Yes(true)), St::Yes(true), St::Yes(false));
        carm_true_true_true => carm_fit(true, Some(St::Yes(true)), St::Yes(true), St::Yes(true));
    }
    CmpOp::Eq => { cmp_eq_xx => cmp_node(CmpOp::Eq, false, false, false); cmp_eq_xk => cmp_node(CmpOp::Eq, false, true, false); cmp_eq_kx => cmp_node(CmpOp::Eq, true, false, false);
        cmp_eq_xx_32 => cmp_node(CmpOp::Eq, false, false, true); cmp_eq_xk_32 => cmp_node(CmpOp::Eq, false, true, true); cmp_eq_kx_32 => cmp_node(CmpOp::Eq, true, false, true); }
    CmpOp::Ne => { cmp_ne_xx => cmp_node(CmpOp::Ne, false, false, false); cmp_ne_xk => cmp_node(CmpOp::Ne, false, true, false); cmp_ne_kx => cmp_node(CmpOp::Ne, true, false, false); cmp_ne_kk => cmp_node(CmpOp::Ne, true, true, false);
        cmp_ne_xx_32 => cmp_node(CmpOp::Ne, false, false, true); cmp_ne_xk_32 => cmp_node(CmpOp::Ne, false, true, true); cmp_ne_kx_32 => cmp_node(CmpOp::Ne, true, false, true); cmp_ne_kk_32 => cmp_node(CmpOp::Ne, true, true, true); }
    CmpOp::Lt => { cmp_lt_xx => cmp_node(CmpOp::Lt, false, false, false); cmp_lt_xk => cmp_node(CmpOp::Lt, false, true, false); cmp_lt_kx => cmp_node(CmpOp::Lt, true, false, false); cmp_lt_kk => cmp_node(CmpOp::Lt, true, true, false);
        cmp_lt_xx_32 => cmp_node(CmpOp::Lt, false, false, true); cmp_lt_xk_32 => cmp_node(CmpOp::Lt, false, true, true); cmp_lt_kx_32 => cmp_node(CmpOp::Lt, true, false, true); cmp_lt_kk_32 => cmp_node(CmpOp::Lt, true, true, true); }
    CmpOp::Le => { cmp_le_xx => cmp_node(CmpOp::Le, false, false, false); cmp_le_xk => cmp_node(CmpOp::Le, false, true, false); cmp_le_kx => cmp_node(CmpOp::Le, true, false, false); cmp_le_kk => cmp_node(CmpOp::Le, true, true, false);
        cmp_le_xx_32 => cmp_node(CmpOp::Le, false, false, true); cmp_le_xk_32 => cmp_node(CmpOp::Le, false, true, true); cmp_le_kx_32 => cmp_node(CmpOp::Le, true, false, true); cmp_le_kk_32 => cmp_node(CmpOp::Le, true, true, true); }
    CmpOp::Gt => { cmp_gt_xx => cmp_node(CmpOp::Gt, false, false, false); cmp_gt_xk => cmp_node(CmpOp::Gt, false, true, false); cmp_gt_kx => cmp_node(CmpOp::Gt, true, false, false); cmp_gt_kk => cmp_node(CmpOp::Gt, true, true, false);
        cmp_gt_xx_32 => cmp_node(CmpOp::Gt, false, false, true); cmp_gt_xk_32 => cmp_node(CmpOp::Gt, false, true, true); cmp_gt_kx_32 => cmp_node(CmpOp::Gt, true, false, true); cmp_gt_kk_32 => cmp_node(CmpOp::Gt, true, true, true); }
    CmpOp::Ge => { cmp_ge_xx => cmp_node(CmpOp::Ge, false, false, false); cmp_ge_xk => cmp_node(CmpOp::Ge, false, true, false); cmp_ge_kx => cmp_node(CmpOp::Ge, true, false, false); cmp_ge_kk => cmp_node(CmpOp::Ge, true, true, false);
        cmp_ge_xx_32 => cmp_node(CmpOp::Ge, false, false, true); cmp_ge_xk_32 => cmp_node(CmpOp::Ge, false, true, true); cmp_ge_kx_32 => cmp_node(CmpOp::Ge, true, false, true); cmp_ge_kk_32 => cmp_node(CmpOp::Ge, true, true, true); }
    Val::Field => { field_nr => field_with(Field::Nr, false); field_arch => field_with(Field::Arch, false); field_ip => field_with(Field::Ip, false); }
    Field::Nr => { field_nr_hi => field_with(Field::Nr, true); }
    Field::Arch => { field_arch_hi => field_with(Field::Arch, true); }
    Field::Ip => { field_ip_hi => field_with(Field::Ip, true); }
    Field::Arg => { field_arg => field_with(Field::Arg(any::<u8>() % 7), false); field_arg_hi => field_with(Field::Arg(any::<u8>() % 7), true); }
    // a typed field: each type, each half, any argument (past 5: refused)
    Field::Typed => {
        typed_u16 => typed_with(Ty::U16); typed_u32 => typed_with(Ty::U32); typed_i32 => typed_with(Ty::I32);
        typed_u64 => typed_with(Ty::U64); typed_i64 => typed_with(Ty::I64); typed_usize => typed_with(Ty::Usize); typed_ptr => typed_with(Ty::Ptr);
    }
    // i32s: each op, each side a leaf or computed (computed both: through `M[0]`); a side not
    // 32 bits refused
    Cond::SCmp => {
        scmp_eq_xk => scmp_node(CmpOp::Eq, false, true); scmp_eq_kx => scmp_node(CmpOp::Eq, true, false); scmp_eq_kk => scmp_node(CmpOp::Eq, true, true); scmp_eq_xx => scmp_node(CmpOp::Eq, false, false);
        scmp_ne_xk => scmp_node(CmpOp::Ne, false, true); scmp_ne_kx => scmp_node(CmpOp::Ne, true, false); scmp_ne_kk => scmp_node(CmpOp::Ne, true, true); scmp_ne_xx => scmp_node(CmpOp::Ne, false, false);
        scmp_lt_xk => scmp_node(CmpOp::Lt, false, true); scmp_lt_kx => scmp_node(CmpOp::Lt, true, false); scmp_lt_kk => scmp_node(CmpOp::Lt, true, true); scmp_lt_xx => scmp_node(CmpOp::Lt, false, false);
        scmp_le_xk => scmp_node(CmpOp::Le, false, true); scmp_le_kx => scmp_node(CmpOp::Le, true, false); scmp_le_kk => scmp_node(CmpOp::Le, true, true); scmp_le_xx => scmp_node(CmpOp::Le, false, false);
        scmp_gt_xk => scmp_node(CmpOp::Gt, false, true); scmp_gt_kx => scmp_node(CmpOp::Gt, true, false); scmp_gt_kk => scmp_node(CmpOp::Gt, true, true); scmp_gt_xx => scmp_node(CmpOp::Gt, false, false);
        scmp_ge_xk => scmp_node(CmpOp::Ge, false, true); scmp_ge_kx => scmp_node(CmpOp::Ge, true, false); scmp_ge_kk => scmp_node(CmpOp::Ge, true, true); scmp_ge_xx => scmp_node(CmpOp::Ge, false, false);
        scmp_wide => scmp_wide_node();
    }
    Cond::IsNull => { isnull_64 => isnull_node(false); isnull_32 => isnull_node(true); }
    // `Cond::Match` of its arms: its `eval` and `stat` lines are `Match`'s (`match_by`,
    // `stat_match`) on `m.arms`, and the recursion calls `Match`'s templates on them
    // (`carms_code`, `arms_code`), whose arms `carm_*`/`arm_*` prove; here, no arm
    Cond::CallMatch => { ccallmatch_nil => for st in STATS { same_node(6, st) }; }
    Stmt::CallMatch => { scallmatch_nil => ssame_node(3); }
    Val::Const => { const_ => const_node(); }
    Val::Bit => {
        bit_and_kx => bit_node(BitOp::And, true, false); bit_and_kk => bit_node(BitOp::And, true, true);
        bit_and_xx_0 => bit_at(BitOp::And, false, false, 0);
        bit_and_xx_1 => bit_at(BitOp::And, false, false, 1);
        bit_and_xx_2 => bit_at(BitOp::And, false, false, 2);
        bit_and_xx_3 => bit_at(BitOp::And, false, false, 3);
        bit_and_xx_4 => bit_at(BitOp::And, false, false, 4);
        bit_and_xx_5 => bit_at(BitOp::And, false, false, 5);
        bit_and_xx_6 => bit_at(BitOp::And, false, false, 6);
        bit_and_xx_7 => bit_at(BitOp::And, false, false, 7);
        bit_and_xx_8 => bit_at(BitOp::And, false, false, 8);
        bit_and_xx_9 => bit_at(BitOp::And, false, false, 9);
        bit_and_xx_10 => bit_at(BitOp::And, false, false, 10);
        bit_and_xx_11 => bit_at(BitOp::And, false, false, 11);
        bit_and_xx_12 => bit_at(BitOp::And, false, false, 12);
        bit_and_xx_13 => bit_at(BitOp::And, false, false, 13);
        bit_and_xx_14 => bit_at(BitOp::And, false, false, 14);
        bit_and_xx_15 => bit_at(BitOp::And, false, false, 15);
    }
    BitOp::And => { bit_and_xk => bit_node(BitOp::And, false, true); }
    BitOp::Or => {
        bit_or_xk => bit_node(BitOp::Or, false, true); bit_or_kx => bit_node(BitOp::Or, true, false); bit_or_kk => bit_node(BitOp::Or, true, true);
        bit_or_xx_0 => bit_at(BitOp::Or, false, false, 0);
        bit_or_xx_1 => bit_at(BitOp::Or, false, false, 1);
        bit_or_xx_2 => bit_at(BitOp::Or, false, false, 2);
        bit_or_xx_3 => bit_at(BitOp::Or, false, false, 3);
        bit_or_xx_4 => bit_at(BitOp::Or, false, false, 4);
        bit_or_xx_5 => bit_at(BitOp::Or, false, false, 5);
        bit_or_xx_6 => bit_at(BitOp::Or, false, false, 6);
        bit_or_xx_7 => bit_at(BitOp::Or, false, false, 7);
        bit_or_xx_8 => bit_at(BitOp::Or, false, false, 8);
        bit_or_xx_9 => bit_at(BitOp::Or, false, false, 9);
        bit_or_xx_10 => bit_at(BitOp::Or, false, false, 10);
        bit_or_xx_11 => bit_at(BitOp::Or, false, false, 11);
        bit_or_xx_12 => bit_at(BitOp::Or, false, false, 12);
        bit_or_xx_13 => bit_at(BitOp::Or, false, false, 13);
        bit_or_xx_14 => bit_at(BitOp::Or, false, false, 14);
        bit_or_xx_15 => bit_at(BitOp::Or, false, false, 15);
    }
    // a u32's and a u64's, each half; a u64's `Mixed` half (through `M[k]`) a harness per depth
    Val::Shift => { shl32_lo => shift_node(ShiftOp::Shl, false, false, None); shl32_hi => shift_node(ShiftOp::Shl, false, true, None); shr32_lo => shift_node(ShiftOp::Shr, false, false, None); shr32_hi => shift_node(ShiftOp::Shr, false, true, None); }
    ShiftOp::Shl => {
        shl_lo => shift_node(ShiftOp::Shl, true, false, None);
        shl_hi => shift_node(ShiftOp::Shl, true, true, None);
        shl_lo_mixed_0 => shift_node(ShiftOp::Shl, true, false, Some(0));
        shl_lo_mixed_1 => shift_node(ShiftOp::Shl, true, false, Some(1));
        shl_lo_mixed_2 => shift_node(ShiftOp::Shl, true, false, Some(2));
        shl_lo_mixed_3 => shift_node(ShiftOp::Shl, true, false, Some(3));
        shl_lo_mixed_4 => shift_node(ShiftOp::Shl, true, false, Some(4));
        shl_lo_mixed_5 => shift_node(ShiftOp::Shl, true, false, Some(5));
        shl_lo_mixed_6 => shift_node(ShiftOp::Shl, true, false, Some(6));
        shl_lo_mixed_7 => shift_node(ShiftOp::Shl, true, false, Some(7));
        shl_lo_mixed_8 => shift_node(ShiftOp::Shl, true, false, Some(8));
        shl_lo_mixed_9 => shift_node(ShiftOp::Shl, true, false, Some(9));
        shl_lo_mixed_10 => shift_node(ShiftOp::Shl, true, false, Some(10));
        shl_lo_mixed_11 => shift_node(ShiftOp::Shl, true, false, Some(11));
        shl_lo_mixed_12 => shift_node(ShiftOp::Shl, true, false, Some(12));
        shl_lo_mixed_13 => shift_node(ShiftOp::Shl, true, false, Some(13));
        shl_lo_mixed_14 => shift_node(ShiftOp::Shl, true, false, Some(14));
        shl_lo_mixed_15 => shift_node(ShiftOp::Shl, true, false, Some(15));
        shl_hi_mixed_0 => shift_node(ShiftOp::Shl, true, true, Some(0));
        shl_hi_mixed_1 => shift_node(ShiftOp::Shl, true, true, Some(1));
        shl_hi_mixed_2 => shift_node(ShiftOp::Shl, true, true, Some(2));
        shl_hi_mixed_3 => shift_node(ShiftOp::Shl, true, true, Some(3));
        shl_hi_mixed_4 => shift_node(ShiftOp::Shl, true, true, Some(4));
        shl_hi_mixed_5 => shift_node(ShiftOp::Shl, true, true, Some(5));
        shl_hi_mixed_6 => shift_node(ShiftOp::Shl, true, true, Some(6));
        shl_hi_mixed_7 => shift_node(ShiftOp::Shl, true, true, Some(7));
        shl_hi_mixed_8 => shift_node(ShiftOp::Shl, true, true, Some(8));
        shl_hi_mixed_9 => shift_node(ShiftOp::Shl, true, true, Some(9));
        shl_hi_mixed_10 => shift_node(ShiftOp::Shl, true, true, Some(10));
        shl_hi_mixed_11 => shift_node(ShiftOp::Shl, true, true, Some(11));
        shl_hi_mixed_12 => shift_node(ShiftOp::Shl, true, true, Some(12));
        shl_hi_mixed_13 => shift_node(ShiftOp::Shl, true, true, Some(13));
        shl_hi_mixed_14 => shift_node(ShiftOp::Shl, true, true, Some(14));
        shl_hi_mixed_15 => shift_node(ShiftOp::Shl, true, true, Some(15));
    }
    ShiftOp::Shr => {
        shr_lo => shift_node(ShiftOp::Shr, true, false, None);
        shr_hi => shift_node(ShiftOp::Shr, true, true, None);
        shr_lo_mixed_0 => shift_node(ShiftOp::Shr, true, false, Some(0));
        shr_lo_mixed_1 => shift_node(ShiftOp::Shr, true, false, Some(1));
        shr_lo_mixed_2 => shift_node(ShiftOp::Shr, true, false, Some(2));
        shr_lo_mixed_3 => shift_node(ShiftOp::Shr, true, false, Some(3));
        shr_lo_mixed_4 => shift_node(ShiftOp::Shr, true, false, Some(4));
        shr_lo_mixed_5 => shift_node(ShiftOp::Shr, true, false, Some(5));
        shr_lo_mixed_6 => shift_node(ShiftOp::Shr, true, false, Some(6));
        shr_lo_mixed_7 => shift_node(ShiftOp::Shr, true, false, Some(7));
        shr_lo_mixed_8 => shift_node(ShiftOp::Shr, true, false, Some(8));
        shr_lo_mixed_9 => shift_node(ShiftOp::Shr, true, false, Some(9));
        shr_lo_mixed_10 => shift_node(ShiftOp::Shr, true, false, Some(10));
        shr_lo_mixed_11 => shift_node(ShiftOp::Shr, true, false, Some(11));
        shr_lo_mixed_12 => shift_node(ShiftOp::Shr, true, false, Some(12));
        shr_lo_mixed_13 => shift_node(ShiftOp::Shr, true, false, Some(13));
        shr_lo_mixed_14 => shift_node(ShiftOp::Shr, true, false, Some(14));
        shr_lo_mixed_15 => shift_node(ShiftOp::Shr, true, false, Some(15));
        shr_hi_mixed_0 => shift_node(ShiftOp::Shr, true, true, Some(0));
        shr_hi_mixed_1 => shift_node(ShiftOp::Shr, true, true, Some(1));
        shr_hi_mixed_2 => shift_node(ShiftOp::Shr, true, true, Some(2));
        shr_hi_mixed_3 => shift_node(ShiftOp::Shr, true, true, Some(3));
        shr_hi_mixed_4 => shift_node(ShiftOp::Shr, true, true, Some(4));
        shr_hi_mixed_5 => shift_node(ShiftOp::Shr, true, true, Some(5));
        shr_hi_mixed_6 => shift_node(ShiftOp::Shr, true, true, Some(6));
        shr_hi_mixed_7 => shift_node(ShiftOp::Shr, true, true, Some(7));
        shr_hi_mixed_8 => shift_node(ShiftOp::Shr, true, true, Some(8));
        shr_hi_mixed_9 => shift_node(ShiftOp::Shr, true, true, Some(9));
        shr_hi_mixed_10 => shift_node(ShiftOp::Shr, true, true, Some(10));
        shr_hi_mixed_11 => shift_node(ShiftOp::Shr, true, true, Some(11));
        shr_hi_mixed_12 => shift_node(ShiftOp::Shr, true, true, Some(12));
        shr_hi_mixed_13 => shift_node(ShiftOp::Shr, true, true, Some(13));
        shr_hi_mixed_14 => shift_node(ShiftOp::Shr, true, true, Some(14));
        shr_hi_mixed_15 => shift_node(ShiftOp::Shr, true, true, Some(15));
    }
    Val::Paren => { vparen => vparen_node(); }
    Val::Param => { param => param_node(); }
    Stmt::Verdict => { verdict => ret_node(false); }
    Stmt::Return => { return_ => ret_node(true); }
    Stmt::Let => { slet => ssame_node(0); }
    Stmt::Block => { block => ssame_node(1); }
    Stmt::If => { if_ => for st in STATS { if_node(false, st) }; }
    Stmt::IfThen => { if_then => for st in STATS { if_node(true, st) }; }
    Stmt::Match => {
        smatch_nil => ssame_node(2);
        arm_dead => arm_fit(false, Some(St::No));
        arm_none => arm_fit(true, None);
        arm_no => arm_fit(true, Some(St::No));
        arm_false => arm_fit(true, Some(St::Yes(false)));
        arm_true => arm_fit(true, Some(St::Yes(true)));
    }
}

// ===== each harness's node =====

/// `jcond`'s instructions meet its contract (`holds`), as `step` runs them.
fn jcond_with(code: u16) {
    let (t, f, k, d) = (exit(), exit(), any::<u32>(), data());
    let c = jcond_insns::<Frag<3>>(code, k, t, f);
    if !c.refused {
        let mut s = state();
        let want = Out::Exit(if holds(code, &s, k) { t } else { f });
        assert!(exec(&c, &mut s, &d, t.max(f) + 1) == want);
    }
}

/// `cmp_half`'s instructions meet its contract: A, B the halves (B a leaf's, or computed into
/// X through `M[0]`), the jumps by them.
fn half_with(leaf_b: bool, j: Jumps) {
    let (va, vb, hi, d) = (any::<u64>(), any::<u64>(), any::<bool>(), data());
    let c = cmp_half_insns::<Frag<8>>(if leaf_b { Some(vb) } else { None }, &mut val_hole(va), &mut val_hole(vb), hi, j);
    let (a, b) = if hi { ((va >> 32) as u32, (vb >> 32) as u32) } else { (va as u32, vb as u32) };
    if !c.refused {
        assert!(exec(&c, &mut state(), &d, exits_of(j) + 1) == Out::Exit(half_exit(j, a, b)));
    }
}

/// A pattern `p` then the rest (`q`, standing for any rest: `t_pats` sees it only through
/// whether one fits, and its hole).
fn pats_node(fp: bool, fq: bool) {
    let (p, q, t, f, d) = (pat(fp), pat(fq), exit(), exit(), data());
    let code = t_pats::<Frag<4>>(p, fq, pats_hole(member(&[leaf(q)], &d)), t, f);
    pats_contract(code, &d, member(&[leaf(p), leaf(q)], &d), t, f);
}

fn static_node() {
    let (v, t, f, d) = (any(), exit(), exit(), data());
    let node = Cond::Static(leaf(v));
    cond_contract(t_static::<Frag<1>>(v, t, f), &d, stat_by(&node, |_| None), node.eval_by(&d, |_| false, |_| 0), t, f);
}

fn and_or(or: bool, sa: St) {
    for sb in STATS {
        let (t, f, d) = (exit(), exit(), data());
        let (a, va, sa, ha) = cond_child::<2>(sa);
        let (b, vb, sb, hb) = cond_child::<2>(sb);
        let (node, code) = if or { (Cond::Or(a, b), t_or(sa, sb, ha, hb, t, f)) } else { (Cond::And(a, b), t_and(sa, sb, ha, hb, t, f)) };
        let (Cond::And(a, b) | Cond::Or(a, b)) = &node else { unreachable!() };
        let stat = stat_by(&node, by([(&**a, sa), (&**b, sb)]));
        let eval = node.eval_by(&d, by([(&**a, va), (&**b, vb)]), |_| 0);
        cond_contract(code, &d, stat, eval, t, f);
        // (no drop: a tree's drop glue is recursive, and Kani would unwind it)
        forget(node);
    }
}

fn not_node(st: St) {
    let (t, f, d) = (exit(), exit(), data());
    let (a, v, s, h) = cond_child::<1>(st);
    let node = Cond::Not(a);
    cond_contract(t_not(h, t, f), &d, stat_by(&node, |_| s), node.eval_by(&d, |_| v, |_| 0), t, f);
    forget(node);
}

/// A node whose code is its one child's: `(a)`, `let …; a`, `f(d, …)`, `g(x)`, `{ a }`, `match`
/// of no arm.
fn same_node(kind: u8, st: St) {
    let (t, f, d) = (exit(), exit(), data());
    let (a, v, s, h) = cond_child::<1>(st);
    let node = match kind {
        0 => Cond::Paren(a),
        1 => Cond::Let(Let::Plain(""), a),
        2 => Cond::Call { name: "", args: vec![], d: "", body: a },
        3 => Cond::Apply { name: "", args: vec![], body: a },
        5 => Cond::Block(a),
        6 => Cond::CallMatch(CallMatch { pats: vec![], arms: vec![], default: a }),
        _ => Cond::Match(vec![], a),
    };
    cond_contract(t_same(h, t, f), &d, stat_by(&node, |_| s), node.eval_by(&d, |_| v, |_| 0), t, f);
    forget(node);
}

/// An arm of conditions (one pattern `p`, standing for any: `t_carm` sees the patterns only
/// through whether one fits, and their hole), its guard (`None`: none) and body, then the rest
/// (the default, standing for the arms after it: their `match`'s stat and value). The node's
/// lines are `stat_match` and `match_by` (`Cond::Match`'s), on the arms in a stack array: Kani
/// loses a `Vec`'s length once it is inside another on the heap.
/// A pattern that is an i32 (`fit`) or isn't: every value of either kind (`x ^ 1 << 40` maps
/// every i32 to one that isn't). `fit` a constant: the template branches on it, and one shape
/// per call keeps the proof fast.
fn pat(fit: bool) -> i64 {
    let x: i64 = any();
    let p = if fit { x as i32 as i64 } else if fits(x) { x ^ 1 << 40 } else { x };
    assert!(fits(p) == fit);
    p
}

fn carm_fit(fit: bool, guard: Option<St>, sb: St, sr: St) {
    let (p, t, f, d) = (pat(fit), exit(), exit(), data());
    let (g, vg, sg, hg) = cond_child::<6>(guard.unwrap_or(St::Yes(true)));
    let (b, vb, sb, hb) = cond_child::<6>(sb);
    let (r, vr, sr, hr) = cond_child::<6>(sr);
    // (no drop: a tree's drop glue is recursive, and Kani would unwind it)
    let arms = ManuallyDrop::new([Arm { pats: vec![leaf(p)], guard: keep(guard.is_some(), g), body: *b }]);
    let r = ManuallyDrop::new(r);
    let none = Cond::Static(leaf(true));
    let a = &arms[0];
    let gp = a.guard.as_ref().unwrap_or(&none);
    let s = by([(gp, sg), (&a.body, sb), (&**r, sr)]);
    let stat = stat_match(&*arms, s(&r), &s);
    let c = by([(gp, vg), (&a.body, vb), (&**r, vr)]);
    let eval = match_by(&*arms, &**r, &d, &c, &c);
    let code = t_carm(fit, sg, sb, sr, pats_hole(member(&a.pats, &d)), hg, hb, hr, t, f);
    cond_contract(code, &d, stat, eval, t, f);
}

/// `a op b`, the children's facts given: each a leaf or computed (`la`, `lb`), both high halves
/// known 0 (`hz`) or not.
fn cmp_node(op: CmpOp, la: bool, lb: bool, hz: bool) {
    let val = |hz: bool| -> u64 { if hz { any::<u32>() as u64 } else { any() } };
    let (va, vb, t, f, d) = (val(hz), val(hz), exit(), exit(), data());
    let node = Cond::Cmp(op, Box::new(Val::Const(leaf(va))), Box::new(Val::Const(leaf(vb))));
    let Cond::Cmp(_, a, b) = &node else { unreachable!() };
    let eval = node.eval_by(&d, |_| false, by([(&**a, va), (&**b, vb)]));
    let code = t_cmp::<Frag<2>>(op, la.then_some(va), lb.then_some(vb), hz, &mut val_hole(va), &mut val_hole(vb), t, f);
    cond_contract(code, &d, stat_by(&node, |_| None), eval, t, f);
    forget(node);
}

fn field_with(field: Field, hi: bool) {
    let (k, d) = (depth(), data());
    let node = Val::Field(field);
    val_contract(t_field::<Frag<2>>(field, hi), &d, || node.eval_by(&d, |_| 0, |_| true), hi, k);
}

fn typed_with(ty: Ty) {
    let hi = any::<bool>();
    field_with(Field::Typed { call: "", name: "", arg: any::<u8>() % 7, ty }, hi);
}

/// `a op b` of i32s, each side a leaf or computed: the values any i32s' bits (zero-extended).
fn scmp_node(op: CmpOp, la: bool, lb: bool) {
    let (va, vb, t, f, d) = (any::<u32>() as u64, any::<u32>() as u64, exit(), exit(), data());
    let node = Cond::SCmp(op, Box::new(Val::Const(leaf(va))), Box::new(Val::Const(leaf(vb))));
    let Cond::SCmp(_, a, b) = &node else { unreachable!() };
    let eval = node.eval_by(&d, |_| false, by([(&**a, va), (&**b, vb)]));
    let code = t_scmp::<Frag<8>>(op, la.then_some(va), lb.then_some(vb), true, &mut val_hole(va), &mut val_hole(vb), t, f);
    cond_contract(code, &d, stat_by(&node, |_| None), eval, t, f);
    forget(node);
}

/// A side that isn't 32 bits: refused.
fn scmp_wide_node() {
    let op = CmpOp::Ge;
    let (va, vb) = (any::<u64>(), any::<u64>());
    let code = t_scmp::<Frag<8>>(op, None, Some(vb), false, &mut val_hole(va), &mut val_hole(vb), exit(), exit());
    assert!(code.refused);
}

fn isnull_node(hz: bool) {
    let va = if hz { any::<u32>() as u64 } else { any() };
    let (t, f, d) = (exit(), exit(), data());
    let node = Cond::IsNull(Box::new(Val::Const(leaf(va))));
    let eval = node.eval_by(&d, |_| false, |_| va);
    let code = t_isnull::<Frag<2>>(hz, &mut val_hole(va), t, f);
    cond_contract(code, &d, stat_by(&node, |_| None), eval, t, f);
    forget(node);
}


fn const_node() {
    let (v, hi, k, d) = (any::<u64>(), any::<bool>(), depth(), data());
    let node = Val::Const(leaf(v));
    val_contract(t_const::<Frag<1>>(v, hi), &d, || node.eval_by(&d, |_| 0, |_| true), hi, k);
}

/// `a & b`, `a | b`, each side a leaf or computed, at any depth (computed on both sides,
/// through `M[k]`: a harness per depth, `bit_at`: a store and a load at a symbolic slot cost the
/// solver 10x).
fn bit_node(op: BitOp, la: bool, lb: bool) {
    bit_at(op, la, lb, depth())
}

fn bit_at(op: BitOp, la: bool, lb: bool, k: usize) {
    let (va, vb, hi, d) = (any::<u64>(), any::<u64>(), any::<bool>(), data());
    let node = Val::Bit(op, Box::new(Val::Const(leaf(va))), Box::new(Val::Const(leaf(vb))));
    let Val::Bit(_, a, b) = &node else { unreachable!() };
    let code = t_bit::<Frag<5>>(op, la.then_some(va), lb.then_some(vb), &mut val_hole(va), &mut val_hole(vb), hi, k);
    val_contract(code, &d, || node.eval_by(&d, by([(&**a, va), (&**b, vb)]), |_| true), hi, k);
    forget(node);
}

/// `a << s`, `a >> s`: `a` a u64 (a leaf's placeholder) or a u32 (`d.arch`'s), `s` any, the
/// half `hi`. `t_shift` is `t_shift_case` of `shift_case`: each case's code is checked in its
/// own arm, the case's opcodes (asserted) as constants (one shape each: Kani merging the cases'
/// fragments took 99 s).
fn shift_node(op: ShiftOp, wide: bool, hi: bool, at: Option<usize>) {
    let (sh, back) = if op == ShiftOp::Shl { (LSH_K, RSH_K) } else { (RSH_K, LSH_K) };
    // `Mixed` stores at `M[k]`: a harness per depth (`at`); every other case at any depth
    let k = at.unwrap_or_else(depth);
    let (va, s, d) = (any::<u64>(), any::<u32>(), data());
    let a = Box::new(if wide { Val::Const(leaf(va)) } else { Val::Field(Field::Arch) });
    let node = ManuallyDrop::new(Val::Shift(op, a, leaf(s)));
    let eval = || node.eval_by(&d, |_| va, |_| wide);
    let a = &mut val_hole(va);
    match (shift_case(op, wide, s, hi), at) {
        (ShiftCase::Mixed(h, b, o, x), Some(_)) => {
            assert!(b == back && o == sh);
            val_contract(t_shift_case::<Frag<7>>(ShiftCase::Mixed(h, back, sh, x), a, k), &d, eval, hi, k)
        }
        (_, Some(_)) => {}
        (ShiftCase::Refused, None) => assert!(t_shift_case::<Frag<7>>(ShiftCase::Refused, a, k).refused),
        (ShiftCase::Zero, None) => val_contract(t_shift_case::<Frag<7>>(ShiftCase::Zero, a, k), &d, eval, hi, k),
        (ShiftCase::Copy(h), None) => val_contract(t_shift_case::<Frag<7>>(ShiftCase::Copy(h), a, k), &d, eval, hi, k),
        (ShiftCase::Shifted(h, o, b), None) => {
            assert!(o == sh);
            val_contract(t_shift_case::<Frag<7>>(ShiftCase::Shifted(h, sh, b), a, k), &d, eval, hi, k)
        }
        // each depth's harness
        (ShiftCase::Mixed(..), None) => {}
    }
}

fn vparen_node() {
    let (va, hi, k, d) = (any::<u64>(), any::<bool>(), depth(), data());
    let node = Val::Paren(Box::new(Val::Const(leaf(va))));
    val_contract(t_vsame::<Frag<1>>(&mut val_hole(va), hi, k), &d, || node.eval_by(&d, |_| va, |_| true), hi, k);
    forget(node);
}

fn param_node() {
    assert!(t_param::<Frag<1>>().refused);
}

fn ret_node(ret: bool) {
    let (v, d) = (any::<u32>(), data());
    let node = if ret { Stmt::Return(leaf(v)) } else { Stmt::Verdict(leaf(v)) };
    stmt_contract(t_ret::<Frag<1>>(v), &d, node.eval_by(&d, |_| false, |_| 0));
}

/// A statement whose code is its one child's: `let …; s`, `{ s }`, a `match` of no arm.
fn ssame_node(kind: u8) {
    let (v, d) = (any::<u32>(), data());
    let a = Box::new(Stmt::Verdict(leaf(v)));
    let node = match kind {
        0 => Stmt::Let(Let::Plain(""), a),
        1 => Stmt::Block(a),
        3 => Stmt::CallMatch(CallMatch { pats: vec![], arms: vec![], default: a }),
        _ => Stmt::Match(vec![], a),
    };
    stmt_contract(t_ssame::<Frag<1>>(stmt_hole(v)), &d, node.eval_by(&d, |_| false, |_| v));
    forget(node);
}

fn if_node(then: bool, sc: St) {
    let d = data();
    let (c, vc, sc, hc) = cond_child::<3>(sc);
    let (va, vb): (u32, u32) = (any(), any());
    let (a, b) = (Box::new(Stmt::Verdict(leaf(va))), Box::new(Stmt::Verdict(leaf(vb))));
    let node = if then { Stmt::IfThen(*c, a, b) } else { Stmt::If(*c, a, b) };
    let (Stmt::If(_, a, b) | Stmt::IfThen(_, a, b)) = &node else { unreachable!() };
    let eval = node.eval_by(&d, |_| vc, by([(&**a, va), (&**b, vb)]));
    stmt_contract(t_if(sc, hc, stmt_hole(va), stmt_hole(vb)), &d, eval);
    forget(node);
}

/// A statement arm (as `carm_node`), then the rest (the default, standing for the arms after).
fn arm_fit(fit: bool, guard: Option<St>) {
    let (p, d) = (pat(fit), data());
    let (g, vg, sg, hg) = cond_child::<6>(guard.unwrap_or(St::Yes(true)));
    let (vb, vr): (u32, u32) = (any(), any());
    let arms = ManuallyDrop::new([Arm { pats: vec![leaf(p)], guard: keep(guard.is_some(), g), body: Stmt::Verdict(leaf(vb)) }]);
    let r = Stmt::Verdict(leaf(vr));
    let a = &arms[0];
    let eval = match_by(&*arms, &r, &d, &|_: &Cond| vg, &by([(&a.body, vb), (&r, vr)]));
    let code = t_arm(fit, sg, pats_hole(member(&a.pats, &d)), hg, stmt_hole(vb), stmt_hole(vr));
    stmt_contract(code, &d, eval);
}
