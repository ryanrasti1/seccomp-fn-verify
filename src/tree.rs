//! A policy's tree as `const` data ([`Tree`]), and the check that it is the policy.
//!
//! `seccomp_fn::tree!(policy)` (not trusted) emits a [`Tree`]: the tree of `expr.rs` with every
//! child a `&'static` reference and every leaf a static expression of the params ([`S`]: a
//! const, a param, an operator on them). It is data, evaluated by rustc in a `const` item: no
//! code of the compiler's runs where it is used. [`Tree::build`] gives the tree for the params'
//! values; [`filter!`](crate::filter) makes the filter (`compile` of it) and the check
//! (`eval` of it is the policy, for a symbolic `d`) from one list of params, and
//! [`harnesses!`](crate::harnesses) the Kani harnesses that call the check (in the caller's
//! `#[cfg(kani)] mod proof`).
//!
//! So the claim is `run_bpf(filter(params), d) == policy(params)(d)`: the compiler's proof
//! (`proof.rs`: the program is `eval` of the tree), then the check (`eval` of the tree is the
//! policy), on the same `build` of the same `Tree`. Neither needs `build` or [`S`] to mean what
//! Rust means: a tree the compiler got wrong fails the check. (The print and the round trip,
//! `print.rs` and `bpf!`'s, are a convenience: an error at compile time, naming the construct.)

use crate::expr::*;
use libc::seccomp_data;

/// A static expression of the params, on `u64`s (a param's value `as u64`; a condition nonzero
/// for true). Its meaning matters only in that it is a function of the params: the check
/// compares the tree it builds with the policy.
#[derive(Clone, Copy, Debug)]
pub enum S {
    Const(u64),
    Param(u8),
    Not(&'static S),
    Bin(&'static (SOp, S, S)),
    /// `as u32`
    Low(&'static S),
}

#[derive(Clone, Copy, Debug)]
pub enum SOp {
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    And,
    Or,
    BitAnd,
    BitOr,
    BitXor,
    Add,
    Sub,
    Mul,
    Div,
}

impl S {
    pub fn eval(&self, p: &[u64]) -> u64 {
        match *self {
            S::Const(v) => v,
            S::Param(i) => p[i as usize],
            S::Not(a) => (a.eval(p) == 0) as u64,
            S::Low(a) => a.eval(p) as u32 as u64,
            S::Bin(&(op, ref a, ref b)) => {
                let (a, b) = (a.eval(p), b.eval(p));
                match op {
                    SOp::Eq => (a == b) as u64,
                    SOp::Ne => (a != b) as u64,
                    SOp::Lt => (a < b) as u64,
                    SOp::Le => (a <= b) as u64,
                    SOp::Gt => (a > b) as u64,
                    SOp::Ge => (a >= b) as u64,
                    SOp::And => (a != 0 && b != 0) as u64,
                    SOp::Or => (a != 0 || b != 0) as u64,
                    SOp::BitAnd => a & b,
                    SOp::BitOr => a | b,
                    SOp::BitXor => a ^ b,
                    SOp::Add => a.wrapping_add(b),
                    SOp::Sub => a.wrapping_sub(b),
                    SOp::Mul => a.wrapping_mul(b),
                    SOp::Div => a.checked_div(b).unwrap_or(0),
                }
            }
        }
    }
}

// The node types: each variant one `&'static` to its payload (Kani reads a `const` enum's
// payload as constants only when its variants share one shape: with a multi-field variant
// beside a one-pointer one, the reads were unknown and a check took minutes, not ms).

/// A value (`expr::Val`), its leaves static, each with its source.
#[derive(Clone, Copy, Debug)]
pub enum V {
    Field(&'static Field),
    Leaf(&'static (&'static S, &'static str)),
    Bit(&'static (BitOp, V, V)),
    Shift(&'static (ShiftOp, V, &'static S, &'static str)),
    Paren(&'static V),
    Param(&'static (u8, &'static str)),
}

/// A condition (`expr::Cond`).
#[derive(Clone, Copy, Debug)]
pub enum C {
    Static(&'static (&'static S, &'static str)),
    Cmp(&'static (CmpOp, V, V)),
    /// `a op b` of i32s (`expr::Cond::SCmp`)
    SCmp(&'static (CmpOp, V, V)),
    /// `p.is_null()`
    IsNull(&'static V),
    /// `match d.call()`: its patterns as written (for the print), its arms, its default
    CallMatch(&'static (&'static [&'static [CallPat]], Option<&'static A<C>>, C)),
    And(&'static (C, C)),
    Or(&'static (C, C)),
    Not(&'static C),
    Paren(&'static C),
    Let(&'static (L, C)),
    Block(&'static C),
    Match(&'static (Option<&'static A<C>>, C)),
    Call(&'static Call),
    Apply(&'static Apply),
}

/// `f(d, args…)`: a fn of the file, its body.
#[derive(Clone, Copy, Debug)]
pub struct Call {
    pub name: &'static str,
    pub args: &'static [&'static str],
    pub d: &'static str,
    pub body: C,
}

/// `g(args…)`: a closure's call, its body.
#[derive(Clone, Copy, Debug)]
pub struct Apply {
    pub name: &'static str,
    pub args: &'static [V],
    pub body: C,
}

/// A statement (`expr::Stmt`).
#[derive(Clone, Copy, Debug)]
pub enum T {
    Verdict(&'static (&'static S, &'static str)),
    Return(&'static (&'static S, &'static str)),
    Let(&'static (L, T)),
    If(&'static (C, T, T)),
    IfThen(&'static (C, T, T)),
    Match(&'static (Option<&'static A<T>>, T)),
    CallMatch(&'static (&'static [&'static [CallPat]], Option<&'static A<T>>, T)),
    Block(&'static T),
}

/// A `match d.call()` arm's pattern, as written (`expr::CallPat`).
#[derive(Clone, Copy, Debug)]
pub struct CallPat {
    pub call: &'static str,
    pub binds: &'static [&'static str],
    pub rest: bool,
    pub braces: bool,
}

fn call_pats(p: &[&[CallPat]]) -> Vec<Vec<crate::expr::CallPat>> {
    p.iter()
        .map(|a| a.iter().map(|q| crate::expr::CallPat { call: q.call, binds: q.binds.to_vec(), rest: q.rest, braces: q.braces }).collect())
        .collect()
}

/// A `match`'s arms, a list: an arm (its patterns, guard, body), then the next. (Lists, not
/// slices: Kani reads a large `const` array's elements as unknown, so each node is its own.)
#[derive(Clone, Copy, Debug)]
pub struct A<B: 'static> {
    pub pats: &'static P,
    pub guard: Option<&'static C>,
    pub body: B,
    pub next: Option<&'static A<B>>,
}

/// A pattern (a const), then the next.
#[derive(Clone, Copy, Debug)]
pub struct P {
    pub value: i64,
    pub src: &'static str,
    pub next: Option<&'static P>,
}

#[derive(Clone, Copy, Debug)]
pub enum L {
    Plain(&'static &'static str),
    Closure(&'static Closure),
}

#[derive(Clone, Copy, Debug)]
pub struct Closure {
    pub name: &'static str,
    pub params: &'static [(&'static str, &'static str)],
    pub body: C,
}

/// A policy's tree: `d`'s name, the body.
#[derive(Clone, Copy, Debug)]
pub struct Tree {
    pub d: &'static str,
    pub body: T,
}

impl Tree {
    /// The tree for the params' values (`p[i]`: param `i` `as u64`).
    pub fn build(&self, p: &[u64]) -> Policy {
        Policy { d: self.d, body: t(&self.body, p) }
    }
}

fn leaf<X>(value: X, src: &'static str) -> Leaf<X> {
    Leaf { value, src }
}

pub(crate) fn v(x: &V, p: &[u64]) -> Val {
    let bv = |x: &V| Box::new(v(x, p));
    match *x {
        V::Field(f) => Val::Field(*f),
        V::Leaf(&(s, src)) => Val::Const(leaf(s.eval(p), src)),
        V::Bit((op, a, b)) => Val::Bit(*op, bv(a), bv(b)),
        V::Shift((op, a, s, src)) => Val::Shift(*op, bv(a), leaf(s.eval(p) as u32, src)),
        V::Paren(a) => Val::Paren(bv(a)),
        V::Param(&(i, name)) => Val::Param(i, name),
    }
}

fn l(x: &L, p: &[u64]) -> Let {
    match *x {
        L::Plain(src) => Let::Plain(src),
        L::Closure(k) => Let::Closure { name: k.name, params: k.params.to_vec(), body: Box::new(c(&k.body, p)) },
    }
}

fn arms<B, X>(mut a: Option<&A<B>>, p: &[u64], b: impl Fn(&B) -> X) -> Vec<Arm<X>> {
    let mut v = vec![];
    while let Some(x) = a {
        let (mut pats, mut q) = (vec![], Some(x.pats));
        while let Some(y) = q {
            pats.push(leaf(y.value, y.src));
            q = y.next;
        }
        v.push(Arm { pats, guard: x.guard.map(|g| c(g, p)), body: b(&x.body) });
        a = x.next;
    }
    v
}

pub(crate) fn c(x: &C, p: &[u64]) -> Cond {
    let bc = |x: &C| Box::new(c(x, p));
    match *x {
        C::Static(&(s, src)) => Cond::Static(leaf(s.eval(p) != 0, src)),
        C::Cmp((op, a, b)) => Cond::Cmp(*op, Box::new(v(a, p)), Box::new(v(b, p))),
        C::SCmp((op, a, b)) => Cond::SCmp(*op, Box::new(v(a, p)), Box::new(v(b, p))),
        C::IsNull(a) => Cond::IsNull(Box::new(v(a, p))),
        C::CallMatch((pats, a, d)) => Cond::CallMatch(CallMatch { pats: call_pats(pats), arms: arms(*a, p, |b| c(b, p)), default: bc(d) }),
        C::And((a, b)) => Cond::And(bc(a), bc(b)),
        C::Or((a, b)) => Cond::Or(bc(a), bc(b)),
        C::Not(a) => Cond::Not(bc(a)),
        C::Paren(a) => Cond::Paren(bc(a)),
        C::Let((x, a)) => Cond::Let(l(x, p), bc(a)),
        C::Block(a) => Cond::Block(bc(a)),
        C::Match((a, d)) => Cond::Match(arms(*a, p, |b| c(b, p)), bc(d)),
        C::Call(k) => Cond::Call { name: k.name, args: k.args.to_vec(), d: k.d, body: bc(&k.body) },
        C::Apply(k) => Cond::Apply { name: k.name, args: k.args.iter().map(|a| v(a, p)).collect(), body: bc(&k.body) },
    }
}

pub(crate) fn t(x: &T, p: &[u64]) -> Stmt {
    let bt = |x: &T| Box::new(t(x, p));
    match *x {
        T::Verdict(&(s, src)) => Stmt::Verdict(leaf(s.eval(p) as u32, src)),
        T::Return(&(s, src)) => Stmt::Return(leaf(s.eval(p) as u32, src)),
        T::Let((x, a)) => Stmt::Let(l(x, p), bt(a)),
        T::If((k, a, b)) => Stmt::If(c(k, p), bt(a), bt(b)),
        T::IfThen((k, a, b)) => Stmt::IfThen(c(k, p), bt(a), bt(b)),
        T::Match((a, d)) => Stmt::Match(arms(*a, p, |b| t(b, p)), bt(d)),
        T::CallMatch((pats, a, d)) => Stmt::CallMatch(CallMatch { pats: call_pats(pats), arms: arms(*a, p, |b| t(b, p)), default: bt(d) }),
        T::Block(a) => Stmt::Block(bt(a)),
    }
}

// ---- the tree's meaning, read in place (no tree built: Kani's heap is slow) ----
// Each node's line is `expr.rs`'s line for the node `build` makes of it; `tree_proof.rs`
// proves the two equal, node kind by node kind (`eval_t(x) == build(x).eval()`).

impl Tree {
    /// `build(p)`'s `eval` on `d`, read in place.
    pub fn eval(&self, p: &[u64], d: &seccomp_data) -> u32 {
        eval_t(&self.body, p, d)
    }
}

pub fn eval_v(x: &V, p: &[u64], d: &seccomp_data) -> u64 {
    match *x {
        V::Field(f) => f.eval(d),
        V::Leaf(&(s, _)) => s.eval(p),
        V::Bit((BitOp::And, a, b)) => eval_v(a, p, d) & eval_v(b, p, d),
        V::Bit((BitOp::Or, a, b)) => eval_v(a, p, d) | eval_v(b, p, d),
        V::Shift((op, a, k, _)) => {
            let (va, k) = (eval_v(a, p, d), k.eval(p) as u32);
            if !wide_v(a) {
                (match op {
                    ShiftOp::Shl => (va as u32) << k,
                    ShiftOp::Shr => (va as u32) >> k,
                }) as u64
            } else {
                match op {
                    ShiftOp::Shl => va << k,
                    ShiftOp::Shr => va >> k,
                }
            }
        }
        V::Paren(a) => eval_v(a, p, d),
        V::Param(_) => panic!("a closure's parameter outside its closure"),
    }
}

/// `Val::wide` of `build`'s value.
pub fn wide_v(x: &V) -> bool {
    match *x {
        V::Field(f) => f.wide(),
        V::Leaf(_) => true,
        V::Bit((_, a, b)) => match a {
            V::Leaf(_) => wide_v(b),
            _ => wide_v(a),
        },
        V::Shift((_, a, _, _)) | V::Paren(a) => wide_v(a),
        V::Param(_) => true,
    }
}

pub fn eval_c(x: &C, p: &[u64], d: &seccomp_data) -> bool {
    match *x {
        C::Static(&(s, _)) => s.eval(p) != 0,
        C::Cmp((op, a, b)) => op.holds(eval_v(a, p, d), eval_v(b, p, d)),
        C::SCmp((op, a, b)) => op.holds_i32(eval_v(a, p, d) as u32 as i32, eval_v(b, p, d) as u32 as i32),
        C::IsNull(a) => eval_v(a, p, d) == 0,
        C::CallMatch((_, arms, default)) => eval_arms(*arms, p, d, |b| eval_c(b, p, d), || eval_c(default, p, d)),
        C::And((a, b)) => eval_c(a, p, d) && eval_c(b, p, d),
        C::Or((a, b)) => eval_c(a, p, d) || eval_c(b, p, d),
        C::Not(a) => !eval_c(a, p, d),
        C::Paren(a) | C::Block(a) | C::Let((_, a)) => eval_c(a, p, d),
        C::Match((arms, default)) => eval_arms(*arms, p, d, |b| eval_c(b, p, d), || eval_c(default, p, d)),
        C::Call(k) => eval_c(&k.body, p, d),
        C::Apply(k) => eval_c(&k.body, p, d),
    }
}

pub fn eval_t(x: &T, p: &[u64], d: &seccomp_data) -> u32 {
    match *x {
        T::Verdict(&(s, _)) | T::Return(&(s, _)) => s.eval(p) as u32,
        T::Let((_, a)) | T::Block(a) => eval_t(a, p, d),
        T::If((k, a, b)) | T::IfThen((k, a, b)) => {
            if eval_c(k, p, d) {
                eval_t(a, p, d)
            } else {
                eval_t(b, p, d)
            }
        }
        T::Match((arms, default)) | T::CallMatch((_, arms, default)) => {
            eval_arms(*arms, p, d, |b| eval_t(b, p, d), || eval_t(default, p, d))
        }
    }
}

/// A `match`: the body (by `body`) of the first arm whose pattern is `d.nr as i64` and whose
/// guard holds, else the default's. (The body is evaluated where its arm is: an arm chosen by a
/// symbolic call, returned, would be an unknown node to Kani.)
pub fn eval_arms<B, X>(mut a: Option<&'static A<B>>, p: &[u64], d: &seccomp_data, body: impl Fn(&B) -> X, default: impl FnOnce() -> X) -> X {
    while let Some(x) = a {
        let mut q = Some(x.pats);
        let mut hit = false;
        while let Some(y) = q {
            hit |= d.nr as i64 == y.value;
            q = y.next;
        }
        if hit && x.guard.is_none_or(|g| eval_c(g, p, d)) {
            return body(&x.body);
        }
        a = x.next;
    }
    default()
}

/// A symbolic call, every field `kani::any()`; its number `nr` if given (a harness per number
/// keeps each small).
#[cfg(kani)]
#[doc(hidden)]
pub fn any_data(nr: Option<i32>) -> libc::seccomp_data {
    let any: i32 = ::kani::any();
    libc::seccomp_data { nr: nr.unwrap_or(any), arch: ::kani::any(), instruction_pointer: ::kani::any(), args: ::kani::any() }
}

/// The filter from a [`Tree`], and its check:
///
/// ```ignore
/// pub const TREE: seccomp_fn_verify::tree::Tree = seccomp_fn::tree!(policy);
/// seccomp_fn_verify::filter!(pub fn filter(pid: u64, on: bool) = TREE, policy; check filter_is_policy);
/// ```
///
/// `filter(params)` is `compile` of `TREE.build` of the params; `filter_is_policy(nr, params)`
/// (with `cfg(kani)`) asserts, for a symbolic call (its number `nr` if given), that `eval` of the
/// same tree is `policy(params)`'s verdict. One list of params makes both: the filter's tree is
/// the one checked. The harnesses: [`harnesses!`](crate::harnesses).
#[macro_export]
macro_rules! filter {
    ($(#[$m:meta])* $vis:vis fn $name:ident($($p:ident: $t:ty),* $(,)?) = $tree:path, $policy:path; check $check:ident) => {
        $(#[$m])*
        $vis fn $name($($p: $t),*) -> ::std::vec::Vec<$crate::sock_filter> {
            $crate::compile(&$tree.build(&[$($p as u64),*]))
        }

        /// The check: `eval` of the filter's tree is the policy, for every call (its number
        /// `nr` if given). Called by the harnesses (`seccomp_fn_verify::harnesses!`).
        #[cfg(kani)]
        #[allow(dead_code)]
        $vis fn $check(nr: ::core::option::Option<i32>, $($p: $t),*) {
            let d = $crate::tree::any_data(nr);
            // the tree's `eval` read in place (`build`'s, by `tree_proof.rs`)
            assert!($tree.eval(&[$($p as u64),*], &d) == $policy($($p),*)(&d), "the tree isn't the policy");
        }
    };
}

/// Kani harnesses calling a check (`filter!`'s), each with its params (`kani::any()` for a
/// symbolic one; an enum's values listed, a harness each):
///
/// ```ignore
/// #[cfg(kani)]
/// mod proof {
///     use super::*;
///     seccomp_fn_verify::harnesses!(filter_is_policy, unwind = 64;
///         off => (None, ::kani::any(), false);
///         on => (None, ::kani::any(), true));
/// }
/// ```
#[macro_export]
macro_rules! harnesses {
    ($check:path, unwind = $u:literal; $($name:ident => ($($a:expr),* $(,)?));* $(;)?) => {
        $(
            #[::kani::proof]
            #[::kani::unwind($u)]
            fn $name() {
                $check($($a),*)
            }
        )*
    };
}

/// The combinator: a filter of rows as a [`Tree`], each sub-filter a condition (it can only
/// allow, or not, never change the checks before it). Another ABI (an arch but `arch`, or the
/// x32 bit): KILL_PROCESS; a call not from `gate`: TRAP; then ALLOW if `core` or a sub holds,
/// else KILL_PROCESS. `arch` and `gate` are static expressions ([`S`]), the rest conditions
/// ([`C`]); the tree is the source
///
/// ```text
/// if d.arch != arch || d.nr as u32 >= X32_SYSCALL_BIT { return SECCOMP_RET_KILL_PROCESS; }
/// if d.instruction_pointer != gate { return SECCOMP_RET_TRAP; }
/// if core || sub… { SECCOMP_RET_ALLOW } else { SECCOMP_RET_KILL_PROCESS }
/// ```
///
/// (A tree of the usual nodes: the compiler's proof and the tree's cover it.)
#[macro_export]
macro_rules! gated {
    (arch = $arch:expr, gate = $gate:expr, core = $core:expr, subs = [$($sub:expr),* $(,)?] $(,)?) => {{
        use $crate::expr::{CmpOp, Field};
        use $crate::tree::{C, S, T, Tree, V};
        Tree {
            d: "d",
            body: T::IfThen(&(
                C::Or(&(
                    C::Cmp(&(CmpOp::Ne, V::Field(&Field::Arch), V::Leaf(&(&$arch, "arch")))),
                    C::Cmp(&(CmpOp::Ge, V::Field(&Field::Nr), V::Leaf(&(&S::Const(0x4000_0000), "X32_SYSCALL_BIT")))),
                )),
                T::Return(&(&S::Const($crate::verdicts::KILL), "SECCOMP_RET_KILL_PROCESS")),
                T::IfThen(&(
                    C::Cmp(&(CmpOp::Ne, V::Field(&Field::Ip), V::Leaf(&(&$gate, "gate")))),
                    T::Return(&(&S::Const($crate::verdicts::TRAP), "SECCOMP_RET_TRAP")),
                    T::If(&(
                        $crate::__or!($core $(, $sub)*),
                        T::Verdict(&(&S::Const($crate::verdicts::ALLOW), "SECCOMP_RET_ALLOW")),
                        T::Verdict(&(&S::Const($crate::verdicts::KILL), "SECCOMP_RET_KILL_PROCESS")),
                    )),
                )),
            )),
        }
    }};
}

/// `a || b || …`, left to right (`gated!`'s rows).
#[doc(hidden)]
#[macro_export]
macro_rules! __or {
    ($a:expr) => { $a };
    ($a:expr, $b:expr $(, $rest:expr)*) => { $crate::__or!($crate::tree::C::Or(&($a, $b)) $(, $rest)*) };
}
