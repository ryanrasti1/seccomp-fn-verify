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

/// A static expression of the params, on `u64`s (a param's value `as u64`; a condition nonzero
/// for true). Its meaning matters only in that it is a function of the params: the check
/// compares the tree it builds with the policy.
#[derive(Clone, Copy, Debug)]
pub enum S {
    Const(u64),
    Param(u8),
    Not(&'static S),
    Bin(SOp, &'static S, &'static S),
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
            S::Bin(op, a, b) => {
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

/// A value (`expr::Val`), its leaves static, each with its source.
#[derive(Clone, Copy, Debug)]
pub enum V {
    Field(Field),
    Leaf(S, &'static str),
    Bit(BitOp, &'static V, &'static V),
    Shift(ShiftOp, &'static V, S, &'static str),
    Paren(&'static V),
    Param(u8, &'static str),
}

/// A condition (`expr::Cond`).
#[derive(Clone, Copy, Debug)]
pub enum C {
    Static(S, &'static str),
    Cmp(CmpOp, &'static V, &'static V),
    And(&'static C, &'static C),
    Or(&'static C, &'static C),
    Not(&'static C),
    Paren(&'static C),
    Let(L, &'static C),
    Block(&'static C),
    Match(Option<&'static A<C>>, &'static C),
    Call { name: &'static str, args: &'static [&'static str], d: &'static str, body: &'static C },
    Apply { name: &'static str, args: &'static [V], body: &'static C },
}

/// A statement (`expr::Stmt`).
#[derive(Clone, Copy, Debug)]
pub enum T {
    Verdict(S, &'static str),
    Return(S, &'static str),
    Let(L, &'static T),
    If(&'static C, &'static T, &'static T),
    IfThen(&'static C, &'static T, &'static T),
    Match(Option<&'static A<T>>, &'static T),
    Block(&'static T),
}

/// A `match`'s arms, a list: an arm (its patterns, guard, body), then the next. (Lists, not
/// slices: Kani reads a large `const` array's elements as unknown, a small allocation's as
/// constants, so each node is its own.)
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
    Plain(&'static str),
    Closure { name: &'static str, params: &'static [(&'static str, &'static str)], body: &'static C },
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

/// The combinator as `const` data (`expr::gated`): the ABI and gate checks, then `core` or a
/// sub-filter (each a condition: it can only allow, or not), leaves static.
#[derive(Clone, Copy, Debug)]
pub struct Gated {
    pub arch: S,
    pub gate: S,
    pub core: &'static C,
    pub subs: &'static [&'static C],
}

impl Gated {
    pub fn build(&self, p: &[u64]) -> Policy {
        gated(self.arch.eval(p) as u32, self.gate.eval(p), c(self.core, p), self.subs.iter().map(|s| c(s, p)).collect())
    }
}

fn leaf<X>(value: X, src: &'static str) -> Leaf<X> {
    Leaf { value, src }
}

fn v(x: &V, p: &[u64]) -> Val {
    match *x {
        V::Field(f) => Val::Field(f),
        V::Leaf(s, src) => Val::Const(leaf(s.eval(p), src)),
        V::Bit(op, a, b) => Val::Bit(op, Box::new(v(a, p)), Box::new(v(b, p))),
        V::Shift(op, a, s, src) => Val::Shift(op, Box::new(v(a, p)), leaf(s.eval(p) as u32, src)),
        V::Paren(a) => Val::Paren(Box::new(v(a, p))),
        V::Param(i, name) => Val::Param(i, name),
    }
}

fn l(x: &L, p: &[u64]) -> Let {
    match *x {
        L::Plain(src) => Let::Plain(src),
        L::Closure { name, params, body } => Let::Closure { name, params: params.to_vec(), body: Box::new(c(body, p)) },
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

fn c(x: &C, p: &[u64]) -> Cond {
    let bc = |x: &C| Box::new(c(x, p));
    match *x {
        C::Static(s, src) => Cond::Static(leaf(s.eval(p) != 0, src)),
        C::Cmp(op, a, b) => Cond::Cmp(op, Box::new(v(a, p)), Box::new(v(b, p))),
        C::And(a, b) => Cond::And(bc(a), bc(b)),
        C::Or(a, b) => Cond::Or(bc(a), bc(b)),
        C::Not(a) => Cond::Not(bc(a)),
        C::Paren(a) => Cond::Paren(bc(a)),
        C::Let(ref x, a) => Cond::Let(l(x, p), bc(a)),
        C::Block(a) => Cond::Block(bc(a)),
        C::Match(a, d) => Cond::Match(arms(a, p, |b| c(b, p)), bc(d)),
        C::Call { name, args, d, body } => Cond::Call { name, args: args.to_vec(), d, body: bc(body) },
        C::Apply { name, args, body } => Cond::Apply { name, args: args.iter().map(|a| v(a, p)).collect(), body: bc(body) },
    }
}

fn t(x: &T, p: &[u64]) -> Stmt {
    let bt = |x: &T| Box::new(t(x, p));
    match *x {
        T::Verdict(s, src) => Stmt::Verdict(leaf(s.eval(p) as u32, src)),
        T::Return(s, src) => Stmt::Return(leaf(s.eval(p) as u32, src)),
        T::Let(ref x, a) => Stmt::Let(l(x, p), bt(a)),
        T::If(k, a, b) => Stmt::If(c(k, p), bt(a), bt(b)),
        T::IfThen(k, a, b) => Stmt::IfThen(c(k, p), bt(a), bt(b)),
        T::Match(a, d) => Stmt::Match(arms(a, p, |b| t(b, p)), bt(d)),
        T::Block(a) => Stmt::Block(bt(a)),
    }
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
            let tree = $tree.build(&[$($p as u64),*]);
            assert!(tree.eval(&d) == $policy($($p),*)(&d), "the tree isn't the policy");
            // (no drop: a tree's drop glue is recursive, and Kani would unwind it)
            ::core::mem::forget(tree);
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
