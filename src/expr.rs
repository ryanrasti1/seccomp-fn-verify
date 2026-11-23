//! The policy as a tree: the subset of Rust a policy's closure body is written in, a node per
//! construct, and [`Stmt::eval`], its meaning, a line per node that is the Rust operator itself.
//! `bpf!` (seccomp-fn, not trusted) parses the body into this tree and refuses to compile unless
//! the tree printed ([`Policy::print`], `print.rs`) is the body's own tokens; the compiler
//! (`compile.rs`) translates the tree, node by node, and each node's translation is proven
//! (`proof.rs`) to give its node's `eval`.
//!
//! A leaf ([`Leaf`]) is an expression without `d`: its value, as rustc computes it from its
//! source when the filter is built (a param, a const, `O_RDONLY | O_NB`), and its source, for
//! the print. A policy's values without `d` are leaves, so its params are too: the tree holds
//! their values, and a proof of a node for every value of its leaves is a proof for every param.

use crate::calls::Ty;
use libc::seccomp_data;

/// An expression without `d`: `value`, rustc's, of the source `src`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Leaf<T> {
    pub value: T,
    pub src: &'static str,
}

/// A field of `d`, as a value (zero-extended to 64 bits).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Field {
    /// `d.nr as u32`
    Nr,
    /// `d.arch`
    Arch,
    /// `d.instruction_pointer`
    Ip,
    /// `d.args[i]`, `i` below 6
    Arg(u8),
    /// A typed view's field: `name`, bound by an arm of `match d.call()` on `call`, argument
    /// `arg` read as its C type `ty` (both [`crate::calls::field`]'s, which [`Field::typed`]
    /// takes and the check confirms: never the macro's).
    Typed { call: &'static str, name: &'static str, arg: u8, ty: Ty },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CmpOp {
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BitOp {
    And,
    Or,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ShiftOp {
    Shl,
    Shr,
}

/// A value: an integer, u32 or u64 (as Rust types it: a field's type), held zero-extended.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Val {
    Field(Field),
    /// An expression without `d`, of the type of what it is compared or combined with.
    Const(Leaf<u64>),
    /// `a & b`, `a | b`
    Bit(BitOp, Box<Val>, Box<Val>),
    /// `a << k`, `a >> k`, `k` a leaf below the width (else the compiler refuses: Rust panics)
    Shift(ShiftOp, Box<Val>, Leaf<u32>),
    /// `(a)`
    Paren(Box<Val>),
    /// A closure's parameter `i`, by its name (only in a closure's body: [`Cond::Apply`]
    /// holds the body with each replaced by its argument).
    Param(u8, &'static str),
}

/// A condition.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Cond {
    /// A condition without `d`: `threads`, `fs == Fs::ReadWrite`.
    Static(Leaf<bool>),
    /// `a op b`
    Cmp(CmpOp, Box<Val>, Box<Val>),
    /// `a op b` of i32s: each side's low half, as an i32 (an i32 field's, a leaf's, or a closure
    /// parameter's of type i32)
    SCmp(CmpOp, Box<Val>, Box<Val>),
    /// `p.is_null()`, `p` a pointer argument (a typed field of type `Ptr`)
    IsNull(Box<Val>),
    /// `match d.call() { Call::V { a, b, .. } if g => body, … _ => default, }`: as [`Cond::Match`]
    /// of its arms (each pattern the variant's number, [`CallArm::new`]), the arms' patterns
    /// beside them (`pats[i]` is `arms[i]`'s)
    CallMatch(CallMatch<Cond>),
    /// `a && b`
    And(Box<Cond>, Box<Cond>),
    /// `a || b`
    Or(Box<Cond>, Box<Cond>),
    /// `!a`
    Not(Box<Cond>),
    /// `(a)`
    Paren(Box<Cond>),
    /// `let …;` then `rest` (as [`Stmt::Let`])
    Let(Let, Box<Cond>),
    /// `{ c }` (a `match` arm's)
    Block(Box<Cond>),
    /// `match d.nr as i64 { arms… _ => default, }`, of conditions
    Match(Vec<Arm<Cond>>, Box<Cond>),
    /// `f(d, args…)`: a `fn f(d: &seccomp_data, params…) -> bool` of the policy's file, its
    /// `body` with `d` its own name for `d` and its params bound to the args (each without
    /// `d`: rustc computes the body's leaves with them bound, in the call's place)
    Call { name: &'static str, args: Vec<&'static str>, d: &'static str, body: Box<Cond> },
    /// `f(args…)`, `f` a closure in scope ([`Let::Closure`]): its body, each parameter replaced
    /// by its argument (checked: [`Policy::check`])
    Apply { name: &'static str, args: Vec<Val>, body: Box<Cond> },
}

/// A `let` statement.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Let {
    /// `let …;` without `d`, its source: it binds names later leaves use (rustc computes them,
    /// in the same scope)
    Plain(&'static str),
    /// `let name = |params| body;`: a closure of `d`-values to a condition, each param its
    /// name and its source (`fd`, `fd: u64`)
    Closure { name: &'static str, params: Vec<(&'static str, &'static str)>, body: Box<Cond> },
}

/// A statement list's value: what the closure returns.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Stmt {
    /// `v`, the block's value
    Verdict(Leaf<u32>),
    /// `return v;`
    Return(Leaf<u32>),
    /// `let …;` then `rest`
    Let(Let, Box<Stmt>),
    /// `if c { a } else b`, `b` a [`Stmt::Block`] or an `if`
    If(Cond, Box<Stmt>, Box<Stmt>),
    /// `if c { a } rest`: `a` returns (rustc refuses an `if` without `else` of a value)
    IfThen(Cond, Box<Stmt>, Box<Stmt>),
    /// `match d.nr as i64 { arms… _ => default, }`
    Match(Vec<Arm<Stmt>>, Box<Stmt>),
    /// `match d.call() { … }` (as [`Cond::CallMatch`])
    CallMatch(CallMatch<Stmt>),
    /// `{ s }`
    Block(Box<Stmt>),
}

/// `p | q … if guard => body`, the patterns consts (as `i64`), at least one.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Arm<B> {
    pub pats: Vec<Leaf<i64>>,
    pub guard: Option<Cond>,
    pub body: B,
}

/// `match d.call()`: its arms, each a [`Cond::Match`]'s arm whose patterns are the variants'
/// numbers, and each arm's patterns as written (`pats[i]` are `arms[i]`'s: `Call::A { .. } |
/// Call::B`, alternatives binding nothing, or one pattern binding its fields).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CallMatch<B> {
    pub pats: Vec<Vec<CallPat>>,
    pub arms: Vec<Arm<B>>,
    pub default: Box<B>,
}

/// An arm's pattern: `Call::call { binds…, .. }` (`rest`: with `..`; `braces`: with `{ }` at
/// all, else a bare path).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CallPat {
    pub call: &'static str,
    pub binds: Vec<&'static str>,
    pub rest: bool,
    pub braces: bool,
}

impl<B> CallMatch<B> {
    /// The arm for patterns `pats`: each its number by the table (`None` if a call has none).
    pub fn arm(pats: &[CallPat], guard: Option<Cond>, body: B) -> Option<Arm<B>> {
        let nrs = pats.iter().map(|p| Some(Leaf { value: crate::calls::nr(p.call)?, src: p.call })).collect::<Option<Vec<_>>>()?;
        Some(Arm { pats: nrs, guard, body })
    }
}

/// A policy's closure: `move |d| body`, `d` its parameter's name.
#[derive(Clone, Debug)]
pub struct Policy {
    pub d: &'static str,
    pub body: Stmt,
}

impl Field {
    pub fn eval(self, d: &seccomp_data) -> u64 {
        match self {
            Field::Nr => d.nr as u32 as u64,
            Field::Arch => d.arch as u64,
            Field::Ip => d.instruction_pointer,
            Field::Arg(i) => d.args[i as usize],
            // as `CallExt::call` reads it: truncated to the type, held zero-extended (an i32's
            // bits as a u32's: `Cond::SCmp` compares them signed)
            Field::Typed { arg, ty, .. } => {
                let a = d.args[arg as usize % 6];
                match ty {
                    Ty::U16 => a as u16 as u64,
                    Ty::U32 | Ty::I32 => a as u32 as u64,
                    Ty::U64 | Ty::I64 | Ty::Usize | Ty::Ptr => a,
                }
            }
        }
    }
    /// The type: 64 bits, or 32 (its value's high half is 0).
    pub fn wide(self) -> bool {
        match self {
            Field::Ip | Field::Arg(_) => true,
            Field::Typed { ty, .. } => matches!(ty, Ty::U64 | Ty::I64 | Ty::Usize | Ty::Ptr),
            Field::Nr | Field::Arch => false,
        }
    }
    /// Field `name` of `call`, by the table ([`crate::calls::field`]); `None` if it has none.
    pub fn typed(call: &'static str, name: &'static str) -> Option<Field> {
        crate::calls::field(call, name).map(|(arg, ty)| Field::Typed { call, name, arg, ty })
    }
}

impl CmpOp {
    pub fn holds(self, a: u64, b: u64) -> bool {
        match self {
            CmpOp::Eq => a == b,
            CmpOp::Ne => a != b,
            CmpOp::Lt => a < b,
            CmpOp::Le => a <= b,
            CmpOp::Gt => a > b,
            CmpOp::Ge => a >= b,
        }
    }
    pub fn holds_i32(self, a: i32, b: i32) -> bool {
        match self {
            CmpOp::Eq => a == b,
            CmpOp::Ne => a != b,
            CmpOp::Lt => a < b,
            CmpOp::Le => a <= b,
            CmpOp::Gt => a > b,
            CmpOp::Ge => a >= b,
        }
    }
}

// Each `eval` is its node's line (`eval_by`) with the children's values by `eval` itself: a
// line uses a child only through its value, which the proofs give symbolically (`proof.rs`).

impl Val {
    /// Rust's value. (A u32's, zero-extended: equal and ordered as the u32s are.)
    pub fn eval(&self, d: &seccomp_data) -> u64 {
        self.eval_by(d, |v| v.eval(d), Val::wide)
    }

    /// The node's line, a child's value by `v` and its type (`wide`) by `w`.
    pub fn eval_by(&self, d: &seccomp_data, v: impl Fn(&Val) -> u64, w: impl Fn(&Val) -> bool) -> u64 {
        match self {
            Val::Field(f) => f.eval(d),
            Val::Const(l) => l.value,
            Val::Bit(BitOp::And, a, b) => v(a) & v(b),
            Val::Bit(BitOp::Or, a, b) => v(a) | v(b),
            Val::Shift(op, a, k) if !w(a) => (match op {
                ShiftOp::Shl => (v(a) as u32) << k.value,
                ShiftOp::Shr => (v(a) as u32) >> k.value,
            }) as u64,
            Val::Shift(ShiftOp::Shl, a, k) => v(a) << k.value,
            Val::Shift(ShiftOp::Shr, a, k) => v(a) >> k.value,
            Val::Paren(a) => v(a),
            Val::Param(..) => panic!("a closure's parameter outside its closure"),
        }
    }

    /// The type (u64, else u32), as Rust types it: a field's, through the operators (both sides
    /// of `&`, `|` have one type; a shift has its left's). A leaf has its sibling's, so it
    /// decides nothing: a value with no field is a leaf (`bpf!` makes one of it).
    pub fn wide(&self) -> bool {
        match self {
            Val::Field(f) => f.wide(),
            Val::Const(_) => true,
            Val::Bit(_, a, b) => match **a {
                Val::Const(_) => b.wide(),
                _ => a.wide(),
            },
            Val::Shift(_, a, _) | Val::Paren(a) => a.wide(),
            Val::Param(..) => true,
        }
    }

    /// A leaf's value, when the value is one (the compiler's immediates).
    pub fn as_const(&self) -> Option<u64> {
        match self {
            Val::Const(l) => Some(l.value),
            _ => None,
        }
    }
}

impl Cond {
    pub fn eval(&self, d: &seccomp_data) -> bool {
        self.eval_by(d, |c| c.eval(d), |v| v.eval(d))
    }

    pub fn eval_by(&self, d: &seccomp_data, c: impl Fn(&Cond) -> bool, v: impl Fn(&Val) -> u64) -> bool {
        match self {
            Cond::Static(l) => l.value,
            Cond::Cmp(op, a, b) => op.holds(v(a), v(b)),
            Cond::SCmp(op, a, b) => op.holds_i32(v(a) as u32 as i32, v(b) as u32 as i32),
            Cond::IsNull(a) => v(a) == 0,
            Cond::CallMatch(m) => match_by(&m.arms, &m.default, d, &c, &c),
            Cond::And(a, b) => c(a) && c(b),
            Cond::Or(a, b) => c(a) || c(b),
            Cond::Not(a) => !c(a),
            Cond::Paren(a) | Cond::Let(_, a) | Cond::Block(a) => c(a),
            Cond::Match(arms, default) => match_by(arms, default, d, &c, &c),
            Cond::Call { body, .. } | Cond::Apply { body, .. } => c(body),
        }
    }
}

impl Stmt {
    pub fn eval(&self, d: &seccomp_data) -> u32 {
        self.eval_by(d, |c| c.eval(d), |s| s.eval(d))
    }

    pub fn eval_by(&self, d: &seccomp_data, c: impl Fn(&Cond) -> bool, s: impl Fn(&Stmt) -> u32) -> u32 {
        match self {
            Stmt::Verdict(v) | Stmt::Return(v) => v.value,
            Stmt::Let(_, rest) | Stmt::Block(rest) => s(rest),
            Stmt::If(cond, a, b) | Stmt::IfThen(cond, a, b) => {
                if c(cond) {
                    s(a)
                } else {
                    s(b)
                }
            }
            Stmt::Match(arms, default) => match_by(arms, default, d, &c, &s),
            Stmt::CallMatch(m) => match_by(&m.arms, &m.default, d, &c, &s),
        }
    }
}

/// A `match`: the first arm whose pattern is `d.nr as i64` and whose guard holds, else `default`.
pub fn match_by<B, R>(arms: &[Arm<B>], default: &B, d: &seccomp_data, c: &impl Fn(&Cond) -> bool, b: &impl Fn(&B) -> R) -> R {
    match arms.split_first() {
        None => b(default),
        Some((a, rest)) => {
            if member(&a.pats, d) && a.guard.as_ref().is_none_or(c) {
                b(&a.body)
            } else {
                match_by(rest, default, d, c, b)
            }
        }
    }
}

/// `d.nr as i64` is one of `pats`.
pub fn member(pats: &[Leaf<i64>], d: &seccomp_data) -> bool {
    pats.iter().any(|p| d.nr as i64 == p.value)
}

impl Policy {
    pub fn eval(&self, d: &seccomp_data) -> u32 {
        self.body.eval(d)
    }
}
