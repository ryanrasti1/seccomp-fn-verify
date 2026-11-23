//! The const tree's in-place meaning is its built tree's: for every node kind,
//! `eval_*(x, p, d) == build(x, p).eval(d)` (Kani), each child a leaf of a symbolic value.
//!
//! The induction (every tree): each `eval_*` line uses a child only through the child's own
//! `eval_*`, and `eval_by`'s line (`expr.rs`) a built child only through its `eval`; so two
//! nodes of one kind whose children agree agree, and leaves agree (their own harnesses). Two
//! facts aren't values: `wide_v` (a shift's), proven equal to `Val::wide` of the built value
//! the same way; and a `match`'s arm list, a loop here and a recursion there (`match_by`), the
//! loop's body the recursion's step, checked for two arms of two patterns each.

use crate::expr::*;
use crate::tree::*;
use kani::any;
use libc::seccomp_data;

fn data() -> seccomp_data {
    seccomp_data { nr: any(), arch: any(), instruction_pointer: any(), args: any() }
}

fn st<X>(x: X) -> &'static X {
    Box::leak(Box::new(x))
}

/// Param `i`'s leaf of each kind.
fn ps(i: u8) -> &'static S {
    st(S::Param(i))
}
fn cl(i: u8) -> C {
    C::Static(st((ps(i), "")))
}
fn vl(i: u8) -> V {
    V::Leaf(st((ps(i), "")))
}
fn tl(i: u8) -> T {
    T::Verdict(st((ps(i), "")))
}

// A built child's value: it is a leaf (each harness's children are), read without recursion.
fn leaf_c(x: &Cond) -> bool {
    match x {
        Cond::Static(l) => l.value,
        _ => unreachable!("a leaf child"),
    }
}
fn leaf_v(d: &seccomp_data) -> impl Fn(&Val) -> u64 + '_ {
    move |x| match x {
        Val::Const(l) => l.value,
        Val::Field(f) => f.eval(d),
        _ => unreachable!("a leaf child"),
    }
}
fn leaf_t(x: &Stmt) -> u32 {
    match x {
        Stmt::Verdict(l) => l.value,
        _ => unreachable!("a leaf child"),
    }
}
fn wide_leaf(x: &Val) -> bool {
    match x {
        Val::Const(_) => true,
        Val::Field(f) => f.wide(),
        _ => unreachable!("a leaf child"),
    }
}

/// The node's line in place against `eval_by`'s line on the built node, its children by their
/// values (the induction's step).
fn cond_eq(x: C, p: &[u64]) {
    let d = data();
    let built = c(&x, p);
    assert!(eval_c(&x, p, &d) == built.eval_by(&d, leaf_c, leaf_v(&d)));
    core::mem::forget(built);
}
fn val_eq(x: V, p: &[u64]) {
    let d = data();
    let built = v(&x, p);
    assert!(eval_v(&x, p, &d) == built.eval_by(&d, leaf_v(&d), wide_leaf));
    // `wide`'s line, the same way
    let w = match &built {
        Val::Bit(_, a, b) => match **a {
            Val::Const(_) => wide_leaf(b),
            _ => wide_leaf(a),
        },
        Val::Shift(_, a, _) | Val::Paren(a) => wide_leaf(a),
        b => b.wide(),
    };
    assert!(wide_v(&x) == w);
    core::mem::forget(built);
}
fn stmt_eq(x: T, p: &[u64]) {
    let d = data();
    let built = t(&x, p);
    assert!(eval_t(&x, p, &d) == built.eval_by(&d, leaf_c, leaf_t));
    core::mem::forget(built);
}

fn params() -> [u64; 4] {
    any()
}

macro_rules! lemma {
    ($($name:ident => $body:expr;)*) => {$(
        #[kani::proof]
        #[kani::unwind(8)]
        fn $name() {
            $body
        }
    )*};
}

fn field(f: Field) {
    val_eq(V::Field(st(f)), &params())
}

fn shift(op: ShiftOp, wide: bool) {
    let mut p = params();
    // below the width (past it both panic: no value to compare)
    p[1] %= if wide { 64 } else { 32 };
    let a = if wide { vl(0) } else { V::Field(st(Field::Arch)) };
    val_eq(V::Shift(st((op, a, ps(1), ""))), &p)
}

fn scmp(op: CmpOp) {
    cond_eq(C::SCmp(st((op, vl(0), vl(1)))), &params())
}

fn cmp(op: CmpOp) {
    cond_eq(C::Cmp(st((op, vl(0), vl(1)))), &params())
}

/// Two arms (two patterns each, the second with a guard), then the default.
fn arms2() -> (Option<&'static A<C>>, Option<&'static A<T>>, [u64; 4]) {
    let p = params();
    let pats = |a: i64, b: i64| st(P { value: a, src: "", next: Some(st(P { value: b, src: "", next: None })) });
    let (q0, q1, q2, q3): (i64, i64, i64, i64) = (any(), any(), any(), any());
    let c2 = st(A { pats: pats(q2, q3), guard: Some(st(cl(2))), body: cl(1), next: None });
    let c1 = st(A { pats: pats(q0, q1), guard: None, body: cl(0), next: Some(c2) });
    let t2 = st(A { pats: pats(q2, q3), guard: Some(st(cl(2))), body: tl(1), next: None });
    let t1 = st(A { pats: pats(q0, q1), guard: None, body: tl(0), next: Some(t2) });
    (Some(c1), Some(t1), p)
}

lemma! {
    v_field_nr => field(Field::Nr);
    v_field_arch => field(Field::Arch);
    v_field_ip => field(Field::Ip);
    v_field_arg => field(Field::Arg(any::<u8>() % 6));
    v_leaf => val_eq(vl(0), &params());
    v_and => val_eq(V::Bit(st((BitOp::And, vl(0), vl(1)))), &params());
    v_or => val_eq(V::Bit(st((BitOp::Or, vl(0), vl(1)))), &params());
    v_or_field => val_eq(V::Bit(st((BitOp::Or, V::Field(st(Field::Arch)), vl(1)))), &params());
    v_shl => shift(ShiftOp::Shl, true);
    v_shr => shift(ShiftOp::Shr, true);
    v_shl32 => shift(ShiftOp::Shl, false);
    v_shr32 => shift(ShiftOp::Shr, false);
    v_paren => val_eq(V::Paren(st(vl(0))), &params());
    c_static => cond_eq(cl(0), &params());
    c_eq => cmp(CmpOp::Eq);
    c_ne => cmp(CmpOp::Ne);
    c_lt => cmp(CmpOp::Lt);
    c_le => cmp(CmpOp::Le);
    c_gt => cmp(CmpOp::Gt);
    c_ge => cmp(CmpOp::Ge);
    c_scmp_eq => scmp(CmpOp::Eq);
    c_scmp_ne => scmp(CmpOp::Ne);
    c_scmp_lt => scmp(CmpOp::Lt);
    c_scmp_le => scmp(CmpOp::Le);
    c_scmp_gt => scmp(CmpOp::Gt);
    c_scmp_ge => scmp(CmpOp::Ge);
    c_isnull => cond_eq(C::IsNull(st(vl(0))), &params());
    c_call_match => { let (a, _, p) = arms2(); cond_eq(C::CallMatch(st((&[], a, cl(3)))), &p) };
    t_call_match => { let (_, a, p) = arms2(); stmt_eq(T::CallMatch(st((&[], a, tl(3)))), &p) };
    v_field_typed => {
        let ty = [crate::calls::Ty::U16, crate::calls::Ty::U32, crate::calls::Ty::I32, crate::calls::Ty::U64, crate::calls::Ty::I64, crate::calls::Ty::Usize, crate::calls::Ty::Ptr][any::<usize>() % 7];
        field(Field::Typed { call: "", name: "", arg: any::<u8>() % 6, ty })
    };
    c_and => cond_eq(C::And(st((cl(0), cl(1)))), &params());
    c_or => cond_eq(C::Or(st((cl(0), cl(1)))), &params());
    c_not => cond_eq(C::Not(st(cl(0))), &params());
    c_paren => cond_eq(C::Paren(st(cl(0))), &params());
    c_block => cond_eq(C::Block(st(cl(0))), &params());
    c_let => cond_eq(C::Let(st((L::Plain(st("")), cl(0)))), &params());
    c_call => cond_eq(C::Call(st(Call { name: "", args: &[], d: "", body: cl(0) })), &params());
    c_apply => cond_eq(C::Apply(st(Apply { name: "", args: &[], body: cl(0) })), &params());
    c_match => { let (a, _, p) = arms2(); cond_eq(C::Match(st((a, cl(3)))), &p) };
    t_verdict => stmt_eq(tl(0), &params());
    t_return => stmt_eq(T::Return(st((ps(0), ""))), &params());
    t_let => stmt_eq(T::Let(st((L::Plain(st("")), tl(0)))), &params());
    t_block => stmt_eq(T::Block(st(tl(0))), &params());
    t_if => stmt_eq(T::If(st((cl(0), tl(1), tl(2)))), &params());
    t_if_then => stmt_eq(T::IfThen(st((cl(0), tl(1), tl(2)))), &params());
    t_match => { let (_, a, p) = arms2(); stmt_eq(T::Match(st((a, tl(3)))), &p) };
}
