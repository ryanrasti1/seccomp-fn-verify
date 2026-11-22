//! The print (trusted: the round trip's) and the hygiene check: a tree prints as the Rust whose
//! meaning is its `eval`, parenthesized where precedence needs it, so a tree built in another
//! shape than rustc's parse of its tokens doesn't print as them; and what `check` refuses.

use seccomp_fn_verify::expr::*;
use seccomp_fn_verify::print::{cond, has_word, leaf_prec, val};

fn s(src: &'static str) -> Box<Cond> {
    Box::new(Cond::Static(Leaf { value: true, src }))
}
fn k(src: &'static str) -> Box<Val> {
    Box::new(Val::Const(Leaf { value: 0, src }))
}

#[test]
fn precedence() {
    // And(Or(a, b), c) is not `a || b && c` (rustc: Or(a, And(b, c))): parenthesized
    assert_eq!(cond(&Cond::And(Box::new(Cond::Or(s("a"), s("b"))), s("c")), "d", 0), "(a || b) && c");
    assert_eq!(cond(&Cond::Or(s("a"), Box::new(Cond::And(s("b"), s("c")))), "d", 0), "a || b && c");
    // left-associative: And(a, And(b, c)) needs them, And(And(a, b), c) doesn't
    assert_eq!(cond(&Cond::And(s("a"), Box::new(Cond::And(s("b"), s("c")))), "d", 0), "a && (b && c)");
    assert_eq!(cond(&Cond::And(Box::new(Cond::And(s("a"), s("b"))), s("c")), "d", 0), "a && b && c");
    // a leaf of a looser operator than its place
    let arg = Box::new(Val::Field(Field::Arg(2)));
    assert_eq!(cond(&Cond::Cmp(CmpOp::Eq, arg.clone(), k("O_RDONLY | O_NB")), "d", 0), "d.args[2] == O_RDONLY | O_NB");
    assert_eq!(cond(&Cond::Cmp(CmpOp::Eq, arg.clone(), k("a == b")), "d", 0), "d.args[2] == (a == b)");
    assert_eq!(cond(&Cond::Not(s("a && b")), "d", 0), "!(a && b)");
    assert_eq!(val(&Val::Bit(BitOp::And, arg.clone(), k("1 | 2")), "d", 0), "d.args[2] & (1 | 2)");
    // a Paren node prints its own
    assert_eq!(cond(&Cond::Paren(Box::new(Cond::And(s("a"), s("b")))), "d", 0), "(a && b)");
}

#[test]
fn leaves() {
    assert_eq!(leaf_prec("n"), 12);
    assert_eq!(leaf_prec("libc :: SIGCHLD as u64"), 10);
    assert_eq!(leaf_prec("(libc :: CLONE_PARENT | libc :: SIGCHLD) as u64"), 10);
    assert_eq!(leaf_prec("O_RDONLY | O_NB"), 4);
    assert_eq!(leaf_prec("a || b"), 1);
    assert_eq!(leaf_prec("mode != Mode :: Coroutine"), 3);
    // anything it doesn't know: the loosest
    for l in ["|x| x", "x = 1", "1 .. 2", "if a { b } else { c }", "\"a || b\"", "m ! ()", "a, b", "return 5"] {
        assert_eq!(leaf_prec(l), 0, "{l}");
    }
    assert!(has_word("d . args [0]", "d") && !has_word("dd + d_x", "d"));
}

fn policy(body: Stmt) -> Policy {
    Policy { d: "d", body }
}

#[test]
fn check_refuses() {
    let v = |src| Leaf { value: 0u32, src };
    // a let rebinding `d`
    let p = policy(Stmt::Let(Let::Plain("let d = 5;"), Box::new(Stmt::Verdict(v("0")))));
    assert!(p.check().unwrap_err().contains("mentions `d`"));
    // a leaf of `d`
    assert!(policy(Stmt::Verdict(v("d . nr as u32"))).check().is_err());
    // a closure call whose body isn't the closure's, its parameter replaced
    let def = Cond::Cmp(CmpOp::Ge, Box::new(Val::Param(0, "fd")), k("n"));
    let arg = Val::Field(Field::Arg(0));
    let wrong = Cond::Cmp(CmpOp::Ge, Box::new(Val::Field(Field::Arg(1))), k("n"));
    let call = |body: Cond| {
        policy(Stmt::Let(
            Let::Closure { name: "plugin", params: vec![("fd", "fd : u64")], body: Box::new(def.clone()) },
            Box::new(Stmt::If(
                Cond::Apply { name: "plugin", args: vec![arg.clone()], body: Box::new(body) },
                Box::new(Stmt::Verdict(v("0"))),
                Box::new(Stmt::Verdict(v("1"))),
            )),
        ))
    };
    let right = Cond::Cmp(CmpOp::Ge, Box::new(arg.clone()), k("n"));
    assert!(call(right).check().is_ok());
    assert!(call(wrong).check().unwrap_err().contains("isn't the closure's"));
    // a pattern that isn't a path or an integer
    let arm = Arm { pats: vec![Leaf { value: 0, src: "1 ..= 5" }], guard: None, body: Stmt::Verdict(v("0")) };
    assert!(policy(Stmt::Match(vec![arm], Box::new(Stmt::Verdict(v("1"))))).check().is_err());
}

/// `src/proof-harnesses` (the flake's `expectHarnesses`) is `nodes!`'s list in `src/proof.rs`.
#[test]
fn harness_list() {
    let src = include_str!("../src/proof.rs");
    let list = &src[src.find("nodes! {").unwrap()..];
    let list = &list[..list.find("\n}\n").unwrap()];
    // each `name => body` (not `Kind::Variant => {`): the identifier before a ` => ` not
    // followed by `{`
    let mut names = vec![];
    let mut rest = list;
    while let Some(i) = rest.find(" => ") {
        let before = &rest[..i];
        let start = before.rfind(|c: char| !(c.is_ascii_alphanumeric() || c == '_')).map_or(0, |j| j + 1);
        if !rest[i + 4..].starts_with('{') && !before[..start].ends_with("::") {
            names.push(before[start..].to_string());
        }
        rest = &rest[i + 4..];
    }
    let file: Vec<String> = include_str!("../src/proof-harnesses").lines().map(String::from).collect();
    assert_eq!(names, file, "regenerate src/proof-harnesses from nodes!");
}

/// The typed view's hygiene: a field only where its arm binds it, its argument and type the
/// table's; a signed field never in an unsigned comparison, an unsigned one never in a signed;
/// `is_null` of a pointer only; an arm's pattern its variant's number.
#[test]
fn typed_check() {
    let v = |src| Leaf { value: 0u32, src };
    let pat = |call, binds: Vec<&'static str>| CallPat { call, binds, rest: true, braces: true };
    let on = |p: CallPat, guard: Cond| {
        let arm = CallMatch::arm(std::slice::from_ref(&p), Some(guard), Stmt::Verdict(v("ALLOW"))).unwrap();
        Policy { d: "d", body: Stmt::CallMatch(CallMatch { pats: vec![vec![p]], arms: vec![arm], default: Box::new(Stmt::Verdict(v("KILL"))) }) }
    };
    let f = |call, name| Box::new(Val::Field(Field::typed(call, name).unwrap()));
    // right: a signed field, signed; an unsigned one, unsigned; a pointer's is_null
    assert!(on(pat("Openat", vec!["dfd"]), Cond::SCmp(CmpOp::Ge, f("Openat", "dfd"), k("n"))).check().is_ok());
    assert!(on(pat("Close", vec!["fd"]), Cond::Cmp(CmpOp::Ge, f("Close", "fd"), k("n"))).check().is_ok());
    assert!(on(pat("Ppoll", vec!["sigmask"]), Cond::IsNull(f("Ppoll", "sigmask"))).check().is_ok());
    // a signed field unsigned (ordered, or ==: a leaf's bits may differ), an unsigned one signed
    assert!(on(pat("Openat", vec!["dfd"]), Cond::Cmp(CmpOp::Ge, f("Openat", "dfd"), k("n"))).check().is_err());
    assert!(on(pat("Openat", vec!["dfd"]), Cond::Cmp(CmpOp::Eq, f("Openat", "dfd"), k("n"))).check().is_err());
    assert!(on(pat("Close", vec!["fd"]), Cond::SCmp(CmpOp::Ge, f("Close", "fd"), k("n"))).check().is_err());
    // a field its arm doesn't bind, or of another variant, or with another argument or type
    assert!(on(pat("Openat", vec![]), Cond::SCmp(CmpOp::Ge, f("Openat", "dfd"), k("n"))).check().is_err());
    assert!(on(pat("Connect", vec!["fd"]), Cond::Cmp(CmpOp::Ge, f("Close", "fd"), k("n"))).check().is_err());
    let forged = Box::new(Val::Field(Field::Typed { call: "Close", name: "fd", arg: 1, ty: seccomp_fn_verify::calls::Ty::U32 }));
    assert!(on(pat("Close", vec!["fd"]), Cond::Cmp(CmpOp::Ge, forged, k("n"))).check().is_err());
    // is_null of anything but a pointer field
    assert!(on(pat("Close", vec!["fd"]), Cond::IsNull(f("Close", "fd"))).check().is_err());
    // a pattern that isn't its variant's number, or a variant that isn't the table's
    let p = pat("Close", vec!["fd"]);
    let mut arm = CallMatch::arm(std::slice::from_ref(&p), None, Stmt::Verdict(v("ALLOW"))).unwrap();
    arm.pats[0].value = 4;
    let bad = Policy { d: "d", body: Stmt::CallMatch(CallMatch { pats: vec![vec![p]], arms: vec![arm], default: Box::new(Stmt::Verdict(v("KILL"))) }) };
    assert!(bad.check().is_err());
    assert!(CallMatch::arm(&[pat("Nope", vec![])], None, Stmt::Verdict(v("ALLOW"))).is_none());
    // alternatives: binding nothing, each its number; one that binds is refused
    let alts = vec![pat("Read", vec![]), pat("Write", vec![])];
    let arm = CallMatch::arm(&alts, None, Stmt::Verdict(v("ALLOW"))).unwrap();
    let ok = Policy { d: "d", body: Stmt::CallMatch(CallMatch { pats: vec![alts], arms: vec![arm], default: Box::new(Stmt::Verdict(v("KILL"))) }) };
    assert!(ok.check().is_ok());
    assert_eq!(ok.print(), "match d.call() { Call::Read { .. } | Call::Write { .. } => ALLOW, _ => KILL, }");
    let alts = vec![pat("Close", vec!["fd"]), pat("Write", vec![])];
    let arm = CallMatch::arm(&alts, None, Stmt::Verdict(v("ALLOW"))).unwrap();
    assert!(Policy { d: "d", body: Stmt::CallMatch(CallMatch { pats: vec![alts], arms: vec![arm], default: Box::new(Stmt::Verdict(v("KILL"))) }) }.check().is_err());
    // alternatives binding the same field, the same argument and type: its use is fine; of
    // another type (an i32 `fd` against a u32 one) refused
    let on_alts = |alts: Vec<CallPat>, guard: Cond| {
        let arm = CallMatch::arm(&alts, Some(guard), Stmt::Verdict(v("ALLOW"))).unwrap();
        Policy { d: "d", body: Stmt::CallMatch(CallMatch { pats: vec![alts], arms: vec![arm], default: Box::new(Stmt::Verdict(v("KILL"))) }) }
    };
    let alts = vec![pat("Fstat", vec!["fd"]), pat("Pread64", vec!["fd"])];
    assert!(on_alts(alts, Cond::Cmp(CmpOp::Ge, f("Fstat", "fd"), k("n"))).check().is_ok());
    let alts = vec![pat("Fstat", vec!["fd"]), pat("Connect", vec!["fd"])];
    assert!(on_alts(alts, Cond::Cmp(CmpOp::Ge, f("Fstat", "fd"), k("n"))).check().is_err());
    // a field outside any arm
    let outside = Policy { d: "d", body: Stmt::If(Cond::Cmp(CmpOp::Ge, f("Close", "fd"), k("n")), Box::new(Stmt::Verdict(v("A"))), Box::new(Stmt::Verdict(v("B")))) };
    assert!(outside.check().is_err());
    // its print
    let p = on(pat("Openat", vec!["dfd", "flags"]), Cond::SCmp(CmpOp::Ge, f("Openat", "dfd"), k("n")));
    assert_eq!(p.print(), "match d.call() { Call::Openat { dfd, flags, .. } if dfd >= n => ALLOW, _ => KILL, }");
}
