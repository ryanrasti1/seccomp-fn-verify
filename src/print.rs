//! The tree as Rust source ([`Policy::print`]), and its hygiene ([`Policy::check`]).
//!
//! **Why the print is trusted.** `bpf!` refuses a policy unless its body's tokens are the
//! tree's print: so the tree is the source, provided the print of a tree is Rust that means what
//! `eval` says. Each node prints as the construct whose line in `eval_by` is its meaning, and
//! with exactly the parentheses Rust's precedence needs: a child that binds looser than its
//! place gets parentheses the source must also have (a `Paren` node prints its own), so a tree
//! built with another shape than rustc's parse of the same tokens doesn't print as them. A
//! leaf's text is given; its precedence is read from it conservatively (the loosest operator at
//! its top level; anything unknown, the loosest of all), so a leaf is bare only where rustc
//! parses it as one operand.
//!
//! **What the check refuses**: a leaf or `let` that mentions `d` (or the function's own name for
//! it), or, inside a closure, its parameters (a leaf is a value without `d`, computed where the
//! tree is built); a closure parameter named `d`; a call of a closure not in scope, or whose
//! body isn't the closure's with each parameter replaced by its argument; a pattern that isn't
//! a path or an integer literal.

use crate::calls::Ty;
use crate::expr::*;

// Rust's binary precedence, loosest first (the Reference's expression precedence table).
const NONE: u8 = 0;
const OR: u8 = 1;
const AND: u8 = 2;
const CMP: u8 = 3;
const BOR: u8 = 4;
const XOR: u8 = 5;
const BAND: u8 = 6;
const SHIFT: u8 = 7;
const ADD: u8 = 8;
const MUL: u8 = 9;
const AS: u8 = 10;
const UNARY: u8 = 11;
const ATOM: u8 = 12;

/// `s`, of precedence `p`, where `need` is the least that place takes: parenthesized if looser.
fn wrap(p: u8, need: u8, s: String) -> String {
    if p >= need { s } else { format!("({s})") }
}

/// A leaf's text, conservatively: the loosest operator outside brackets, or `NONE` for anything
/// it doesn't know (a string or char literal, a keyword that makes a statement or a closure, an
/// assignment, a range, a comma, a semicolon).
pub fn leaf_prec(src: &str) -> u8 {
    if src.contains('"') || src.contains('\'') {
        return NONE;
    }
    let b = src.as_bytes();
    let (mut depth, mut p, mut i) = (0i32, ATOM, 0);
    let low = |p: &mut u8, q: u8| *p = (*p).min(q);
    while i < b.len() {
        let (c, next) = (b[i], b.get(i + 1).copied().unwrap_or(b' '));
        // the char before, past spaces (`m ! ()`, a macro, as proc_macro2 prints it)
        let prev = b[..i].iter().rev().copied().find(|c| *c != b' ').unwrap_or(b' ');
        match c {
            b'(' | b'[' | b'{' => depth += 1,
            b')' | b']' | b'}' => {
                depth -= 1;
                if depth < 0 {
                    return NONE;
                }
            }
            _ if depth > 0 => {}
            b'|' if next == b'|' => {
                low(&mut p, OR);
                i += 1;
            }
            b'|' => low(&mut p, if i == 0 { NONE } else { BOR }),
            b'&' if next == b'&' => {
                low(&mut p, AND);
                i += 1;
            }
            b'&' => low(&mut p, BAND),
            b'^' => low(&mut p, XOR),
            b'=' if next == b'=' => {
                low(&mut p, CMP);
                i += 1;
            }
            b'=' => low(&mut p, NONE),
            b'!' if next == b'=' => {
                low(&mut p, CMP);
                i += 1;
            }
            b'!' if prev.is_ascii_alphanumeric() || prev == b'_' => low(&mut p, NONE), // a macro
            b'!' => low(&mut p, UNARY),
            b'<' | b'>' if next == c => {
                low(&mut p, SHIFT);
                i += 1;
            }
            b'>' if prev == b'-' => low(&mut p, NONE),
            b'<' | b'>' => low(&mut p, CMP),
            b'+' | b'-' => low(&mut p, ADD),
            b'*' | b'/' | b'%' => low(&mut p, MUL),
            b'.' if next == b'.' => low(&mut p, NONE),
            b',' | b';' | b'#' | b'@' | b'$' => low(&mut p, NONE),
            c if c.is_ascii_alphabetic() || c == b'_' => {
                let start = i;
                while i < b.len() && (b[i].is_ascii_alphanumeric() || b[i] == b'_') {
                    i += 1;
                }
                let w = &src[start..i];
                if w == "as" {
                    low(&mut p, AS);
                } else if KEYWORDS.contains(&w) {
                    low(&mut p, NONE);
                }
                continue;
            }
            _ => {}
        }
        i += 1;
    }
    if depth != 0 { NONE } else { p }
}

const KEYWORDS: [&str; 18] = [
    "if", "else", "match", "return", "break", "continue", "loop", "while", "for", "in", "let", "move", "unsafe", "async", "await", "yield", "static", "become",
];

fn leaf(src: &str, need: u8) -> String {
    wrap(leaf_prec(src), need, src.to_string())
}

fn cmp_op(op: CmpOp) -> &'static str {
    match op {
        CmpOp::Eq => "==",
        CmpOp::Ne => "!=",
        CmpOp::Lt => "<",
        CmpOp::Le => "<=",
        CmpOp::Gt => ">",
        CmpOp::Ge => ">=",
    }
}

/// A value, where precedence `need` is taken; `d` the function's name for the call.
pub fn val(v: &Val, d: &str, need: u8) -> String {
    match v {
        Val::Field(Field::Nr) => wrap(AS, need, format!("{d}.nr as u32")),
        Val::Field(Field::Arch) => format!("{d}.arch"),
        Val::Field(Field::Ip) => format!("{d}.instruction_pointer"),
        Val::Field(Field::Arg(i)) => format!("{d}.args[{i}]"),
        // bound by its arm's pattern: its name (the check confirms the binding)
        Val::Field(Field::Typed { name, .. }) => name.to_string(),
        Val::Const(l) => leaf(l.src, need),
        Val::Bit(op, a, b) => {
            let (p, o) = match op {
                BitOp::And => (BAND, "&"),
                BitOp::Or => (BOR, "|"),
            };
            wrap(p, need, format!("{} {o} {}", val(a, d, p), val(b, d, p + 1)))
        }
        Val::Shift(op, a, k) => {
            let o = if *op == ShiftOp::Shl { "<<" } else { ">>" };
            wrap(SHIFT, need, format!("{} {o} {}", val(a, d, SHIFT), leaf(k.src, SHIFT + 1)))
        }
        Val::Paren(a) => format!("({})", val(a, d, NONE)),
        Val::Param(_, name) => name.to_string(),
    }
}

/// A condition, where precedence `need` is taken.
pub fn cond(c: &Cond, d: &str, need: u8) -> String {
    match c {
        Cond::Static(l) => leaf(l.src, need),
        // comparisons don't chain: both sides tighter
        Cond::Cmp(op, a, b) => wrap(CMP, need, format!("{} {} {}", val(a, d, CMP + 1), cmp_op(*op), val(b, d, CMP + 1))),
        Cond::SCmp(op, a, b) => wrap(CMP, need, format!("{} {} {}", val(a, d, CMP + 1), cmp_op(*op), val(b, d, CMP + 1))),
        // a method call binds tighter than anything: its receiver an atom
        Cond::IsNull(a) => format!("{}.is_null()", val(a, d, ATOM)),
        Cond::CallMatch(m) => format!(
            "match {d}.call() {{ {} }}",
            call_arms(m, d, |b| match b {
                Cond::Block(_) => cond(b, d, NONE),
                b => format!("{},", cond(b, d, NONE)),
            })
        ),
        Cond::And(a, b) => wrap(AND, need, format!("{} && {}", cond(a, d, AND), cond(b, d, AND + 1))),
        Cond::Or(a, b) => wrap(OR, need, format!("{} || {}", cond(a, d, OR), cond(b, d, OR + 1))),
        Cond::Not(a) => wrap(UNARY, need, format!("!{}", cond(a, d, UNARY))),
        Cond::Paren(a) => format!("({})", cond(a, d, NONE)),
        Cond::Block(a) => format!("{{ {} }}", cond(a, d, NONE)),
        // a block's statements: only a body's or an arm's whole (anywhere else rustc refuses it)
        Cond::Let(l, rest) => wrap(NONE, need, format!("{} {}", let_(l, d), cond(rest, d, NONE))),
        Cond::Match(arms, default) => format!(
            "match {d}.nr as i64 {{ {} }}",
            arms_(arms, default, d, |b| match b {
                Cond::Block(_) => cond(b, d, NONE),
                b => format!("{},", cond(b, d, NONE)),
            })
        ),
        Cond::Call { name, args, .. } => {
            let mut all = vec![d.to_string()];
            all.extend(args.iter().map(|a| a.to_string()));
            format!("{name}({})", all.join(", "))
        }
        Cond::Apply { name, args, .. } => {
            format!("{name}({})", args.iter().map(|a| val(a, d, NONE)).collect::<Vec<_>>().join(", "))
        }
    }
}

fn let_(l: &Let, d: &str) -> String {
    match l {
        Let::Plain(src) => src.to_string(),
        Let::Closure { name, params, body } => {
            let ps: Vec<&str> = params.iter().map(|(_, src)| *src).collect();
            format!("let {name} = |{}| {};", ps.join(", "), cond(body, d, NONE))
        }
    }
}

/// A `match`'s arms and `_`, each body by `body` (with its separator).
fn arms_<B>(arms: &[Arm<B>], default: &B, d: &str, body: impl Fn(&B) -> String) -> String {
    let mut s = String::new();
    for a in arms {
        let pats: Vec<&str> = a.pats.iter().map(|p| p.src).collect();
        s += &pats.join(" | ");
        if let Some(g) = &a.guard {
            s += &format!(" if {}", cond(g, d, NONE));
        }
        s += &format!(" => {} ", body(&a.body));
    }
    s + &format!("_ => {}", body(default))
}

/// A `match d.call()`'s arms and `_`, each body by `body` (with its separator).
fn call_arms<B>(m: &CallMatch<B>, d: &str, body: impl Fn(&B) -> String) -> String {
    let mut s = String::new();
    for (ps, a) in m.pats.iter().zip(&m.arms) {
        let alts: Vec<String> = ps
            .iter()
            .map(|p| {
                let mut t = format!("Call::{}", p.call);
                if p.braces {
                    let mut fs: Vec<String> = p.binds.iter().map(|b| b.to_string()).collect();
                    if p.rest {
                        fs.push("..".into());
                    }
                    t += &format!(" {{ {} }}", fs.join(", "));
                }
                t
            })
            .collect();
        s += &alts.join(" | ");
        if let Some(g) = &a.guard {
            s += &format!(" if {}", cond(g, d, NONE));
        }
        s += &format!(" => {} ", body(&a.body));
    }
    s + &format!("_ => {}", body(&m.default))
}

/// A statement list: a block's contents.
pub fn stmt(s: &Stmt, d: &str) -> String {
    match s {
        Stmt::Verdict(l) => leaf(l.src, NONE),
        Stmt::Return(l) => format!("return {};", leaf(l.src, NONE)),
        Stmt::Let(l, rest) => format!("{} {}", let_(l, d), stmt(rest, d)),
        Stmt::If(c, a, b) => {
            let els = match &**b {
                Stmt::If(..) => stmt(b, d),
                Stmt::Block(x) => format!("{{ {} }}", stmt(x, d)),
                b => format!("{{ {} }}", stmt(b, d)),
            };
            format!("if {} {{ {} }} else {els}", cond(c, d, NONE), stmt(a, d))
        }
        Stmt::IfThen(c, a, rest) => format!("if {} {{ {} }} {}", cond(c, d, NONE), stmt(a, d), stmt(rest, d)),
        Stmt::Match(arms, default) => format!(
            "match {d}.nr as i64 {{ {} }}",
            arms_(arms, default, d, |b| match b {
                Stmt::Block(x) => format!("{{ {} }}", stmt(x, d)),
                b => format!("{},", stmt(b, d)),
            })
        ),
        Stmt::Block(x) => format!("{{ {} }}", stmt(x, d)),
        Stmt::CallMatch(m) => format!(
            "match {d}.call() {{ {} }}",
            call_arms(m, d, |b| match b {
                Stmt::Block(x) => format!("{{ {} }}", stmt(x, d)),
                b => format!("{},", stmt(b, d)),
            })
        ),
    }
}

impl Policy {
    /// The closure's body, as source (its block's contents).
    pub fn print(&self) -> String {
        stmt(&self.body, self.d)
    }

    /// The hygiene the print relies on (the module's doc): `Err` names what is refused.
    pub fn check(&self) -> Result<(), String> {
        let mut cx = Check { d: vec![self.d], closures: vec![], params: vec![], arm: None };
        cx.stmt(&self.body)
    }
}

/// A call's body (a `fn f(d, …) -> bool` of the file), as source: its block's contents.
pub fn print_fn_body(body: &Cond, d: &str) -> String {
    cond(body, d, NONE)
}

/// `src` has `w` as a word (an identifier token).
pub fn has_word(src: &str, w: &str) -> bool {
    let id = |c: u8| c.is_ascii_alphanumeric() || c == b'_';
    let b = src.as_bytes();
    let mut from = 0;
    while let Some(i) = src[from..].find(w) {
        let (s, e) = (from + i, from + i + w.len());
        if (s == 0 || !id(b[s - 1])) && (e == b.len() || !id(b[e])) {
            return true;
        }
        from = s + 1;
    }
    false
}

struct Check<'a> {
    /// the names of `d`: the closure's and each call's
    d: Vec<&'static str>,
    /// closures in scope: name, params, body
    closures: Vec<&'a Let>,
    /// the parameters of the closure whose body this is
    params: Vec<&'static str>,
    /// the `match d.call()` arm whose guard or body this is: its patterns
    arm: Option<&'a [CallPat]>,
}

impl<'a> Check<'a> {
    fn text(&self, src: &str, what: &str) -> Result<(), String> {
        for w in self.d.iter().chain(&self.params) {
            if has_word(src, w) {
                return Err(format!("{what} `{src}` mentions `{w}`"));
            }
        }
        Ok(())
    }

    fn let_(&mut self, l: &'a Let) -> Result<(), String> {
        match l {
            Let::Plain(src) => {
                self.text(src, "a let")?;
                // a closure it shadows is out of scope
                self.closures.retain(|c| !matches!(c, Let::Closure { name, .. } if has_word(src, name)));
                Ok(())
            }
            Let::Closure { name, params, body } => {
                for (p, _) in params {
                    if self.d.contains(p) {
                        return Err(format!("closure `{name}`'s parameter `{p}` is the call's name"));
                    }
                }
                let outer = std::mem::replace(&mut self.params, params.iter().map(|(p, _)| *p).collect());
                let r = self.cond(body);
                self.params = outer;
                r?;
                self.closures.retain(|c| !matches!(c, Let::Closure { name: n, .. } if n == name));
                self.closures.push(l);
                Ok(())
            }
        }
    }

    fn pats(&self, pats: &[Leaf<i64>]) -> Result<(), String> {
        for p in pats {
            let ok = !p.src.is_empty() && p.src.bytes().all(|c| c.is_ascii_alphanumeric() || b"_: -".contains(&c));
            if !ok {
                return Err(format!("a pattern `{}` other than a path or an integer", p.src));
            }
            self.text(p.src, "a pattern")?;
        }
        Ok(())
    }

    fn val(&self, v: &Val) -> Result<(), String> {
        match v {
            // a typed field: bound by the arm it is in, by name, its argument and type the table's
            Val::Field(f @ Field::Typed { call, name, .. }) => match self.arm {
                // bound by every alternative, as the same argument of the same type (rustc's rule:
                // one binding, one type); the field names the first's
                Some(ps @ [p0, ..])
                    if p0.call == *call
                        && Field::typed(call, name) == Some(*f)
                        && ps.iter().all(|p| p.binds.contains(name) && crate::calls::field(p.call, name) == crate::calls::field(call, name)) =>
                {
                    Ok(())
                }
                _ => Err(format!("a field `{name}` of `{call}` that its arm doesn't bind")),
            },
            Val::Field(_) => Ok(()),
            Val::Const(l) => self.text(l.src, "a leaf"),
            Val::Bit(_, a, b) => self.val(a).and(self.val(b)),
            Val::Shift(_, a, k) => self.val(a).and(self.text(k.src, "a leaf")),
            Val::Paren(a) => self.val(a),
            Val::Param(i, name) => match self.params.get(*i as usize) {
                Some(p) if p == name => Ok(()),
                _ => Err(format!("a parameter `{name}` outside its closure")),
            },
        }
    }

    fn cond(&mut self, c: &'a Cond) -> Result<(), String> {
        match c {
            Cond::Static(l) => self.text(l.src, "a leaf"),
            Cond::Cmp(op, a, b) => {
                self.val(a)?;
                self.val(b)?;
                // a signed field compared as an unsigned value: the print would mean a signed
                // comparison (rustc's, of the field's type), the code an unsigned one
                if signed(a, true) || signed(b, true) {
                    let ordered = !matches!(op, CmpOp::Eq | CmpOp::Ne);
                    if ordered || i32_field(a) || i32_field(b) {
                        return Err("an i32 or i64 field in an unsigned comparison".into());
                    }
                }
                Ok(())
            }
            Cond::SCmp(_, a, b) => {
                self.val(a)?;
                self.val(b)?;
                // i32s only: each side an i32 field's, a leaf, or (in a closure's body) a param
                if !(only_i32(a) && only_i32(b)) {
                    return Err("a signed comparison of a value that isn't an i32".into());
                }
                Ok(())
            }
            Cond::IsNull(a) => match &**a {
                Val::Field(Field::Typed { ty: Ty::Ptr, .. }) => self.val(a),
                _ => Err("`is_null` of anything but a pointer field".into()),
            },
            Cond::CallMatch(m) => self.call_match(m, |cx, b| cx.cond(b)),
            Cond::And(a, b) | Cond::Or(a, b) => {
                self.cond(a)?;
                self.cond(b)
            }
            Cond::Not(a) | Cond::Paren(a) => self.cond(a),
            Cond::Block(a) => {
                let saved = self.closures.clone();
                let r = self.cond(a);
                self.closures = saved;
                r
            }
            Cond::Let(l, rest) => {
                let saved = self.closures.clone();
                self.let_(l)?;
                let r = self.cond(rest);
                self.closures = saved;
                r
            }
            Cond::Match(arms, default) => {
                for a in arms {
                    self.pats(&a.pats)?;
                    if let Some(g) = &a.guard {
                        self.cond(g)?;
                    }
                    self.cond(&a.body)?;
                }
                self.cond(default)
            }
            Cond::Call { name, args, d, body } => {
                if self.closures.iter().any(|c| matches!(c, Let::Closure { name: n, .. } if n == name)) {
                    return Err(format!("a call of `{name}`, a closure in scope"));
                }
                for a in args {
                    self.text(a, "an argument")?;
                }
                // the callee's body: its own name for `d`, no closure of the caller's, no params
                let saved = (std::mem::replace(&mut self.d, vec![d]), std::mem::take(&mut self.closures), std::mem::take(&mut self.params));
                let r = self.cond(body);
                (self.d, self.closures, self.params) = saved;
                r
            }
            Cond::Apply { name, args, body } => {
                let Some(Let::Closure { params, body: def, .. }) = self.closures.iter().rev().find(|c| matches!(c, Let::Closure { name: n, .. } if n == name))
                else {
                    return Err(format!("a call of `{name}`, no closure in scope"));
                };
                if params.len() != args.len() {
                    return Err(format!("a call of `{name}` with {} arguments", args.len()));
                }
                for a in args {
                    self.val(a)?;
                }
                if subst(def, args) != **body {
                    return Err(format!("a call of `{name}` whose body isn't the closure's"));
                }
                // its arguments in place: their fields bound, each comparison's signs right
                self.cond(body)
            }
        }
    }

    fn stmt(&mut self, s: &'a Stmt) -> Result<(), String> {
        match s {
            Stmt::Verdict(l) | Stmt::Return(l) => self.text(l.src, "a leaf"),
            Stmt::Let(l, rest) => {
                let saved = self.closures.clone();
                self.let_(l)?;
                let r = self.stmt(rest);
                self.closures = saved;
                r
            }
            Stmt::If(c, a, b) | Stmt::IfThen(c, a, b) => {
                self.cond(c)?;
                self.stmt(a)?;
                self.stmt(b)
            }
            Stmt::Match(arms, default) => {
                for a in arms {
                    self.pats(&a.pats)?;
                    if let Some(g) = &a.guard {
                        self.cond(g)?;
                    }
                    self.stmt(&a.body)?;
                }
                self.stmt(default)
            }
            Stmt::Block(x) => self.stmt(x),
            Stmt::CallMatch(m) => self.call_match(m, |cx, b| cx.stmt(b)),
        }
    }

    /// A `match d.call()`: each arm's pattern a variant of the table's, its binds its fields,
    /// distinct; its one pattern that variant's number; its guard and body with the pattern
    /// in scope.
    fn call_match<B>(&mut self, m: &'a CallMatch<B>, body: impl Fn(&mut Self, &'a B) -> Result<(), String>) -> Result<(), String> {
        if m.pats.len() != m.arms.len() {
            return Err("a `match` on the call whose patterns aren't its arms'".into());
        }
        let outer = self.arm;
        for (ps, a) in m.pats.iter().zip(&m.arms) {
            if ps.is_empty() || a.pats.len() != ps.len() {
                return Err("an arm of `match d.call()` whose patterns aren't its own".into());
            }
            // alternatives bind the same names (rustc refuses otherwise; their types: the fields')
            if ps.iter().any(|p| {
                let (mut x, mut y) = (p.binds.clone(), ps[0].binds.clone());
                x.sort();
                y.sort();
                x != y
            }) {
                return Err("alternatives of `match d.call()` that bind different fields".into());
            }
            for (p, l) in ps.iter().zip(&a.pats) {
                let nr = crate::calls::nr(p.call).ok_or_else(|| format!("`Call::{}`, not a call of the table's", p.call))?;
                if l.value != nr || l.src != p.call {
                    return Err(format!("an arm `Call::{}` whose pattern isn't its number", p.call));
                }
                let all = crate::calls::CALLS.iter().find(|r| r.0 == p.call).map_or(0, |r| r.2.len());
                for (i, b) in p.binds.iter().enumerate() {
                    if crate::calls::field(p.call, b).is_none() || p.binds[..i].contains(b) {
                        return Err(format!("`Call::{} {{ {b} }}`: not one of its fields, or twice", p.call));
                    }
                    if self.d.contains(b) {
                        return Err(format!("a field bound as `{b}`, the call's name"));
                    }
                }
                // rustc's: all fields bound, or `..`; a bare path only for a variant without any
                let as_rust = if all == 0 { p.binds.is_empty() } else { p.braces && (p.rest || p.binds.len() == all) };
                if !as_rust {
                    return Err(format!("the pattern of `Call::{}` as Rust needs it", p.call));
                }
            }
            self.arm = Some(ps);
            let saved = self.closures.clone();
            let r = (|| {
                if let Some(g) = &a.guard {
                    self.cond(g)?;
                }
                body(self, &a.body)
            })();
            self.closures = saved;
            self.arm = outer;
            r?;
        }
        body(self, &m.default)
    }
}

/// `v` has a signed field (`also64`: an i64's too).
fn signed(v: &Val, also64: bool) -> bool {
    match v {
        Val::Field(Field::Typed { ty: Ty::I32, .. }) => true,
        Val::Field(Field::Typed { ty: Ty::I64, .. }) => also64,
        Val::Bit(_, a, b) => signed(a, also64) || signed(b, also64),
        Val::Shift(_, a, _) | Val::Paren(a) => signed(a, also64),
        _ => false,
    }
}

fn i32_field(v: &Val) -> bool {
    signed(v, false)
}

/// `v` is an i32 throughout: its fields i32s (leaves and closure params take its type).
fn only_i32(v: &Val) -> bool {
    match v {
        Val::Field(Field::Typed { ty: Ty::I32, .. }) | Val::Const(_) | Val::Param(..) => true,
        Val::Field(_) => false,
        Val::Bit(_, a, b) => only_i32(a) && only_i32(b),
        Val::Shift(..) => false,
        Val::Paren(a) => only_i32(a),
    }
}

/// A closure's body with parameter `i` replaced by `args[i]`.
pub fn subst(c: &Cond, args: &[Val]) -> Cond {
    let b = |c: &Cond| Box::new(subst(c, args));
    match c {
        Cond::Static(_) => c.clone(),
        Cond::Cmp(op, x, y) => Cond::Cmp(*op, Box::new(subst_val(x, args)), Box::new(subst_val(y, args))),
        Cond::SCmp(op, x, y) => Cond::SCmp(*op, Box::new(subst_val(x, args)), Box::new(subst_val(y, args))),
        Cond::IsNull(x) => Cond::IsNull(Box::new(subst_val(x, args))),
        Cond::And(x, y) => Cond::And(b(x), b(y)),
        Cond::Or(x, y) => Cond::Or(b(x), b(y)),
        Cond::Not(x) => Cond::Not(b(x)),
        Cond::Paren(x) => Cond::Paren(b(x)),
        Cond::Block(x) => Cond::Block(b(x)),
        // (a closure's body has none of these: the check refuses them there by their
        // substitution not matching, as they are left as they are)
        Cond::Let(..) | Cond::Match(..) | Cond::CallMatch(..) | Cond::Call { .. } | Cond::Apply { .. } => c.clone(),
    }
}

fn subst_val(v: &Val, args: &[Val]) -> Val {
    let b = |v: &Val| Box::new(subst_val(v, args));
    match v {
        Val::Field(_) | Val::Const(_) => v.clone(),
        Val::Bit(op, x, y) => Val::Bit(*op, b(x), b(y)),
        Val::Shift(op, x, k) => Val::Shift(*op, b(x), *k),
        Val::Paren(x) => Val::Paren(b(x)),
        Val::Param(i, _) => args.get(*i as usize).cloned().unwrap_or_else(|| v.clone()),
    }
}
