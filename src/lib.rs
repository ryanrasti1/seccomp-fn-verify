//! seccomp-fn-verify: the proof that a seccomp filter's program is its policy. This crate is
//! the trusted part of seccomp-fn, and the only part to review (README.md).
//!
//! A policy is a plain Rust function of its params returning the verdict function, and the
//! filter its program, from any compiler (`seccomp_fn::bpf!`, not trusted):
//!
//! ```ignore
//! pub fn policy(pid: u64, strict: bool) -> impl Fn(&libc::seccomp_data) -> u32 { move |d| { … } }
//! pub fn filter(pid: u64, strict: bool) -> Vec<libc::sock_filter> { seccomp_fn::bpf!(policy(pid, strict)) }
//! #[cfg(kani)]
//! mod proof {
//!     use super::*;
//!     seccomp_fn_verify::prove!(policy, filter);
//! }
//! ```
//!
//! [`prove!`] emits the Kani harness (`prove`): for every value of every param and every
//! `seccomp_data`, `run_bpf(&filter(params), &d) == policy(params)(&d)`. [`check_sampled`] is
//! the same assertion on sampled inputs, for a `#[test]`.
//!
//! # The rule
//!
//! Nothing here relies on a trait, type or item the compiler could emit or implement. Its
//! expansion is an expression, but an expression can hold items (`impl`s among them), so:
//! the policy and the filter are taken as plain functions through this crate's own blanket
//! impls ([`Policy`], [`Filter`]: over std's `Fn`, which nothing else can implement for a
//! function item); a symbolic param is a [`Symbolic`] type, a trait sealed here and implemented
//! only for the unsigned integers and `bool` (and tuples of them), whose values are Kani's own
//! `kani::any()` (an `impl kani::Arbitrary` emitted for an enum can't reach the proof); an enum
//! param is given by its listed values ([`prove!`]), each list a `match` with no wildcard; the
//! `seccomp_data` is made here, field by field, no `kani::assume`; the program is run here
//! ([`run_bpf`]); and the sampled check finds the constants to sample around in the program
//! itself. A compiler that emits anything at all can only make the proof fail.
//!
//! Two things the rule doesn't cover, the policy's author's to keep: the trait impls the
//! policy itself uses on an enum param (its `==`: derive `PartialEq`, and an impl the compiler
//! emitted would then conflict and not compile); and `cfg(kani)`: the proof is of the program
//! as built with `cfg(kani)` set, and an expansion could build another without it. The tests
//! (`check_sampled`, and run_bpf against Linux) run the build without it.

mod bpf;
pub mod calls;
pub mod compile;
pub mod expr;
pub mod print;
#[cfg(kani)]
mod proof;
pub use bpf::{MAX_INSNS, run_bpf};
pub use compile::compile;
pub use libc::{seccomp_data, sock_filter};

/// A policy: a function of its params (as a tuple, `Args`) returning its verdict function.
pub trait Policy<Args> {
    fn verdict(&self, args: Args, d: &seccomp_data) -> u32;
}

/// A filter: a function of the same params returning the program.
pub trait Filter<Args> {
    fn program(&self, args: Args) -> Vec<sock_filter>;
}

macro_rules! arity {
    ($($a:ident),*) => {
        impl<Func, Ret, $($a),*> Policy<($($a,)*)> for Func
        where
            Func: Fn($($a),*) -> Ret,
            Ret: Fn(&seccomp_data) -> u32,
        {
            #[allow(non_snake_case)]
            fn verdict(&self, ($($a,)*): ($($a,)*), d: &seccomp_data) -> u32 {
                self($($a),*)(d)
            }
        }
        impl<Func, $($a),*> Filter<($($a,)*)> for Func
        where
            Func: Fn($($a),*) -> Vec<sock_filter>,
        {
            #[allow(non_snake_case)]
            fn program(&self, ($($a,)*): ($($a,)*)) -> Vec<sock_filter> {
                self($($a),*)
            }
        }
    };
}
arity!();
arity!(A);
arity!(A, B);
arity!(A, B, C);
arity!(A, B, C, D);
arity!(A, B, C, D, E);
arity!(A, B, C, D, E, G);

/// A param type the proof makes symbolic: every value of it, by Kani's own `kani::any()`.
/// Sealed: implemented here, for the unsigned integers, `bool` and tuples of them, and nowhere
/// else (an enum's values are listed instead, [`prove!`]), so no impl the compiler emits can
/// narrow the values a proof covers:
///
/// ```compile_fail
/// #[derive(Clone, Copy)]
/// enum Mode { A, B }
/// impl seccomp_fn_verify::Symbolic for Mode {}
/// ```
pub trait Symbolic: sealed::Sealed + Copy {
    #[cfg(kani)]
    #[doc(hidden)]
    fn any() -> Self;
}

mod sealed {
    pub trait Sealed {}
}

macro_rules! symbolic {
    ($($t:ty),*) => {$(
        impl sealed::Sealed for $t {}
        impl Symbolic for $t {
            #[cfg(kani)]
            fn any() -> Self {
                ::kani::any()
            }
        }
    )*};
}
symbolic!(u8, u16, u32, u64, u128, usize, bool);

macro_rules! symbolic_tuple {
    ($($a:ident),*) => {
        impl<$($a: Symbolic),*> sealed::Sealed for ($($a,)*) {}
        impl<$($a: Symbolic),*> Symbolic for ($($a,)*) {
            #[cfg(kani)]
            fn any() -> Self {
                ($($a::any(),)*)
            }
        }
    };
}
symbolic_tuple!();
symbolic_tuple!(A);
symbolic_tuple!(A, B);
symbolic_tuple!(A, B, C);
symbolic_tuple!(A, B, C, D);
symbolic_tuple!(A, B, C, D, E);
symbolic_tuple!(A, B, C, D, E, G);

/// `kani::any()` of a [`Symbolic`] type: a `prove!` param `_`, or a payload's.
#[cfg(kani)]
#[doc(hidden)]
pub fn any<T: Symbolic>() -> T {
    T::any()
}

/// The proof's assertion, for every input: params and `seccomp_data` symbolic, each param
/// [`Symbolic`] (all its values), the program run by [`run_bpf`] (which also asserts the kernel
/// would take it).
#[cfg(kani)]
pub fn prove<Args: Symbolic>(policy: impl Policy<Args>, filter: impl Filter<Args>) {
    prove_at(policy, filter, Args::any())
}

/// `prove` for params `args`: `prove!`'s, each [`any`] or one of a list of values.
#[cfg(kani)]
pub fn prove_at<Args: Copy>(policy: impl Policy<Args>, filter: impl Filter<Args>, args: Args) {
    let d = seccomp_data { nr: ::kani::any(), arch: ::kani::any(), instruction_pointer: ::kani::any(), args: ::kani::any() };
    assert_eq!(run_bpf(&filter.program(args), &d), policy.verdict(args, &d));
}

/// The Kani harnesses for `policy` and `filter` (functions of the same params, in scope): only
/// the `#[::kani::proof]` fns, in the caller's module, which the caller writes as it would
/// `#[cfg(test)] mod tests`:
///
/// ```ignore
/// #[cfg(kani)]
/// mod proof {
///     use super::*;
///     seccomp_fn_verify::prove!(policy, filter, unwind = 128, (Mode = [coroutine: Coroutine, fork: Fork], bool = [off: false, on: true]));
/// }
/// ```
///
/// (`::kani` paths: a build without `cfg(kani)` that sees them doesn't compile.) With no list,
/// one harness, `<module>::proof::policy_is_filter`, every param [`Symbolic`]. `unwind` bounds
/// the program's length (default 100).
///
/// `(…)` instead gives each param in order: `_` (`any`: a [`Symbolic`] type), or a fieldless
/// enum's or a bool's values, each named: `Mode = [coroutine: Coroutine, fork: Fork]`, `bool =
/// [off: false, on: true]`, or an enum's variants with a payload left symbolic, `Option<u64> =
/// [none: None, some: Some(_)]` (the payload [`Symbolic`]). A harness is proved for each
/// combination of the listed values, a module per value of each list but the last, whose
/// values name the harnesses (`proof::coroutine::off`); each list is a `match` with no
/// wildcard, so a value left out (a variant added later) doesn't compile: the list covers the
/// type. With every param `_`, the one harness is `policy_is_filter`.
#[macro_export]
macro_rules! prove {
    ($policy:ident, $filter:ident) => {
        $crate::prove!($policy, $filter, unwind = 100);
    };
    ($policy:ident, $filter:ident, unwind = $u:literal) => {
        #[::kani::proof]
        #[::kani::unwind($u)]
        fn policy_is_filter() {
            $crate::prove($policy, $filter)
        }
    };
    ($policy:ident, $filter:ident, unwind = $u:literal, ($($spec:tt)*)) => {
        $crate::__prove_cases!([$u $policy $filter] [] $($spec)*);
    };
}

/// `prove!`'s params, one at a time: `[unwind policy filter] [args so far] params left…`.
#[doc(hidden)]
#[macro_export]
macro_rules! __prove_cases {
    ([$u:tt $p:ident $f:ident] [$($done:expr,)*]) => {
        #[::kani::proof]
        #[::kani::unwind($u)]
        fn policy_is_filter() {
            $crate::prove_at($p, $f, ($($done,)*))
        }
    };
    ($c:tt [$($done:expr,)*] _ $(, $($rest:tt)*)?) => {
        $crate::__prove_cases!($c [$($done,)* $crate::any(),] $($($rest)*)?);
    };
    ($c:tt [$($done:expr,)*] bool = [$($n:ident : $v:literal),* $(,)?] $(, $($rest:tt)*)?) => {
        #[allow(dead_code)]
        fn __covers(x: bool) {
            match x {
                $($v)|* => {}
            }
        }
        $crate::__prove_values!($c [$($done,)*] [$($n: $v,)*] [$($($rest)*)?]);
    };
    ($c:tt [$($done:expr,)*] $t:ident = [$($n:ident : $v:ident),* $(,)?] $(, $($rest:tt)*)?) => {
        #[allow(dead_code)]
        fn __covers(x: $t) {
            match x {
                $($t::$v)|* => {}
            }
        }
        $crate::__prove_values!($c [$($done,)*] [$($n: $t::$v,)*] [$($($rest)*)?]);
    };
    // An enum's variants, a payload symbolic: `Option<u64> = [none: None, some: Some(_)]`, the
    // harness's value `Some($crate::any())`, the match's pattern `Some(_)`.
    ($c:tt [$($done:expr,)*] $t:ty = [$($n:ident : $v:ident $(($p:tt))?),* $(,)?] $(, $($rest:tt)*)?) => {
        #[allow(dead_code)]
        fn __covers(x: $t) {
            match x {
                $($v $(($p))?)|* => {}
            }
        }
        $crate::__prove_values!($c [$($done,)*] [$($n: $v $(($crate::__any!($p)))?,)*] [$($($rest)*)?]);
    };
}

/// `_` in a `prove!` payload: `any`, of a [`Symbolic`] type.
#[doc(hidden)]
#[macro_export]
macro_rules! __any {
    (_) => {
        $crate::any()
    };
}

/// Each listed value: `[unwind policy filter] [args so far] [name: value, …] [params left]`.
#[doc(hidden)]
#[macro_export]
macro_rules! __prove_values {
    ($c:tt $done:tt [] $rest:tt) => {};
    ($c:tt [$($done:expr,)*] [$n:ident : $v:expr, $($more:tt)*] [$($rest:tt)*]) => {
        $crate::__prove_leaf!($c $n [$($done,)* $v,] $($rest)*);
        $crate::__prove_values!($c [$($done,)*] [$($more)*] [$($rest)*]);
    };
}

/// One value's harness, `name`: the params left that are `_` taken (`any`), a harness named by
/// the value if no list is left, else a module of that name for the next list.
#[doc(hidden)]
#[macro_export]
macro_rules! __prove_leaf {
    ([$u:tt $p:ident $f:ident] $n:ident [$($done:expr,)*]) => {
        #[allow(non_snake_case)]
        #[::kani::proof]
        #[::kani::unwind($u)]
        fn $n() {
            $crate::prove_at($p, $f, ($($done,)*))
        }
    };
    ($c:tt $n:ident [$($done:expr,)*] _ $(, $($rest:tt)*)?) => {
        $crate::__prove_leaf!($c $n [$($done,)* $crate::any(),] $($($rest)*)?);
    };
    ($c:tt $n:ident [$($done:expr,)*] $($rest:tt)+) => {
        #[allow(non_snake_case)]
        mod $n {
            #[allow(unused_imports)]
            use super::*;
            $crate::__prove_cases!($c [$($done,)*] $($rest)+);
        }
    };
}

/// The proof's assertion on `n` sampled `seccomp_data`s, for params `args`: each 32-bit word of
/// `seccomp_data` drawn from the constants the program compares that word with (found in the
/// program: the word last loaded, and each jump's `k`), one either side, and extremes. Panics on
/// the first input where the program and the policy differ. For a `#[test]`, in seconds.
pub fn check_sampled<Args: Copy + std::fmt::Debug>(policy: impl Policy<Args>, filter: impl Filter<Args>, args: Args, n: usize) {
    let prog = filter.program(args);
    // the constants per word (16 words of seccomp_data)
    let mut exact: Vec<Vec<u32>> = vec![vec![]; 16];
    let mut word = 0;
    for i in &prog {
        match i.code {
            0x20 => word = (i.k / 4) as usize % 16,
            0x15 | 0x25 | 0x35 | 0x45 => exact[word].push(i.k),
            _ => {}
        }
    }
    let near: Vec<Vec<u32>> = exact
        .iter()
        .map(|e| {
            let mut v = vec![0, 1, u32::MAX, 1 << 31];
            for &k in e {
                v.extend([k, k.wrapping_add(1), k.wrapping_sub(1)]);
            }
            v
        })
        .collect();
    let mut seed = 0x9e37_79b9_7f4a_7c15u64;
    let mut rand = move || {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        seed
    };
    for _ in 0..n {
        let mut w = [0u32; 16];
        for (i, x) in w.iter_mut().enumerate() {
            let r = rand();
            let pool = if r & 1 == 0 && !exact[i].is_empty() { &exact[i] } else { &near[i] };
            *x = pool[(r >> 1) as usize % pool.len()];
        }
        // the words as libc's seccomp_data lays them out (little-endian halves: x86-64)
        let wide = |lo: usize| w[lo] as u64 | (w[lo + 1] as u64) << 32;
        let d = seccomp_data {
            nr: w[0] as i32,
            arch: w[1],
            instruction_pointer: wide(2),
            args: [wide(4), wide(6), wide(8), wide(10), wide(12), wide(14)],
        };
        assert_eq!(
            run_bpf(&prog, &d),
            policy.verdict(args, &d),
            "params {args:?}, nr {} arch {:#x} ip {:#x} args {:x?}",
            d.nr,
            d.arch,
            d.instruction_pointer,
            d.args
        );
    }
}
