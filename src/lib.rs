//! seccomp-fn-verify: the trusted part of seccomp-fn. A policy, a plain Rust function, is
//! parsed by `seccomp_fn::tree!` (not trusted) into a tree held as `const` data
//! ([`tree::Tree`]); its filter is [`compile`] of the tree (proven once for every tree:
//! `proof.rs`), and a Kani harness per policy checks the tree is the policy
//! ([`filter!`], [`harnesses!`]): together, the filter's program is the policy.
//!
//! ```ignore
//! pub fn policy(pid: u64, on: bool) -> impl Fn(&libc::seccomp_data) -> u32 { move |d| { … } }
//! pub const TREE: seccomp_fn_verify::tree::Tree = seccomp_fn::tree!(policy);
//! seccomp_fn_verify::filter!(pub fn filter(pid: u64, on: bool) = TREE, policy; check filter_is_policy);
//! #[cfg(kani)]
//! mod proof {
//!     use super::*;
//!     seccomp_fn_verify::harnesses!(filter_is_policy, unwind = 64;
//!         off => (None, ::kani::any(), false);
//!         on => (None, ::kani::any(), true));
//! }
//! ```
//!
//! [`check_sampled`] is the same assertion on the program, on sampled inputs, for a `#[test]`.

mod bpf;
pub mod calls;
pub mod compile;
pub mod expr;
pub mod print;
pub mod tree;
#[cfg(kani)]
mod proof;
#[cfg(kani)]
mod tree_proof;
pub use bpf::{MAX_INSNS, run_bpf};
pub use compile::compile;
pub use libc::{seccomp_data, sock_filter};

/// The verdicts `gated!` returns, libc's, as `u64` leaves.
#[doc(hidden)]
pub mod verdicts {
    pub const KILL: u64 = libc::SECCOMP_RET_KILL_PROCESS as u64;
    pub const TRAP: u64 = libc::SECCOMP_RET_TRAP as u64;
    pub const ALLOW: u64 = libc::SECCOMP_RET_ALLOW as u64;
}

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
