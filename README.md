# seccomp-fn-verify
The trusted part of seccomp-fn: the proof that a seccomp filter's program is its policy, a plain Rust function. The compiler (`bpf!`, [seccomp-fn](https://github.com/ryanrasti1/seccomp-fn), its own repository) is not trusted; this crate checks whatever it emits. About 580 lines of source including comments (`src/lib.rs`, `src/bpf.rs`), one dependency, `libc`.

Its tests: `cargo test` (`tests/sampled.rs`; `tests/kernel.rs`, `run_bpf` against Linux on seccomp-fn's example programs, `tests/policies`, a copy of them). Its flake: `lib.kaniCheck`, a crate's proofs as a derivation, and `lib.kani`, Kani 0.68 built for Nix.

## Claim & Guarantees
For a policy `policy(params…) -> impl Fn(&libc::seccomp_data) -> u32` and a filter `filter(params…) -> Vec<libc::sock_filter>` (the same params), `seccomp_fn_verify::prove!(policy, filter)` emits Kani harnesses proving

  `run_bpf(&filter(params), &d) == policy(params)(&d)`

  (a) for every `d`: every field of libc's `seccomp_data` (syscall number, arch, instruction pointer, the six arguments) `kani::any()`
  (b) for every value of every param: each param an unsigned integer or `bool` (a tuple of them), `kani::any()` by this crate's sealed trait `Symbolic`, or an enum given by its values, every one listed (below)

and, as `run_bpf` asserts the kernel's checks first, that the kernel takes the program. No `kani::assume`: no input is excluded.

```rust
pub fn policy(pid: u64) -> impl Fn(&seccomp_data) -> u32 {
    move |d| {
        if d.arch != AUDIT_ARCH_X86_64 { return SECCOMP_RET_KILL_PROCESS; }
        match d.nr as i64 {
            SYS_read | SYS_write => SECCOMP_RET_ALLOW,
            SYS_kill if d.args[0] == pid && d.args[1] >= 1 && d.args[1] <= 64 => SECCOMP_RET_ALLOW,
            _ => SECCOMP_RET_KILL_PROCESS,
        }
    }
}
pub fn filter(pid: u64) -> Vec<sock_filter> { seccomp_fn::bpf!(policy(pid)) }
#[cfg(kani)]
mod proof {          // the Kani harness, proof::policy_is_filter
    use super::*;
    seccomp_fn_verify::prove!(policy, filter);
}
```

`check_sampled(policy, filter, params, n)` is the same assertion on `n` sampled `seccomp_data`s, for a `#[test]`: fast feedback, not the guarantee.

The claim then rests on:
- `run_bpf` (`src/bpf.rs`) being classic BPF as the kernel's seccomp runs it: checked against Linux by installing programs in forked children and comparing verdicts (`tests/kernel.rs`): the examples, with argument values whose 32-bit halves differ, and each opcode on edge values (a division by X = 0, shifts by 32 and more, scratch memory, LEN, the jumps by X); and its checks being the kernel's (`bpf_check_classic` with its rule for scratch memory, `seccomp_check_filter`): a table of programs each taken or refused by both Linux and `run_bpf` (`tests/kernel.rs` `accepts_as_linux`); in a proof, stricter: a program that loads scratch memory fails (`bpf!` emits none; the walk made proofs 4-6x slower)
- the harness (`prove`, `prove!` in `src/lib.rs`): every input made here, the policy called as written; the unwind bound an upper bound on the program's length (Kani fails an unwinding assertion rather than pass a short bound; `kaniCheck` refuses `--no-unwinding-assertions`)
- the proof having run: `kaniCheck`'s `expectHarnesses`, each harness by name, else the build fails (a run that checked none passed before)
- `Symbolic` being every value of its types: sealed here, implemented for the unsigned integers and `bool` only, each Kani's own `kani::any()`; nothing the compiler emits can implement it (an `impl kani::Arbitrary` it might emit is never used)
- x86-64, little-endian: the proof runs on x86-64 (Kani's), `run_bpf` and `seccomp_data`'s offsets are the build's; `bpf!` refuses a big-endian target, and another little-endian target's proof would need Kani there
- a param given by its values (`Mode = [coroutine: Coroutine, …]`, `bool = [off: false, on: true]`) having them all: not trusted to the list's author, but enforced by rustc's exhaustiveness check, as `prove!` makes each list a `match` with no wildcard, so a missing value (a variant added later) doesn't compile
- Toolchain correctness: `rustc`; Kani and CBMC; `libc` (opcodes, `seccomp_data`'s layout)

## The rule
Nothing here relies on a trait, type or item the compiler could emit or implement (its expansion is an expression, but an expression can hold items, `impl`s among them). The policy and the filter are taken as plain functions, through this crate's own blanket impls (`Policy`, `Filter`, over std's `Fn`: nothing else can implement them for a function item); a symbolic param is `Symbolic`, sealed here; an enum param is only its listed values; the inputs are made here; the program is run here; the sampled check finds the constants it samples around in the program itself, not in anything the compiler says. A compiler that emits anything at all can only make the proof fail, but for two things the rule doesn't reach, the policy author's:
- **An enum param's trait impls** that the policy uses (`level == Level::High`): derive them (`PartialEq`), and an impl the compiler emitted would conflict and not compile.
- **`cfg(kani)`**: the proof is of the program built with `cfg(kani)` set; an expansion could build another without it (`#[cfg(not(kani))]`). The tests (`check_sampled`, the kernel's) run the build without it: they would see a different program only where they sample.

## Not guaranteed
- **The policy is right**: the proof says the program is the function, not that the function is the policy you want.
- **Your reading of the ABI**: whether the kernel reads an argument as 32 or 64 bits, signed or not.
- **Installing it**: passing the program to `seccomp(2)`, and when, is the caller's.

# Design
1. `prove!(policy, filter)`: a `macro_rules` (no proc macro, no syn) emitting only the harness, `#[::kani::proof] fn policy_is_filter() { prove(policy, filter) }`, in the caller's own `#[cfg(kani)] mod proof { use super::*; … }` (written like `#[cfg(test)] mod tests`; the `::kani` paths make a build that forgot the `cfg` fail to compile). With `unwind = N` it bounds the program's length (default 100); with `(…)` each param in order, `_` (a `Symbolic` type's `kani::any()`) or its named values (`Mode = [coroutine: Coroutine, fork: Fork]`, `bool = [off: false, on: true]`): a harness per combination of values (`proof::coroutine::off`: a module per value of each list but the last, whose values name the harnesses), each list also a wildcard-free `match` over its type.
2. `prove`: `Symbolic` params and `kani::any()` `seccomp_data`, the assertion above.
3. `run_bpf`: one forward pass over the program (seccomp's jumps only go forward), after the kernel's checks (`bpf_check_classic` with its rule for scratch memory, `check_scratch_loads` here; `seccomp_check_filter`).

## Review checklist
| Claim | Where | Verify |
|---|---|---|
| BPF semantics | `src/bpf.rs` `run_bpf` | the kernel's: loads from `seccomp_data`'s offsets, unsigned jumps, forward only; and `tests/kernel.rs` agrees |
| the kernel's checks | `src/bpf.rs` `check`, `check_scratch_loads` | `bpf_check_classic`'s and `seccomp_check_filter`'s (the scratch rule from its behaviour); `tests/kernel.rs` `accepts_as_linux` agrees |
| harness | `src/lib.rs` `prove`, `prove!` | every param `Symbolic` or listed, every field of `d` `kani::any()`, no `assume`; calls the policy as written |
| the rule | `src/lib.rs` | nothing used comes from the compiler: `Policy`/`Filter` are blanket impls over `Fn`, `Symbolic` is sealed; the two exceptions above |
| proof runs | the caller's `cargo kani` (`lib.kaniCheck` in the flake) | fails the build when a proof fails, or an expected harness wasn't checked |

## License
MIT or Apache-2.0, at your option (`LICENSE-MIT`, `LICENSE-APACHE`).
