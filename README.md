# seccomp-fn-verify
The trusted part of seccomp-fn: a seccomp policy's tree, its meaning, and a compiler from the tree to classic BPF **proven once, for every tree** (Kani, a proof per node kind). The front end (`bpf!`, [seccomp-fn](https://github.com/ryanrasti1/seccomp-fn)) parses a policy, a plain Rust function, into the tree and refuses to compile unless the tree, printed by this crate, is the function's own tokens. No proof runs per policy. One dependency, `libc`.

Its tests: `cargo test` (`tests/print.rs`, the print and the hygiene check; `tests/sampled.rs`; `tests/kernel.rs`, `run_bpf` against Linux). Its proofs: `cargo kani` (`src/proof.rs`, 246 harnesses, and `src/tree_proof.rs`, 36, each a few seconds). seccomp-fn's tests check the three agree on sampled calls: a policy's Rust function, its program by `run_bpf`, and Linux running the program. Its flake: `lib.kaniCheck`, a crate's proofs as a derivation, and `lib.kani`, Kani 0.68 built for Nix.

## Claim & Guarantees
A policy's filter, made by `filter!` from its tree (`TREE`, `seccomp_fn::tree!`'s const data), gives the policy's verdict on every call, for the params its harnesses cover:

  `run_bpf(&filter(params), &d) == policy(params)(&d)`  for every `d`, and the kernel takes the program

It is three proofs on one tree:
1. **The compiler, once** (`src/proof.rs`): for every tree `compile` takes, `run_bpf(&compile(&t), &d) == t.eval(&d)`; each node kind's template meets its contract for every child meeting its own (the induction at the file's head).
2. **The tree's meaning in place, once** (`src/tree_proof.rs`): the const tree's `eval` is its built tree's (`tree.eval(p, d) == tree.build(p).eval(d)`), node kind by node kind.
3. **The tree is the policy, per policy** (`filter!`'s check, `harnesses!`): `TREE.eval(params, d) == policy(params)(&d)` for a symbolic `d` and the params each harness gives (a few seconds each: the tcb's 54 take 1-8 s).

`filter!` makes the filter (`compile(&TREE.build(params))`) and the check from one list of params, so the filter's tree is the checked one. The tree is `const` data: no code the front end emits runs in a harness (it can't `kani::assume`), and the check needs nothing of the front end to be right: a wrong tree fails it. So the front end (`seccomp_fn::tree!`), the print and the round trip (`src/print.rs`, `bpf!`'s) are not trusted: they are there for errors at compile time.

**What a reviewer reads** (non-comment lines): `src/bpf.rs` (247: `run_bpf`, the kernel's checks; `tests/kernel.rs` checks it against Linux), `src/expr.rs` (201: the tree, `eval_by`, a line per node), `src/proof.rs`'s prelude and coverage list (the hole model, the contracts, the induction; `nodes!`), `src/tree_proof.rs` (147: the lemmas and their induction), and the macros of `src/tree.rs` (`filter!`, `harnesses!`, `gated!`, about 60). Proven, not read: `src/compile.rs` (453), `src/tree.rs`'s `build` and `eval` (proven equal). Not trusted: `src/print.rs` (398), seccomp-fn.

The claim then rests on:
- `run_bpf` being classic BPF as the kernel's seccomp runs it, and its checks the kernel's (`tests/kernel.rs`, and seccomp-fn's three-way test)
- `eval` (`src/expr.rs`) read by eye: only in that the compiler's proof and the per-policy check meet on it (any meaning would do, if both use it)
- the harnesses covering the params: an enum's values are listed by the harnesses' author (`harnesses!`); integers and bools `kani::any()`
- the policy's purity: the check calls `policy(params)(&d)` as written; a policy reading anything but its params and `d` isn't one function of them
- the proofs having run (`kaniCheck`'s `expectHarnesses`)
- x86-64, little-endian; Toolchain correctness: `rustc`; Kani and CBMC; `libc`

## Not guaranteed
- **The policy is right**: the program is the function, not the policy you want.
- **Your reading of the ABI**: whether the kernel reads an argument as 32 or 64 bits, signed or not.
- **Installing it**: passing the program to `seccomp(2)`, and when, is the caller's.

# Design
1. **The tree** (`src/expr.rs`): values (a field of `d`, a leaf, `&`, `|`, a shift by a leaf, a closure's parameter), conditions (a leaf, a comparison, `&&`, `||`, `!`, a `match` of conditions, a call of a fn of the file or of a closure, inlined), statements (a verdict, `return`, `let`, `if`, `match d.nr as i64`, a block); `eval_by`, each node's line with its children's values by a closure (`eval` passes itself; a proof, symbolic values).
2. **The compiler** (`src/compile.rs`): a fixed template per node kind, its children generators (from exits, or half and depth, to their code), emitted backwards so every forward jump's target is known. A condition's code goes to its exit `t` or `f`; a value's leaves a 32-bit half in A, a nested one through `M[depth]`; a statement's returns. A condition decided when the program is built (`stat`) is its jump; a template drops a decided child's branch. Jumps past 253 go through a JA (`jcond`); 64-bit comparisons are two halves (`cmp_half`). Both are lemmas: proven of their instructions, held by their contracts elsewhere.
3. **The print** (`src/print.rs`) and the hygiene check.
4. **`run_bpf`**: one forward pass over the program after the kernel's checks; `compile` runs those checks on every program it returns.

## Review checklist
| Claim | Where | Verify |
|---|---|---|
| BPF semantics | `src/bpf.rs` `run_bpf`, `step` | the kernel's; `tests/kernel.rs` agrees |
| the kernel's checks | `src/bpf.rs` `check`, `insn_ok`, `check_scratch_loads` | `bpf_check_classic`'s and `seccomp_check_filter`'s; `tests/kernel.rs` `accepts_as_linux` |
| the meaning | `src/expr.rs` `eval_by` | each line the Rust construct's meaning |
| the print | `src/print.rs` | each node the construct of its `eval` line; parentheses by precedence; a leaf's precedence read conservatively (`tests/print.rs`) |
| the proof | `src/proof.rs`, its head | the hole model and contracts; the induction; `nodes!` covers every kind |
| proof runs | `cargo kani` (`lib.kaniCheck`) | every harness checked |

## License
MIT or Apache-2.0, at your option (`LICENSE-MIT`, `LICENSE-APACHE`).
