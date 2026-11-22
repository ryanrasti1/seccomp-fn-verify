# seccomp-fn-verify
The trusted part of seccomp-fn: a seccomp policy's tree, its meaning, and a compiler from the tree to classic BPF **proven once, for every tree** (Kani, a proof per node kind). The front end (`bpf!`, [seccomp-fn](https://github.com/ryanrasti1/seccomp-fn)) parses a policy, a plain Rust function, into the tree and refuses to compile unless the tree, printed by this crate, is the function's own tokens. No proof runs per policy. One dependency, `libc`.

Its tests: `cargo test` (`tests/print.rs`, the print and the hygiene check; `tests/sampled.rs`; `tests/kernel.rs`, `run_bpf` against Linux). Its proofs: `cargo kani` (`src/proof.rs`, about 150 harnesses, each a few seconds). seccomp-fn's tests check the three agree on sampled calls: a policy's Rust function, its program by `run_bpf`, and Linux running the program. Its flake: `lib.kaniCheck`, a crate's proofs as a derivation, and `lib.kani`, Kani 0.68 built for Nix.

## Claim & Guarantees
For a tree `p` (`expr::Policy`) that `compile` takes (it panics on one it refuses: a nesting past the scratch memory, a shift by the width or more, a program over the kernel's limit, a tree its hygiene check refuses):

  `run_bpf(&compile(&p), &d) == p.eval(&d)`  for every `d`, and the kernel takes the program

- `eval` (`src/expr.rs`) is the tree's meaning, a line per node that is the Rust operator itself (`Cmp(Lt, a, b) => a < b`, `And(a, b) => a && b`, a `match`'s first arm whose pattern is `d.nr as i64` and whose guard holds); a leaf (an expression without `d`: a param, a const) is its value.
- The proof (`src/proof.rs`): each node kind's template meets its contract for every child meeting its own, the children opaque (a hole of symbolic length, value and exits), every leaf's value symbolic (so every param), every `d` and machine state symbolic; the induction to every tree is written at the file's head. No `kani::assume`.
- That the tree is the source: `bpf!` (not trusted) round-trips it, and `print.rs` (trusted) prints a node as the construct whose meaning is its `eval`, with exactly the parentheses precedence needs, so a tree of another shape than rustc's parse of the same tokens doesn't print as them.

The claim then rests on:
- `run_bpf` (`src/bpf.rs`) being classic BPF as the kernel's seccomp runs it, and its checks the kernel's: checked against Linux (`tests/kernel.rs`; seccomp-fn's `tests/three_ways.rs`); the proofs run each template's instructions by its `step` and check each by its `insn_ok`
- `eval` and the print (`src/expr.rs`, `src/print.rs`): read by eye, a line per node
- the hygiene check (`Policy::check`): a leaf or `let` doesn't mention `d`; a closure call's body is the closure's with its parameters replaced; a pattern is a path or an integer
- the front end's round trip, and the leaves' values being rustc's of their tokens in the policy's scope (`bpf!` binds the params in a fn item of the caller's module: nothing else in scope); a leaf being pure (it is computed once, when the filter is built)
- the coverage list (`nodes!` in `src/proof.rs`): a `match` over every node kind with no wildcard, each kind's harnesses beside it, so a kind without them doesn't compile; and the proofs having run (`kaniCheck`'s `expectHarnesses`)
- x86-64, little-endian: `bpf!` refuses a big-endian target
- Toolchain correctness: `rustc`; Kani and CBMC; `libc`

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
