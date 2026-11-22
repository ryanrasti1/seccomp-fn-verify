//! `run_bpf` against Linux: programs installed in a forked child, each call's verdict as the
//! kernel gave it (the call's errno, a SIGSYS caught or not, the call made) compared with
//! `run_bpf`'s on the same `seccomp_data`. The proof trusts `run_bpf`; this is why.
//!
//! Each call is made from one `syscall` instruction (`probe`, below), and every program is
//! behind a prefix that allows any call from elsewhere, so the child's own calls (exit) pass.
//! Errnos the programs return are 100 and up; the calls they allow are harmless (unassigned
//! numbers, bad fds, a pid that doesn't exist) and fail with the kernel's own errno, or exit.
//!
//! The hand-assembled programs here (the prefix, `alu_as_linux`) write opcodes and offsets out
//! as numbers on purpose, from the kernel's documentation: independent of the library's
//! constants, so that a layout both the library and the macro got wrong shows here.

// (The example policies' programs against Linux are seccomp-fn's tests, `tests/kernel.rs`
// and `tests/three_ways.rs`: this crate depends on nothing of seccomp-fn's.)
use libc::{SECCOMP_RET_ALLOW, SECCOMP_RET_ERRNO, SECCOMP_RET_KILL_PROCESS, SECCOMP_RET_TRAP, seccomp_data, sock_filter};
use seccomp_fn_verify::run_bpf;

type SockFilter = sock_filter;
type SeccompData = seccomp_data;

/// `d` as a call: its fields (libc's `seccomp_data` has no `Debug`).
fn show(d: &SeccompData) -> String {
    format!("nr {} arch {:#x} ip {:#x} args {:x?}", d.nr, d.arch, d.instruction_pointer, d.args)
}

/// `prog` installed on the calling thread (`SECCOMP_SET_MODE_FILTER`).
fn install(prog: &[SockFilter]) -> Result<(), ()> {
    let fprog = libc::sock_fprog { len: prog.len() as u16, filter: prog.as_ptr() as *mut SockFilter };
    // SAFETY: seccomp reads `fprog` and the instructions, both live for the call.
    let r = unsafe { libc::syscall(libc::SYS_seccomp, libc::SECCOMP_SET_MODE_FILTER, 0, &fprog as *const libc::sock_fprog) };
    if r == 0 { Ok(()) } else { Err(()) }
}

std::arch::global_asm!(
    ".globl seccomp_fn_probe",
    "seccomp_fn_probe:",
    "mov rax, rdi",
    "mov rdi, rsi",
    "mov rsi, rdx",
    "mov rdx, rcx",
    "mov r10, r8",
    "mov r8, r9",
    "mov r9, [rsp + 8]",
    "syscall",
    ".globl seccomp_fn_probe_ip",
    "seccomp_fn_probe_ip:",
    "ret",
);

unsafe extern "C" {
    fn seccomp_fn_probe(nr: u64, a0: u64, a1: u64, a2: u64, a3: u64, a4: u64, a5: u64) -> i64;
    static seccomp_fn_probe_ip: u8;
}

/// The instruction pointer seccomp sees for a probe: just past its `syscall`.
fn probe_ip() -> u64 {
    &raw const seccomp_fn_probe_ip as u64
}

/// `EM_X86_64 | __AUDIT_ARCH_64BIT | __AUDIT_ARCH_LE`.
const AUDIT_ARCH_X86_64: u32 = libc::EM_X86_64 as u32 | 0x8000_0000 | 0x4000_0000;

/// What a call came to, as the parent sees it.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
enum Outcome {
    Allowed,
    Errno(u32),
    Trapped,
    Killed,
}

fn expected(verdict: u32) -> Outcome {
    match verdict & 0xffff_0000 {
        SECCOMP_RET_ALLOW => Outcome::Allowed,
        SECCOMP_RET_ERRNO => Outcome::Errno(verdict & 0xffff),
        SECCOMP_RET_TRAP => Outcome::Trapped,
        // (KILL_THREAD, 0, is a division by X == 0's: the child's only thread, so the process)
        SECCOMP_RET_KILL_PROCESS | libc::SECCOMP_RET_KILL_THREAD => Outcome::Killed,
        v => panic!("verdict {v:#x}"),
    }
}

extern "C" fn trapped(_: libc::c_int) {
    // SAFETY: _exit is async-signal-safe.
    unsafe { libc::_exit(200) }
}

/// `prog` (behind the prefix) installed in a child that makes the call `d`: what came of it.
fn kernel(prog: &[SockFilter], d: &SeccompData) -> Outcome {
    // SAFETY: the child calls only async-signal-safe functions (prctl, sigaction, seccomp, the
    // probe, _exit): the program is built before the fork.
    match unsafe { libc::fork() } {
        0 => unsafe {
            libc::prctl(libc::PR_SET_NO_NEW_PRIVS, 1, 0, 0, 0);
            // no core dump of a child killed by SIGSYS: each one took ~100 ms
            libc::prctl(libc::PR_SET_DUMPABLE, 0, 0, 0, 0);
            libc::signal(libc::SIGSYS, trapped as *const () as libc::sighandler_t);
            if install(prog).is_err() {
                libc::_exit(201);
            }
            let a = d.args;
            let r = seccomp_fn_probe(d.nr as u32 as u64, a[0], a[1], a[2], a[3], a[4], a[5]);
            // an allowed exit doesn't return; anything else is an errno (or a success)
            libc::_exit(if r < 0 { (-r).min(199) as i32 } else { 0 })
        },
        pid => {
            let mut st = 0;
            // SAFETY: waits for the child.
            assert_eq!(unsafe { libc::waitpid(pid, &mut st, 0) }, pid);
            if libc::WIFSIGNALED(st) {
                assert_eq!(libc::WTERMSIG(st), libc::SIGSYS, "the child died by signal {}", libc::WTERMSIG(st));
                return Outcome::Killed;
            }
            match libc::WEXITSTATUS(st) {
                200 => Outcome::Trapped,
                201 => panic!("the kernel refused the program"),
                e @ 100..=199 => Outcome::Errno(e as u32),
                _ => Outcome::Allowed,
            }
        }
    }
}

/// Any call not from the probe at `ip`: ALLOW. Then `prog`.
fn behind_prefix(prog: &[SockFilter], ip: u64) -> Vec<SockFilter> {
    let i = |code, jt, jf, k| SockFilter { code, jt, jf, k };
    let mut p = vec![
        i(0x20, 0, 0, 8),
        i(0x15, 0, 2, ip as u32),
        i(0x20, 0, 0, 12),
        i(0x15, 1, 0, (ip >> 32) as u32),
        i(0x06, 0, 0, SECCOMP_RET_ALLOW),
    ];
    p.extend_from_slice(prog);
    p
}

fn same(prog: &[SockFilter], calls: &[(u32, [u64; 6])]) {
    let p = behind_prefix(prog, probe_ip());
    for &(nr, args) in calls {
        let d = SeccompData { nr: nr as i32, arch: AUDIT_ARCH_X86_64, instruction_pointer: probe_ip(), args };
        assert_eq!(kernel(&p, &d), expected(run_bpf(&p, &d)), "{}", show(&d));
    }
}

/// An unassigned number: allowed, it fails with ENOSYS.
const NONE: u32 = 999;

/// The opcodes the macro doesn't emit: ALU, X, scratch memory, RET A, JSET.
#[test]
fn alu_as_linux() {
    let i = |code, jt, jf, k| SockFilter { code, jt, jf, k };
    let prog = [
        i(0x20, 0, 0, 16), // A = args[0] low
        i(0x02, 0, 0, 3),  // M[3] = A
        i(0x54, 0, 0, 0xff), // A &= 0xff
        i(0x04, 0, 0, 1),  // A += 1
        i(0x07, 0, 0, 0),  // X = A
        i(0x60, 0, 0, 3),  // A = M[3]
        i(0x45, 0, 2, 0x100), // A & 0x100 ?
        i(0x87, 0, 0, 0),  // A = X
        i(0x24, 0, 0, 2),  // A *= 2
        i(0x0c, 0, 0, 0),  // A += X
        i(0x54, 0, 0, 0x3f), // A &= 0x3f
        i(0x04, 0, 0, 100), // A += 100
        i(0x44, 0, 0, SECCOMP_RET_ERRNO), // A |= ERRNO
        i(0x16, 0, 0, 0),  // return A
    ];
    let calls: Vec<(u32, [u64; 6])> = [0u64, 1, 0xff, 0x100, 0x1ff, 0x12345, u64::MAX].iter().map(|&a| (NONE, [a, 0, 0, 0, 0, 0])).collect();
    same(&prog, &calls);
}

/// Values whose halves differ, in every 64-bit field, against `==`, `<` and `<=` on each:
/// a wrong offset or a swapped half gives another verdict than the kernel's.
/// The two constants libc lacks, against the kernel: another arch (the i386 entry) and the x32
/// bit are killed, an x86-64 call isn't.
/// Operand values at the edges: 0, 1, around a shift's width, the sign bit, all ones, and one
/// whose nibbles all differ.
const EDGES: [u32; 8] = [0, 1, 31, 32, 33, 0x8000_0000, 0xffff_ffff, 0x1234_5678];

fn i(code: u16, jt: u8, jf: u8, k: u32) -> SockFilter {
    SockFilter { code, jt, jf, k }
}

/// `body` run with A = args[0]'s low half and X = args[1]'s, for each `(a, x)` of `regs`.
fn with_regs(body: &[SockFilter]) -> Vec<SockFilter> {
    let mut p = vec![i(0x20, 0, 0, 24), i(0x07, 0, 0, 0), i(0x20, 0, 0, 16)];
    p.extend_from_slice(body);
    p
}

fn calls(regs: &[(u32, u32)]) -> Vec<(u32, [u64; 6])> {
    regs.iter().map(|&(a, x)| (NONE, [a as u64, x as u64, 0, 0, 0, 0])).collect()
}

/// A after `body` (as `with_regs`), the kernel's and run_bpf's the same: a verdict's errno is
/// 16 bits and the child's exit status 8, so A is read out a nibble per program, errno 100 + it.
fn same_a(body: &[SockFilter], regs: &[(u32, u32)]) {
    for j in 0..8 {
        let mut p = with_regs(body);
        p.extend([i(0x74, 0, 0, 4 * j), i(0x54, 0, 0, 0xf), i(0x04, 0, 0, 100), i(0x44, 0, 0, SECCOMP_RET_ERRNO), i(0x16, 0, 0, 0)]);
        same(&p, &calls(regs));
    }
}

fn pairs() -> Vec<(u32, u32)> {
    EDGES.iter().flat_map(|&a| EDGES.map(|x| (a, x))).collect()
}

/// Each ALU op by a constant, each edge constant the kernel takes (a division by 0 and a shift
/// by 32 or more it refuses: `accepts_as_linux`), on each edge A.
#[test]
fn alu_k_as_linux() {
    let regs: Vec<(u32, u32)> = EDGES.map(|a| (a, 0)).to_vec();
    // ADD SUB MUL DIV OR AND LSH RSH XOR
    for op in [0x04, 0x14, 0x24, 0x34, 0x44, 0x54, 0x64, 0x74, 0xa4] {
        for k in EDGES {
            if (op == 0x34 && k == 0) || ((op == 0x64 || op == 0x74) && k >= 32) {
                continue;
            }
            same_a(&[i(op, 0, 0, k)], &regs);
        }
    }
}

/// Each ALU op by X, and NEG, on each pair of edge values: a division by X == 0 (the program
/// ends, verdict 0), a shift by X of 32 or more.
#[test]
fn alu_x_as_linux() {
    for op in [0x0c, 0x1c, 0x2c, 0x3c, 0x4c, 0x5c, 0x6c, 0x7c, 0xac, 0x84] {
        same_a(&[i(op, 0, 0, 0)], &pairs());
    }
}

/// The loads but from `seccomp_data`: immediates, LEN, scratch memory by A and X, TAX, TXA.
#[test]
fn loads_as_linux() {
    let regs = pairs();
    for k in EDGES {
        same_a(&[i(0x00, 0, 0, k)], &regs[..1]); // A = k
        same_a(&[i(0x01, 0, 0, k), i(0x87, 0, 0, 0)], &regs[..1]); // X = k; A = X
    }
    same_a(&[i(0x80, 0, 0, 0)], &regs[..1]); // A = len
    same_a(&[i(0x81, 0, 0, 0), i(0x87, 0, 0, 0)], &regs[..1]); // X = len; A = X
    let mem = [
        i(0x03, 0, 0, 15), // M[15] = X
        i(0x02, 0, 0, 0),  // M[0] = A
        i(0x00, 0, 0, 7),  // A = 7
        i(0x02, 0, 0, 7),  // M[7] = A
        i(0x60, 0, 0, 15), // A = M[15]
        i(0x61, 0, 0, 0),  // X = M[0]
        i(0x1c, 0, 0, 0),  // A -= X
        i(0x61, 0, 0, 7),  // X = M[7]
        i(0x2c, 0, 0, 0),  // A *= X
    ];
    same_a(&mem, &regs);
}

/// Each conditional jump, by a constant and by X, on each pair of edge values.
#[test]
fn jumps_as_linux() {
    let regs = pairs();
    let tail = [i(0x06, 0, 0, SECCOMP_RET_ERRNO | 101), i(0x06, 0, 0, SECCOMP_RET_ERRNO | 102)];
    // JEQ JGT JGE JSET
    for op in [0x15, 0x25, 0x35, 0x45] {
        for k in EDGES {
            let mut p = with_regs(&[i(op, 0, 1, k)]);
            p.extend(tail);
            same(&p, &calls(&regs));
        }
        let mut p = with_regs(&[i(op | 0x08, 0, 1, 0)]);
        p.extend(tail);
        same(&p, &calls(&regs));
    }
    // JA, and a conditional jump's both offsets past an instruction
    let mut p = with_regs(&[i(0x05, 0, 0, 1), i(0x06, 0, 0, SECCOMP_RET_ERRNO | 103), i(0x1d, 1, 2, 0), i(0x06, 0, 0, SECCOMP_RET_ERRNO | 104)]);
    p.extend(tail);
    same(&p, &calls(&regs));
}

/// Whether the kernel takes `prog` (behind the prefix, which leaves the program's scratch
/// memory as unstored as at a program's start).
fn kernel_accepts(prog: &[SockFilter]) -> bool {
    let p = behind_prefix(prog, probe_ip());
    // SAFETY: as `kernel`'s child.
    match unsafe { libc::fork() } {
        0 => unsafe {
            libc::prctl(libc::PR_SET_NO_NEW_PRIVS, 1, 0, 0, 0);
            libc::_exit(if install(&p).is_ok() { 0 } else { 1 })
        },
        pid => {
            let mut st = 0;
            // SAFETY: waits for the child.
            assert_eq!(unsafe { libc::waitpid(pid, &mut st, 0) }, pid);
            assert!(libc::WIFEXITED(st), "the child: {st:#x}");
            libc::WEXITSTATUS(st) == 0
        }
    }
}

/// Programs at the edge of what the kernel takes: its verdict, and `run_bpf`'s (which panics on
/// a program the kernel refuses), the table's.
#[test]
fn accepts_as_linux() {
    const R: u16 = 0x06; // RET k
    let table: &[(&str, bool, &[SockFilter])] = &[
        ("a return", true, &[i(0x06, 0, 0, 0)]),
        // scratch memory (check_scratch_loads): a load of a slot stored on every path only
        ("M[0] loaded, never stored", false, &[i(0x60, 0, 0, 0), i(0x16, 0, 0, 0)]),
        ("M[15] loaded into X, never stored", false, &[i(0x61, 0, 0, 15), i(0x16, 0, 0, 0)]),
        ("M[0] stored, loaded", true, &[i(0x02, 0, 0, 0), i(0x60, 0, 0, 0), i(0x16, 0, 0, 0)]),
        ("M[0] stored by X, loaded into X", true, &[i(0x03, 0, 0, 0), i(0x61, 0, 0, 0), i(0x16, 0, 0, 0)]),
        ("M[1] stored, M[0] loaded", false, &[i(0x02, 0, 0, 1), i(0x60, 0, 0, 0), i(0x16, 0, 0, 0)]),
        ("M[0] stored on one path", false, &[i(0x15, 0, 1, 0), i(0x02, 0, 0, 0), i(0x60, 0, 0, 0), i(0x16, 0, 0, 0)]),
        ("M[3] stored before the branch", true, &[i(0x02, 0, 0, 3), i(0x15, 0, 1, 0), i(0x02, 0, 0, 0), i(0x60, 0, 0, 3), i(0x16, 0, 0, 0)]),
        ("a JA over the store", false, &[i(0x05, 0, 0, 1), i(0x02, 0, 0, 0), i(0x60, 0, 0, 0), i(0x16, 0, 0, 0)]),
        ("a JA after the store", true, &[i(0x02, 0, 0, 0), i(0x05, 0, 0, 0), i(0x60, 0, 0, 0), i(0x16, 0, 0, 0)]),
        // the kernel's, by instruction: a return doesn't clear what's stored, a jump sets all
        ("M[0] loaded after a return, never stored", false, &[i(R, 0, 0, 0), i(0x60, 0, 0, 0), i(0x16, 0, 0, 0)]),
        ("M[0] loaded after a return, stored before it", true, &[i(0x02, 0, 0, 0), i(R, 0, 0, 0), i(0x60, 0, 0, 0), i(0x16, 0, 0, 0)]),
        ("M[0] loaded where only a jump goes, not stored", false, &[i(0x15, 1, 1, 0), i(R, 0, 0, 0), i(0x60, 0, 0, 0), i(0x16, 0, 0, 0)]),
        ("M[16] stored", false, &[i(0x02, 0, 0, 16), i(R, 0, 0, 0)]),
        ("M[16] loaded", false, &[i(0x60, 0, 0, 16), i(0x16, 0, 0, 0)]),
        // constants
        ("A / 0", false, &[i(0x34, 0, 0, 0), i(0x16, 0, 0, 0)]),
        ("A / 1", true, &[i(0x34, 0, 0, 1), i(0x16, 0, 0, 0)]),
        ("A << 31", true, &[i(0x64, 0, 0, 31), i(0x16, 0, 0, 0)]),
        ("A << 32", false, &[i(0x64, 0, 0, 32), i(0x16, 0, 0, 0)]),
        ("A >> 32", false, &[i(0x74, 0, 0, 32), i(0x16, 0, 0, 0)]),
        // loads from seccomp_data
        ("the last word", true, &[i(0x20, 0, 0, 60), i(0x16, 0, 0, 0)]),
        ("past the last word", false, &[i(0x20, 0, 0, 64), i(0x16, 0, 0, 0)]),
        ("an unaligned word", false, &[i(0x20, 0, 0, 2), i(0x16, 0, 0, 0)]),
        ("a half word", false, &[i(0x28, 0, 0, 0), i(0x16, 0, 0, 0)]),
        ("a byte", false, &[i(0x30, 0, 0, 0), i(0x16, 0, 0, 0)]),
        ("an indirect word", false, &[i(0x40, 0, 0, 0), i(0x16, 0, 0, 0)]),
        ("X = 4 * (byte & 0xf)", false, &[i(0xb1, 0, 0, 0), i(0x16, 0, 0, 0)]),
        // opcodes seccomp doesn't take
        ("A % 3", false, &[i(0x94, 0, 0, 3), i(0x16, 0, 0, 0)]),
        ("A % X", false, &[i(0x9c, 0, 0, 0), i(0x16, 0, 0, 0)]),
        ("return X", false, &[i(0x0e, 0, 0, 0)]),
        ("opcode 0xff", false, &[i(0xff, 0, 0, 0), i(R, 0, 0, 0)]),
        // jumps
        ("a JA to the last", true, &[i(0x05, 0, 0, 0), i(R, 0, 0, 0)]),
        ("a JA out", false, &[i(0x05, 0, 0, 1), i(R, 0, 0, 0)]),
        ("a JEQ's jt out", false, &[i(0x15, 1, 0, 0), i(R, 0, 0, 0)]),
        ("a JEQ X's jf out", false, &[i(0x1d, 0, 1, 0), i(R, 0, 0, 0)]),
        ("the last not a return", false, &[i(R, 0, 0, 0), i(0x20, 0, 0, 0)]),
    ];
    let d = SeccompData { nr: NONE as i32, arch: AUDIT_ARCH_X86_64, instruction_pointer: 0, args: [0; 6] };
    for &(what, takes, prog) in table {
        assert_eq!(kernel_accepts(prog), takes, "the kernel: {what}");
        let p = behind_prefix(prog, probe_ip());
        assert_eq!(std::panic::catch_unwind(|| run_bpf(&p, &d)).is_ok(), takes, "run_bpf: {what}");
    }
}
