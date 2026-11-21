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

// The example policies' programs (seccomp-fn's `bpf!`: a dev-dependency, only for inputs
// here; what is checked is `run_bpf`, against the kernel). `tests/policies` is a copy of
// seccomp-fn's `examples/policies.rs`: `bpf!` reads its call's own file, so it is here.
mod policies;
use policies::*;
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
    // the i386 ABI's entry, from this x86-64 process: seccomp sees AUDIT_ARCH_I386
    ".globl seccomp_fn_probe80",
    "seccomp_fn_probe80:",
    "push rbx",
    "mov eax, edi",
    "xor ebx, ebx",
    "int 0x80",
    ".globl seccomp_fn_probe80_ip",
    "seccomp_fn_probe80_ip:",
    "pop rbx",
    "ret",
);

unsafe extern "C" {
    fn seccomp_fn_probe(nr: u64, a0: u64, a1: u64, a2: u64, a3: u64, a4: u64, a5: u64) -> i64;
    static seccomp_fn_probe_ip: u8;
    fn seccomp_fn_probe80(nr: u64) -> i64;
    static seccomp_fn_probe80_ip: u8;
}

/// The instruction pointer seccomp sees for a probe: just past its `syscall`.
fn probe_ip() -> u64 {
    &raw const seccomp_fn_probe_ip as u64
}

fn probe80_ip() -> u64 {
    &raw const seccomp_fn_probe80_ip as u64
}

/// include/uapi/linux/audit.h: `EM_386 | __AUDIT_ARCH_LE`.
const AUDIT_ARCH_I386: u32 = libc::EM_386 as u32 | 0x4000_0000;

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
            let r = if d.arch == AUDIT_ARCH_I386 {
                seccomp_fn_probe80(d.nr as u32 as u64)
            } else {
                seccomp_fn_probe(d.nr as u32 as u64, a[0], a[1], a[2], a[3], a[4], a[5])
            };
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

#[test]
fn compares_as_linux() {
    let calls: Vec<(u32, [u64; 6])> = [
        [5, 9, 5, 0, 8, 0],
        [5, 9, 7, 7, 100, 0],
        [4, 9, 9, 8, 100, 0],
        [0, 0, 10, 0, 0, 0],
        [0, 0, 6, 0, 3, 1],
        [0, 0, 6, 1 << 32, 3, 0],
        [u64::MAX; 6],
    ]
    .iter()
    .flat_map(|&a| [(NONE, a), (1001, a)])
    .collect();
    for level in [Level::Low, Level::High] {
        for strict in [false, true] {
            same(&compares::filter(5, 9, strict, level), &calls);
        }
    }
}

#[test]
fn table_as_linux() {
    // the pid nobody has; `kill` to it fails with ESRCH; fds that aren't open
    let pid = 0x7fff_fff0u64;
    let mut calls = vec![];
    for nr in [SYS_read, SYS_write, SYS_kill, SYS_exit, SYS_exit_group, 1000, 1001].map(|n| n as u32) {
        for a0 in [pid, pid + 1, u64::MAX] {
            for a1 in [0, 1, 9, 64, 65] {
                calls.push((nr, [a0, a1, 0, 0, 0, 0]));
            }
        }
    }
    for allow_exit in [false, true] {
        same(&table::filter(pid, allow_exit), &calls);
        // the instruction pointer's row: the probe's
        same(&table::filter(probe_ip(), allow_exit), &[(1000, [0; 6])]);
    }
}

#[test]
fn long_as_linux() {
    let calls = [(NONE, [11, 10, 11, 9, 10, 0]), (NONE, [11, 10, 11, 9, 11, 0]), (NONE, [10, 10, 11, 9, 10, 0]), (2000, [11, 10, 11, 9, 10, 0])];
    same(&long::filter(11), &calls);
}

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

#[test]
fn guarded_as_linux() {
    let pid = 0x7fff_fff0u64;
    let mut calls = vec![];
    for nr in [SYS_read as u32, SYS_kill as u32, 1000, 1001, NONE] {
        for a0 in [pid, 2, 3] {
            for a1 in [0, 9, 65] {
                for a2 in [0, 6] {
                    for a5 in [0, 7] {
                        calls.push((nr, [a0, a1, a2, 0, 0, a5]));
                    }
                }
            }
        }
    }
    for on in [false, true] {
        same(&guarded::filter(pid, on), &calls);
    }
}

/// Values whose halves differ, in every 64-bit field, against `==`, `<` and `<=` on each:
/// a wrong offset or a swapped half gives another verdict than the kernel's.
#[test]
fn halves_as_linux() {
    let vals = [0xaaaa_aaaa_0000_0005u64, 0x0000_0005_aaaa_aaaa, 0x1_0000_0000, u64::MAX, 5, 0xaaaa_aaaa_0000_0004, 0xaaaa_aaa9_0000_0005];
    for v in [0xaaaa_aaaa_0000_0005u64, 0x0000_0005_aaaa_aaaa] {
        let mut calls = vec![];
        for i in 0..6 {
            for &x in &vals {
                // the earlier arguments at v's maximum, past every test of theirs
                let mut args = [u64::MAX; 6];
                args[i] = x;
                calls.push((NONE, args));
            }
        }
        same(&halves::filter(v, 0), &calls);
    }
    // the instruction pointer: v around the probe's
    let ip = probe_ip();
    for v in [ip, ip + 1, ip - 1, ip ^ (1 << 32), ip ^ 1 ^ (1 << 32), ip.rotate_left(32)] {
        same(&halves::filter(v, 0), &[(NONE, [u64::MAX; 6])]);
    }
    // nr: at, under and over w
    for nr in [997, 998, 999, 1000, 1001] {
        same(&halves::filter(0, 999), &[(nr, [u64::MAX; 6])]);
    }
}

/// The two constants libc lacks, against the kernel: another arch (the i386 entry) and the x32
/// bit are killed, an x86-64 call isn't.
#[test]
fn abi_as_linux() {
    same(&abi::filter(), &[(NONE, [0; 6]), (X32_SYSCALL_BIT | NONE, [0; 6]), (X32_SYSCALL_BIT, [0; 6]), (u32::MAX, [0; 6])]);
    let p = behind_prefix(&abi::filter(), probe80_ip());
    let d = SeccompData { nr: 20, arch: AUDIT_ARCH_I386, instruction_pointer: probe80_ip(), args: [0; 6] };
    assert_eq!(run_bpf(&p, &d), SECCOMP_RET_KILL_PROCESS);
    assert_eq!(kernel(&p, &d), Outcome::Killed);
}

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
