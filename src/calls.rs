//! The typed view of a call: [`Call`], each argument as the kernel reads it (its C type's
//! width and sign), from Linux v7.0's x86-64 syscall table and `SYSCALL_DEFINE`s. Generated (from
//! unsharek's `cargo xtask calls`): do not edit. Trusted: the compiler takes each bound field's
//! argument number and type from [`CALLS`] (`expr::Field::typed`), never from the macro.

use libc::seccomp_data;

/// An argument's C type: its width and sign as the kernel reads it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Ty {
    U16,
    U32,
    I32,
    U64,
    I64,
    Usize,
    Ptr,
}

/// An argument the kernel reads as a pointer. A filter can't follow it (the program chooses it,
/// and may change the memory after the check), so the only meaningful test is null.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Ptr(pub u64);

impl Ptr {
    pub fn is_null(self) -> bool {
        self.0 == 0
    }

    /// The raw number: comparing it is visibly deliberate.
    pub fn addr(self) -> u64 {
        self.0
    }
}

/// A call of the table's, its arguments typed; any other number is [`Call::Other`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Call {
    /// 0
    Read { fd: u32, buf: Ptr, count: usize },
    /// 1
    Write { fd: u32, buf: Ptr, count: usize },
    /// 3
    Close { fd: u32 },
    /// 5
    Fstat { fd: u32, statbuf: Ptr },
    /// 15
    RtSigreturn,
    /// 17
    Pread64 { fd: u32, buf: Ptr, count: usize, pos: i64 },
    /// 18
    Pwrite64 { fd: u32, buf: Ptr, count: usize, pos: i64 },
    /// 41
    Socket { family: i32, r#type: i32, protocol: i32 },
    /// 42
    Connect { fd: i32, uservaddr: Ptr, addrlen: i32 },
    /// 48
    Shutdown { fd: i32, how: i32 },
    /// 49
    Bind { fd: i32, umyaddr: Ptr, addrlen: i32 },
    /// 50
    Listen { fd: i32, backlog: i32 },
    /// 51
    Getsockname { fd: i32, usockaddr: Ptr, usockaddr_len: Ptr },
    /// 52
    Getpeername { fd: i32, usockaddr: Ptr, usockaddr_len: Ptr },
    /// 54
    Setsockopt { fd: i32, level: i32, optname: i32, optval: Ptr, optlen: i32 },
    /// 55
    Getsockopt { fd: i32, level: i32, optname: i32, optval: Ptr, optlen: Ptr },
    /// 56
    Clone { clone_flags: u64, newsp: u64, parent_tidptr: Ptr, child_tidptr: Ptr, tls: u64 },
    /// 60
    Exit { error_code: i32 },
    /// 74
    Fsync { fd: u32 },
    /// 77
    Ftruncate { fd: u32, length: i64 },
    /// 217
    Getdents64 { fd: u32, dirent: Ptr, count: u32 },
    /// 231
    ExitGroup { error_code: i32 },
    /// 257
    Openat { dfd: i32, filename: Ptr, flags: i32, mode: u16 },
    /// 258
    Mkdirat { dfd: i32, pathname: Ptr, mode: u16 },
    /// 263
    Unlinkat { dfd: i32, pathname: Ptr, flag: i32 },
    /// 266
    Symlinkat { oldname: Ptr, newdfd: i32, newname: Ptr },
    /// 267
    Readlinkat { dfd: i32, pathname: Ptr, buf: Ptr, bufsiz: i32 },
    /// 268
    Fchmodat { dfd: i32, filename: Ptr, mode: u16 },
    /// 271
    Ppoll { ufds: Ptr, nfds: u32, tsp: Ptr, sigmask: Ptr, sigsetsize: usize },
    /// 280
    Utimensat { dfd: i32, filename: Ptr, utimes: Ptr, flags: i32 },
    /// 288
    Accept4 { fd: i32, upeer_sockaddr: Ptr, upeer_addrlen: Ptr, flags: i32 },
    /// 316
    Renameat2 { olddfd: i32, oldname: Ptr, newdfd: i32, newname: Ptr, flags: u32 },
    Other { nr: i32 },
}

/// Each row: the variant, its number, its arguments (name, type) in order.
pub const CALLS: &[(&str, i64, &[(&str, Ty)])] = &[
    ("Read", 0, &[("fd", Ty::U32), ("buf", Ty::Ptr), ("count", Ty::Usize)]),
    ("Write", 1, &[("fd", Ty::U32), ("buf", Ty::Ptr), ("count", Ty::Usize)]),
    ("Close", 3, &[("fd", Ty::U32)]),
    ("Fstat", 5, &[("fd", Ty::U32), ("statbuf", Ty::Ptr)]),
    ("RtSigreturn", 15, &[]),
    ("Pread64", 17, &[("fd", Ty::U32), ("buf", Ty::Ptr), ("count", Ty::Usize), ("pos", Ty::I64)]),
    ("Pwrite64", 18, &[("fd", Ty::U32), ("buf", Ty::Ptr), ("count", Ty::Usize), ("pos", Ty::I64)]),
    ("Socket", 41, &[("family", Ty::I32), ("type", Ty::I32), ("protocol", Ty::I32)]),
    ("Connect", 42, &[("fd", Ty::I32), ("uservaddr", Ty::Ptr), ("addrlen", Ty::I32)]),
    ("Shutdown", 48, &[("fd", Ty::I32), ("how", Ty::I32)]),
    ("Bind", 49, &[("fd", Ty::I32), ("umyaddr", Ty::Ptr), ("addrlen", Ty::I32)]),
    ("Listen", 50, &[("fd", Ty::I32), ("backlog", Ty::I32)]),
    ("Getsockname", 51, &[("fd", Ty::I32), ("usockaddr", Ty::Ptr), ("usockaddr_len", Ty::Ptr)]),
    ("Getpeername", 52, &[("fd", Ty::I32), ("usockaddr", Ty::Ptr), ("usockaddr_len", Ty::Ptr)]),
    ("Setsockopt", 54, &[("fd", Ty::I32), ("level", Ty::I32), ("optname", Ty::I32), ("optval", Ty::Ptr), ("optlen", Ty::I32)]),
    ("Getsockopt", 55, &[("fd", Ty::I32), ("level", Ty::I32), ("optname", Ty::I32), ("optval", Ty::Ptr), ("optlen", Ty::Ptr)]),
    ("Clone", 56, &[("clone_flags", Ty::U64), ("newsp", Ty::U64), ("parent_tidptr", Ty::Ptr), ("child_tidptr", Ty::Ptr), ("tls", Ty::U64)]),
    ("Exit", 60, &[("error_code", Ty::I32)]),
    ("Fsync", 74, &[("fd", Ty::U32)]),
    ("Ftruncate", 77, &[("fd", Ty::U32), ("length", Ty::I64)]),
    ("Getdents64", 217, &[("fd", Ty::U32), ("dirent", Ty::Ptr), ("count", Ty::U32)]),
    ("ExitGroup", 231, &[("error_code", Ty::I32)]),
    ("Openat", 257, &[("dfd", Ty::I32), ("filename", Ty::Ptr), ("flags", Ty::I32), ("mode", Ty::U16)]),
    ("Mkdirat", 258, &[("dfd", Ty::I32), ("pathname", Ty::Ptr), ("mode", Ty::U16)]),
    ("Unlinkat", 263, &[("dfd", Ty::I32), ("pathname", Ty::Ptr), ("flag", Ty::I32)]),
    ("Symlinkat", 266, &[("oldname", Ty::Ptr), ("newdfd", Ty::I32), ("newname", Ty::Ptr)]),
    ("Readlinkat", 267, &[("dfd", Ty::I32), ("pathname", Ty::Ptr), ("buf", Ty::Ptr), ("bufsiz", Ty::I32)]),
    ("Fchmodat", 268, &[("dfd", Ty::I32), ("filename", Ty::Ptr), ("mode", Ty::U16)]),
    ("Ppoll", 271, &[("ufds", Ty::Ptr), ("nfds", Ty::U32), ("tsp", Ty::Ptr), ("sigmask", Ty::Ptr), ("sigsetsize", Ty::Usize)]),
    ("Utimensat", 280, &[("dfd", Ty::I32), ("filename", Ty::Ptr), ("utimes", Ty::Ptr), ("flags", Ty::I32)]),
    ("Accept4", 288, &[("fd", Ty::I32), ("upeer_sockaddr", Ty::Ptr), ("upeer_addrlen", Ty::Ptr), ("flags", Ty::I32)]),
    ("Renameat2", 316, &[("olddfd", Ty::I32), ("oldname", Ty::Ptr), ("newdfd", Ty::I32), ("newname", Ty::Ptr), ("flags", Ty::U32)]),
];

/// `d.call()`: the call, typed (each argument truncated to its type, as the kernel reads it).
pub trait CallExt {
    fn call(&self) -> Call;
}

impl CallExt for seccomp_data {
    fn call(&self) -> Call {
        let a = &self.args;
        match self.nr as i64 {
            0 => Call::Read { fd: a[0] as u32, buf: Ptr(a[1]), count: a[2] as usize },
            1 => Call::Write { fd: a[0] as u32, buf: Ptr(a[1]), count: a[2] as usize },
            3 => Call::Close { fd: a[0] as u32 },
            5 => Call::Fstat { fd: a[0] as u32, statbuf: Ptr(a[1]) },
            15 => Call::RtSigreturn,
            17 => Call::Pread64 { fd: a[0] as u32, buf: Ptr(a[1]), count: a[2] as usize, pos: a[3] as i64 },
            18 => Call::Pwrite64 { fd: a[0] as u32, buf: Ptr(a[1]), count: a[2] as usize, pos: a[3] as i64 },
            41 => Call::Socket { family: a[0] as i32, r#type: a[1] as i32, protocol: a[2] as i32 },
            42 => Call::Connect { fd: a[0] as i32, uservaddr: Ptr(a[1]), addrlen: a[2] as i32 },
            48 => Call::Shutdown { fd: a[0] as i32, how: a[1] as i32 },
            49 => Call::Bind { fd: a[0] as i32, umyaddr: Ptr(a[1]), addrlen: a[2] as i32 },
            50 => Call::Listen { fd: a[0] as i32, backlog: a[1] as i32 },
            51 => Call::Getsockname { fd: a[0] as i32, usockaddr: Ptr(a[1]), usockaddr_len: Ptr(a[2]) },
            52 => Call::Getpeername { fd: a[0] as i32, usockaddr: Ptr(a[1]), usockaddr_len: Ptr(a[2]) },
            54 => Call::Setsockopt { fd: a[0] as i32, level: a[1] as i32, optname: a[2] as i32, optval: Ptr(a[3]), optlen: a[4] as i32 },
            55 => Call::Getsockopt { fd: a[0] as i32, level: a[1] as i32, optname: a[2] as i32, optval: Ptr(a[3]), optlen: Ptr(a[4]) },
            56 => Call::Clone { clone_flags: a[0], newsp: a[1], parent_tidptr: Ptr(a[2]), child_tidptr: Ptr(a[3]), tls: a[4] },
            60 => Call::Exit { error_code: a[0] as i32 },
            74 => Call::Fsync { fd: a[0] as u32 },
            77 => Call::Ftruncate { fd: a[0] as u32, length: a[1] as i64 },
            217 => Call::Getdents64 { fd: a[0] as u32, dirent: Ptr(a[1]), count: a[2] as u32 },
            231 => Call::ExitGroup { error_code: a[0] as i32 },
            257 => Call::Openat { dfd: a[0] as i32, filename: Ptr(a[1]), flags: a[2] as i32, mode: a[3] as u16 },
            258 => Call::Mkdirat { dfd: a[0] as i32, pathname: Ptr(a[1]), mode: a[2] as u16 },
            263 => Call::Unlinkat { dfd: a[0] as i32, pathname: Ptr(a[1]), flag: a[2] as i32 },
            266 => Call::Symlinkat { oldname: Ptr(a[0]), newdfd: a[1] as i32, newname: Ptr(a[2]) },
            267 => Call::Readlinkat { dfd: a[0] as i32, pathname: Ptr(a[1]), buf: Ptr(a[2]), bufsiz: a[3] as i32 },
            268 => Call::Fchmodat { dfd: a[0] as i32, filename: Ptr(a[1]), mode: a[2] as u16 },
            271 => Call::Ppoll { ufds: Ptr(a[0]), nfds: a[1] as u32, tsp: Ptr(a[2]), sigmask: Ptr(a[3]), sigsetsize: a[4] as usize },
            280 => Call::Utimensat { dfd: a[0] as i32, filename: Ptr(a[1]), utimes: Ptr(a[2]), flags: a[3] as i32 },
            288 => Call::Accept4 { fd: a[0] as i32, upeer_sockaddr: Ptr(a[1]), upeer_addrlen: Ptr(a[2]), flags: a[3] as i32 },
            316 => Call::Renameat2 { olddfd: a[0] as i32, oldname: Ptr(a[1]), newdfd: a[2] as i32, newname: Ptr(a[3]), flags: a[4] as u32 },
            _ => Call::Other { nr: self.nr },
        }
    }
}

/// The number of `call` (a variant's name).
pub fn nr(call: &str) -> Option<i64> {
    CALLS.iter().find(|r| r.0 == call).map(|r| r.1)
}

/// Argument `name` of `call`: its index and type (a raw identifier's `r#` dropped).
pub fn field(call: &str, name: &str) -> Option<(u8, Ty)> {
    let name = name.strip_prefix("r#").unwrap_or(name);
    let row = CALLS.iter().find(|r| r.0 == call)?;
    row.2.iter().position(|f| f.0 == name).map(|i| (i as u8, row.2[i].1))
}
