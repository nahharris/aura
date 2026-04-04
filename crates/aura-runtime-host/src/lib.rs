#[repr(C)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RtSlice {
    pub ptr: *mut u8,
    pub len: usize,
}

#[repr(C)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RtResultI32 {
    pub value: i32,
    pub err: i32,
}

#[repr(C)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RtResultI64 {
    pub value: i64,
    pub err: i32,
}

#[repr(C)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RtResultIsize {
    pub value: isize,
    pub err: i32,
}

#[repr(C)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RtResultU64 {
    pub value: u64,
    pub err: i32,
}

#[repr(C)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RtResultPtr {
    pub value: *mut u8,
    pub err: i32,
}

pub const RT_OK: i32 = 0;
pub const RT_EUNKNOWN: i32 = 1;
pub const RT_EINVAL: i32 = 2;
pub const RT_ENOENT: i32 = 3;
pub const RT_EPERM: i32 = 4;
pub const RT_EIO: i32 = 5;
pub const RT_EAGAIN: i32 = 6;
pub const RT_ENOMEM: i32 = 7;
pub const RT_EBADF: i32 = 8;

fn ok_i32(value: i32) -> RtResultI32 {
    RtResultI32 { value, err: RT_OK }
}

fn ok_i64(value: i64) -> RtResultI64 {
    RtResultI64 { value, err: RT_OK }
}

fn ok_isize(value: isize) -> RtResultIsize {
    RtResultIsize { value, err: RT_OK }
}

fn ok_u64(value: u64) -> RtResultU64 {
    RtResultU64 { value, err: RT_OK }
}

fn ok_ptr(value: *mut u8) -> RtResultPtr {
    RtResultPtr { value, err: RT_OK }
}

fn err_i32(err: i32) -> RtResultI32 {
    RtResultI32 { value: 0, err }
}

fn err_i64(err: i32) -> RtResultI64 {
    RtResultI64 { value: 0, err }
}

fn err_isize(err: i32) -> RtResultIsize {
    RtResultIsize { value: -1, err }
}

fn err_u64(err: i32) -> RtResultU64 {
    RtResultU64 { value: 0, err }
}

fn err_ptr(err: i32) -> RtResultPtr {
    RtResultPtr {
        value: std::ptr::null_mut(),
        err,
    }
}

#[cfg(unix)]
fn map_io_error_kind(err: &std::io::Error) -> i32 {
    use std::io::ErrorKind;
    match err.kind() {
        ErrorKind::NotFound => RT_ENOENT,
        ErrorKind::PermissionDenied => RT_EPERM,
        ErrorKind::WouldBlock => RT_EAGAIN,
        ErrorKind::InvalidInput | ErrorKind::InvalidData => RT_EINVAL,
        ErrorKind::OutOfMemory => RT_ENOMEM,
        ErrorKind::UnexpectedEof | ErrorKind::WriteZero | ErrorKind::BrokenPipe => RT_EIO,
        _ => RT_EUNKNOWN,
    }
}

#[cfg(windows)]
fn map_io_error_kind(err: &std::io::Error) -> i32 {
    use std::io::ErrorKind;
    match err.kind() {
        ErrorKind::NotFound => RT_ENOENT,
        ErrorKind::PermissionDenied => RT_EPERM,
        ErrorKind::WouldBlock => RT_EAGAIN,
        ErrorKind::InvalidInput | ErrorKind::InvalidData => RT_EINVAL,
        ErrorKind::OutOfMemory => RT_ENOMEM,
        ErrorKind::UnexpectedEof | ErrorKind::WriteZero | ErrorKind::BrokenPipe => RT_EIO,
        _ => RT_EUNKNOWN,
    }
}

fn fd_from_i32(fd: i32) -> Result<u32, i32> {
    if fd < 0 {
        return Err(RT_EBADF);
    }
    Ok(fd as u32)
}

fn as_ro_slice<'a>(slice: RtSlice) -> Result<&'a [u8], i32> {
    if slice.len == 0 {
        return Ok(&[]);
    }
    if slice.ptr.is_null() {
        return Err(RT_EINVAL);
    }
    // SAFETY: caller provides valid pointer/len ABI contract.
    Ok(unsafe { std::slice::from_raw_parts(slice.ptr as *const u8, slice.len) })
}

fn as_rw_slice<'a>(slice: RtSlice) -> Result<&'a mut [u8], i32> {
    if slice.len == 0 {
        return Ok(&mut []);
    }
    if slice.ptr.is_null() {
        return Err(RT_EINVAL);
    }
    // SAFETY: caller provides valid pointer/len ABI contract.
    Ok(unsafe { std::slice::from_raw_parts_mut(slice.ptr, slice.len) })
}

#[unsafe(no_mangle)]
pub extern "C" fn rt_exit(code: i32) -> ! {
    std::process::exit(code)
}

#[unsafe(no_mangle)]
pub extern "C" fn rt_fd_read(fd: i32, buf: RtSlice) -> RtResultIsize {
    use std::io::Read;
    let fd = match fd_from_i32(fd) {
        Ok(fd) => fd,
        Err(err) => return err_isize(err),
    };
    let out = match as_rw_slice(buf) {
        Ok(s) => s,
        Err(err) => return err_isize(err),
    };
    #[cfg(unix)]
    {
        use std::os::fd::FromRawFd;
        let mut file = unsafe { std::fs::File::from_raw_fd(fd as i32) };
        let result = file.read(out);
        std::mem::forget(file);
        match result {
            Ok(n) => ok_isize(n as isize),
            Err(e) => err_isize(map_io_error_kind(&e)),
        }
    }
    #[cfg(windows)]
    {
        use std::os::windows::io::FromRawHandle;
        let mut file = unsafe { std::fs::File::from_raw_handle(fd as isize as *mut _) };
        let result = file.read(out);
        std::mem::forget(file);
        match result {
            Ok(n) => ok_isize(n as isize),
            Err(e) => err_isize(map_io_error_kind(&e)),
        }
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn rt_fd_write(fd: i32, buf: RtSlice) -> RtResultIsize {
    use std::io::Write;
    let fd = match fd_from_i32(fd) {
        Ok(fd) => fd,
        Err(err) => return err_isize(err),
    };
    let bytes = match as_ro_slice(buf) {
        Ok(s) => s,
        Err(err) => return err_isize(err),
    };
    #[cfg(unix)]
    {
        use std::os::fd::FromRawFd;
        let mut file = unsafe { std::fs::File::from_raw_fd(fd as i32) };
        let result = file.write(bytes);
        std::mem::forget(file);
        match result {
            Ok(n) => ok_isize(n as isize),
            Err(e) => err_isize(map_io_error_kind(&e)),
        }
    }
    #[cfg(windows)]
    {
        use std::os::windows::io::FromRawHandle;
        let mut file = unsafe { std::fs::File::from_raw_handle(fd as isize as *mut _) };
        let result = file.write(bytes);
        std::mem::forget(file);
        match result {
            Ok(n) => ok_isize(n as isize),
            Err(e) => err_isize(map_io_error_kind(&e)),
        }
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn rt_fd_open(path_utf8: RtSlice, flags: u32, _mode: u32) -> RtResultI32 {
    let path_bytes = match as_ro_slice(path_utf8) {
        Ok(s) => s,
        Err(err) => return err_i32(err),
    };
    let path = match std::str::from_utf8(path_bytes) {
        Ok(s) => s,
        Err(_) => return err_i32(RT_EINVAL),
    };

    let mut opts = std::fs::OpenOptions::new();
    if flags & 0x1 != 0 {
        opts.read(true);
    }
    if flags & 0x2 != 0 {
        opts.write(true);
    }
    if flags & 0x4 != 0 {
        opts.append(true);
    }
    if flags & 0x8 != 0 {
        opts.create(true);
    }
    if flags & 0x10 != 0 {
        opts.truncate(true);
    }

    match opts.open(path) {
        Ok(file) => {
            #[cfg(unix)]
            {
                use std::os::fd::IntoRawFd;
                ok_i32(file.into_raw_fd())
            }
            #[cfg(windows)]
            {
                use std::os::windows::io::IntoRawHandle;
                ok_i32(file.into_raw_handle() as isize as i32)
            }
        }
        Err(e) => err_i32(map_io_error_kind(&e)),
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn rt_fd_close(fd: i32) -> RtResultI32 {
    let fd = match fd_from_i32(fd) {
        Ok(fd) => fd,
        Err(err) => return err_i32(err),
    };
    #[cfg(unix)]
    {
        use std::os::fd::FromRawFd;
        let file = unsafe { std::fs::File::from_raw_fd(fd as i32) };
        drop(file);
        ok_i32(0)
    }
    #[cfg(windows)]
    {
        use std::os::windows::io::FromRawHandle;
        let file = unsafe { std::fs::File::from_raw_handle(fd as isize as *mut _) };
        drop(file);
        ok_i32(0)
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn rt_fd_seek(fd: i32, offset: i64, whence: u32) -> RtResultI64 {
    use std::io::Seek;
    let fd = match fd_from_i32(fd) {
        Ok(fd) => fd,
        Err(err) => return err_i64(err),
    };
    let seek_from = match whence {
        0 => std::io::SeekFrom::Start(offset.max(0) as u64),
        1 => std::io::SeekFrom::Current(offset),
        2 => std::io::SeekFrom::End(offset),
        _ => return err_i64(RT_EINVAL),
    };

    #[cfg(unix)]
    {
        use std::os::fd::FromRawFd;
        let mut file = unsafe { std::fs::File::from_raw_fd(fd as i32) };
        let result = file.seek(seek_from);
        std::mem::forget(file);
        match result {
            Ok(pos) => ok_i64(pos as i64),
            Err(e) => err_i64(map_io_error_kind(&e)),
        }
    }
    #[cfg(windows)]
    {
        use std::os::windows::io::FromRawHandle;
        let mut file = unsafe { std::fs::File::from_raw_handle(fd as isize as *mut _) };
        let result = file.seek(seek_from);
        std::mem::forget(file);
        match result {
            Ok(pos) => ok_i64(pos as i64),
            Err(e) => err_i64(map_io_error_kind(&e)),
        }
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn rt_mem_map(len: usize, _prot: u32, _flags: u32) -> RtResultPtr {
    if len == 0 {
        return err_ptr(RT_EINVAL);
    }
    let mut bytes = vec![0u8; len].into_boxed_slice();
    let ptr = bytes.as_mut_ptr();
    std::mem::forget(bytes);
    ok_ptr(ptr)
}

#[unsafe(no_mangle)]
/// # Safety
///
/// `ptr` and `len` must be the exact pointer and size previously returned by
/// `rt_mem_map`, and must not have been unmapped already.
pub unsafe extern "C" fn rt_mem_unmap(ptr: *mut u8, len: usize) -> RtResultI32 {
    if ptr.is_null() || len == 0 {
        return err_i32(RT_EINVAL);
    }
    // SAFETY: pointer/len must come from rt_mem_map.
    let _ = unsafe { Box::from_raw(std::ptr::slice_from_raw_parts_mut(ptr, len)) };
    ok_i32(0)
}

#[unsafe(no_mangle)]
pub extern "C" fn rt_mem_protect(_ptr: *mut u8, _len: usize, _prot: u32) -> RtResultI32 {
    ok_i32(0)
}

#[unsafe(no_mangle)]
pub extern "C" fn rt_time_now_ns() -> RtResultU64 {
    match std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH) {
        Ok(d) => ok_u64(d.as_nanos() as u64),
        Err(_) => err_u64(RT_EUNKNOWN),
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn rt_random_fill(buf: RtSlice) -> RtResultI32 {
    let out = match as_rw_slice(buf) {
        Ok(s) => s,
        Err(err) => return err_i32(err),
    };
    #[cfg(unix)]
    {
        use std::io::Read;
        match std::fs::File::open("/dev/urandom").and_then(|mut f| f.read_exact(out)) {
            Ok(()) => ok_i32(0),
            Err(e) => err_i32(map_io_error_kind(&e)),
        }
    }
    #[cfg(windows)]
    {
        for (idx, b) in out.iter_mut().enumerate() {
            *b = (idx as u8).wrapping_mul(31).wrapping_add(17);
        }
        ok_i32(0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn time_and_memory_contract_smoke() {
        let now = rt_time_now_ns();
        assert_eq!(now.err, RT_OK);
        assert!(now.value > 0);

        let mapped = rt_mem_map(64, 0, 0);
        assert_eq!(mapped.err, RT_OK);
        assert!(!mapped.value.is_null());
        let unmapped = unsafe { rt_mem_unmap(mapped.value, 64) };
        assert_eq!(unmapped.err, RT_OK);
    }

    #[test]
    fn random_fill_contract_smoke() {
        let mut data = [0u8; 16];
        let res = rt_random_fill(RtSlice {
            ptr: data.as_mut_ptr(),
            len: data.len(),
        });
        assert_eq!(res.err, RT_OK);
    }
}
