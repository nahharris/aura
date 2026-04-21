use std::io::Write;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RuntimeTypeRef {
    Int32,
    ISize,
    USize,
    UInt8,
    Void,
    Bytes,
    String,
    Never,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RuntimeFunctionAbi {
    pub name: &'static str,
    pub params: &'static [RuntimeTypeRef],
    pub ret: RuntimeTypeRef,
}

const SYSCALL_EXIT_PARAMS: [RuntimeTypeRef; 1] = [RuntimeTypeRef::Int32];
const SYSCALL_WRITE_PARAMS: [RuntimeTypeRef; 2] = [RuntimeTypeRef::Int32, RuntimeTypeRef::Bytes];
const BYTES_NEW_PARAMS: [RuntimeTypeRef; 1] = [RuntimeTypeRef::USize];
const BYTES_GET_PARAMS: [RuntimeTypeRef; 2] = [RuntimeTypeRef::Bytes, RuntimeTypeRef::USize];
const BYTES_SET_PARAMS: [RuntimeTypeRef; 3] = [
    RuntimeTypeRef::Bytes,
    RuntimeTypeRef::USize,
    RuntimeTypeRef::UInt8,
];
const STRING_INTO_PARAMS: [RuntimeTypeRef; 1] = [RuntimeTypeRef::String];

const RUNTIME_FUNCTIONS: [RuntimeFunctionAbi; 6] = [
    RuntimeFunctionAbi {
        name: "syscall_exit",
        params: &SYSCALL_EXIT_PARAMS,
        ret: RuntimeTypeRef::Never,
    },
    RuntimeFunctionAbi {
        name: "syscall_write",
        params: &SYSCALL_WRITE_PARAMS,
        ret: RuntimeTypeRef::ISize,
    },
    RuntimeFunctionAbi {
        name: "bytes_new",
        params: &BYTES_NEW_PARAMS,
        ret: RuntimeTypeRef::Bytes,
    },
    RuntimeFunctionAbi {
        name: "bytes_get",
        params: &BYTES_GET_PARAMS,
        ret: RuntimeTypeRef::UInt8,
    },
    RuntimeFunctionAbi {
        name: "bytes_set",
        params: &BYTES_SET_PARAMS,
        ret: RuntimeTypeRef::Void,
    },
    RuntimeFunctionAbi {
        name: "string_into",
        params: &STRING_INTO_PARAMS,
        ret: RuntimeTypeRef::Bytes,
    },
];

pub fn runtime_functions() -> &'static [RuntimeFunctionAbi] {
    &RUNTIME_FUNCTIONS
}

pub fn runtime_function(name: &str) -> Option<&'static RuntimeFunctionAbi> {
    RUNTIME_FUNCTIONS.iter().find(|abi| abi.name == name)
}

pub struct AuraBytes {
    len: usize,
    storage: Vec<u8>,
}

impl AuraBytes {
    fn new_zeroed(size: usize) -> Self {
        Self {
            len: size,
            storage: vec![0; size],
        }
    }

    fn from_storage(storage: Vec<u8>) -> Self {
        Self {
            len: storage.len(),
            storage,
        }
    }
}

unsafe fn bytes_ref<'a>(bytes: *const AuraBytes) -> &'a AuraBytes {
    // The Aura runtime treats `Bytes` as an opaque owned pointer.
    unsafe { &*bytes }
}

unsafe fn bytes_mut<'a>(bytes: *mut AuraBytes) -> &'a mut AuraBytes {
    // Bounds checks are intentionally absent for now; callers own the UB contract.
    unsafe { &mut *bytes }
}

unsafe fn c_string_len(mut ptr: *const u8) -> usize {
    let mut len = 0usize;
    while unsafe { *ptr } != 0 {
        len += 1;
        ptr = unsafe { ptr.add(1) };
    }
    len
}

#[unsafe(no_mangle)]
pub extern "C" fn bytes_new(size: usize) -> *mut AuraBytes {
    Box::into_raw(Box::new(AuraBytes::new_zeroed(size)))
}

#[unsafe(no_mangle)]
/// # Safety
/// `bytes` must point to a valid `AuraBytes`, and `index` must be in bounds.
pub unsafe extern "C" fn bytes_get(bytes: *const AuraBytes, index: usize) -> u8 {
    unsafe { bytes_ref(bytes).storage[index] }
}

#[unsafe(no_mangle)]
/// # Safety
/// `bytes` must point to a valid `AuraBytes`, and `index` must be in bounds.
pub unsafe extern "C" fn bytes_set(bytes: *mut AuraBytes, index: usize, value: u8) {
    unsafe {
        bytes_mut(bytes).storage[index] = value;
    }
}

#[unsafe(no_mangle)]
/// # Safety
/// `string` must be a valid NUL-terminated UTF-8 byte sequence.
pub unsafe extern "C" fn string_into(string: *const u8) -> *mut AuraBytes {
    let len = unsafe { c_string_len(string) };
    let storage = unsafe { std::slice::from_raw_parts(string, len) }.to_vec();
    Box::into_raw(Box::new(AuraBytes::from_storage(storage)))
}

#[unsafe(no_mangle)]
/// # Safety
/// `bytes` must point to a valid `AuraBytes`.
pub unsafe extern "C" fn syscall_write(fd: i32, bytes: *const AuraBytes) -> isize {
    let bytes = unsafe { bytes_ref(bytes) };
    let result = match fd {
        1 => {
            let mut stdout = std::io::stdout().lock();
            stdout
                .write_all(&bytes.storage)
                .and_then(|_| stdout.flush())
                .map(|_| bytes.len as isize)
        }
        2 => {
            let mut stderr = std::io::stderr().lock();
            stderr
                .write_all(&bytes.storage)
                .and_then(|_| stderr.flush())
                .map(|_| bytes.len as isize)
        }
        _ => return -1,
    };

    result.unwrap_or(-1)
}

#[unsafe(no_mangle)]
pub extern "C" fn syscall_exit(code: i32) -> ! {
    std::process::exit(code)
}

#[cfg(test)]
mod tests {
    use super::{AuraBytes, bytes_get, bytes_new, bytes_set, string_into, syscall_write};

    #[test]
    fn bytes_new_allocates_zeroed_storage() {
        let bytes = bytes_new(4);
        let bytes = unsafe { &*bytes };
        assert_eq!(bytes.len, 4);
        assert_eq!(bytes.storage, vec![0, 0, 0, 0]);
    }

    #[test]
    fn bytes_get_and_set_round_trip_a_value() {
        let bytes = bytes_new(2);
        unsafe {
            bytes_set(bytes, 1, 65);
            assert_eq!(bytes_get(bytes, 1), 65);
        }
    }

    #[test]
    fn string_into_copies_utf8_bytes_into_owned_storage() {
        let source = b"Hello, world!\0";
        let bytes = unsafe { string_into(source.as_ptr()) };
        let bytes = unsafe { &*bytes };
        assert_eq!(bytes.len, 13);
        assert_eq!(bytes.storage, b"Hello, world!");
    }

    #[test]
    fn syscall_write_returns_byte_count_for_stdout_and_stderr() {
        let stdout_bytes = Box::into_raw(Box::new(AuraBytes::from_storage(b"out".to_vec())));
        let stderr_bytes = Box::into_raw(Box::new(AuraBytes::from_storage(b"err".to_vec())));

        let stdout_written = unsafe { syscall_write(1, stdout_bytes) };
        let stderr_written = unsafe { syscall_write(2, stderr_bytes) };

        assert_eq!(stdout_written, 3);
        assert_eq!(stderr_written, 3);
    }

    #[test]
    fn syscall_write_returns_negative_one_for_invalid_fd() {
        let bytes = Box::into_raw(Box::new(AuraBytes::from_storage(b"oops".to_vec())));
        let written = unsafe { syscall_write(99, bytes) };
        assert_eq!(written, -1);
    }
}
