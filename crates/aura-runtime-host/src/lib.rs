use std::cell::Cell;
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
const AURA_PANIC_PARAMS: [RuntimeTypeRef; 1] = [RuntimeTypeRef::String];
const AURA_CATCH_END_PARAMS: [RuntimeTypeRef; 0] = [];
const AURA_CATCH_BEGIN_PARAMS: [RuntimeTypeRef; 0] = [];
const AURA_PANIC_SET_HOOK_PARAMS: [RuntimeTypeRef; 1] = [RuntimeTypeRef::String];

const RUNTIME_FUNCTIONS: [RuntimeFunctionAbi; 10] = [
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
    RuntimeFunctionAbi {
        name: "aura_panic",
        params: &AURA_PANIC_PARAMS,
        ret: RuntimeTypeRef::Void,
    },
    RuntimeFunctionAbi {
        name: "aura_catch_begin",
        params: &AURA_CATCH_BEGIN_PARAMS,
        ret: RuntimeTypeRef::Void,
    },
    RuntimeFunctionAbi {
        name: "aura_catch_end",
        params: &AURA_CATCH_END_PARAMS,
        ret: RuntimeTypeRef::Int32,
    },
    RuntimeFunctionAbi {
        name: "aura_panic_set_hook",
        params: &AURA_PANIC_SET_HOOK_PARAMS,
        ret: RuntimeTypeRef::Void,
    },
];

thread_local! {
    static PANIC_ACTIVE: Cell<bool> = const { Cell::new(false) };
    static PANIC_HOOK_ENABLED: Cell<bool> = const { Cell::new(false) };
}

const BYTES_GET_OOB_MSG: &[u8] = b"Bytes.get index out of bounds\0";
const BYTES_SET_OOB_MSG: &[u8] = b"Bytes.set index out of bounds\0";

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

pub struct AuraRawAlloc {
    len: usize,
    elem_size: usize,
    elem_align: usize,
    storage: Vec<u8>,
}

pub struct AuraSlice {
    alloc: *mut AuraRawAlloc,
    start: usize,
    len: usize,
}

pub struct AuraRef {
    alloc: *mut AuraRawAlloc,
    index: usize,
}

fn checked_allocation_size(count: usize, elem_size: usize) -> Option<usize> {
    count.checked_mul(elem_size)
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

impl AuraRawAlloc {
    fn new_zeroed(count: usize, elem_size: usize, elem_align: usize) -> Self {
        let size = checked_allocation_size(count, elem_size).unwrap_or(0);
        Self {
            len: count,
            elem_size,
            elem_align: elem_align.max(1),
            storage: vec![0; size],
        }
    }

    fn slot_range(&self, index: usize) -> Option<std::ops::Range<usize>> {
        if index >= self.len {
            return None;
        }
        debug_assert!(self.elem_align.is_power_of_two());
        let start = index.checked_mul(self.elem_size)?;
        let end = start.checked_add(self.elem_size)?;
        (end <= self.storage.len()).then_some(start..end)
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

unsafe fn raw_alloc_ref<'a>(alloc: *const AuraRawAlloc) -> &'a AuraRawAlloc {
    // RawAlloc handles are runtime-created opaque pointers and leak for process lifetime.
    unsafe { &*alloc }
}

unsafe fn raw_alloc_mut<'a>(alloc: *mut AuraRawAlloc) -> &'a mut AuraRawAlloc {
    // RawAlloc handles are unique runtime allocations; mutation is slot-local.
    unsafe { &mut *alloc }
}

unsafe fn slice_ref<'a>(slice: *const AuraSlice) -> &'a AuraSlice {
    // Slice handles are runtime-created opaque pointers and point at leak-only allocations.
    unsafe { &*slice }
}

unsafe fn ref_ref<'a>(reference: *const AuraRef) -> &'a AuraRef {
    // Ref handles are runtime-created opaque pointers and point at leak-only allocations.
    unsafe { &*reference }
}

#[unsafe(no_mangle)]
pub extern "C" fn bytes_new(size: usize) -> *mut AuraBytes {
    Box::into_raw(Box::new(AuraBytes::new_zeroed(size)))
}

#[unsafe(no_mangle)]
pub extern "C" fn raw_alloc_new(
    count: usize,
    elem_size: usize,
    elem_align: usize,
) -> *mut AuraRawAlloc {
    if checked_allocation_size(count, elem_size).is_none() {
        return std::ptr::null_mut();
    }
    Box::into_raw(Box::new(AuraRawAlloc::new_zeroed(
        count, elem_size, elem_align,
    )))
}

#[unsafe(no_mangle)]
/// # Safety
/// `alloc` must point to a valid `AuraRawAlloc`.
pub unsafe extern "C" fn raw_alloc_len(alloc: *const AuraRawAlloc) -> usize {
    unsafe { raw_alloc_ref(alloc).len }
}

#[unsafe(no_mangle)]
/// # Safety
/// `alloc` must point to a valid `AuraRawAlloc`.
pub unsafe extern "C" fn raw_alloc_slice(alloc: *mut AuraRawAlloc) -> *mut AuraSlice {
    let len = unsafe { raw_alloc_ref(alloc).len };
    Box::into_raw(Box::new(AuraSlice {
        alloc,
        start: 0,
        len,
    }))
}

#[unsafe(no_mangle)]
/// # Safety
/// `slice` must point to a valid `AuraSlice`; `out` must point to writable storage of at least
/// the allocation element size.
pub unsafe extern "C" fn slice_get(slice: *const AuraSlice, index: usize, out: *mut u8) -> bool {
    let slice = unsafe { slice_ref(slice) };
    if index >= slice.len {
        return false;
    }
    let Some(absolute) = slice.start.checked_add(index) else {
        return false;
    };
    let alloc = unsafe { raw_alloc_ref(slice.alloc) };
    let Some(range) = alloc.slot_range(absolute) else {
        return false;
    };
    unsafe {
        std::ptr::copy_nonoverlapping(alloc.storage[range.clone()].as_ptr(), out, alloc.elem_size);
    }
    true
}

#[unsafe(no_mangle)]
/// # Safety
/// `slice` must point to a valid `AuraSlice`; `value` must point to readable storage of at least
/// the allocation element size.
pub unsafe extern "C" fn slice_set(slice: *mut AuraSlice, index: usize, value: *const u8) -> bool {
    let slice = unsafe { slice_ref(slice) };
    if index >= slice.len {
        return false;
    }
    let Some(absolute) = slice.start.checked_add(index) else {
        return false;
    };
    let alloc = unsafe { raw_alloc_mut(slice.alloc) };
    let Some(range) = alloc.slot_range(absolute) else {
        return false;
    };
    unsafe {
        std::ptr::copy_nonoverlapping(
            value,
            alloc.storage[range.clone()].as_mut_ptr(),
            alloc.elem_size,
        );
    }
    true
}

#[unsafe(no_mangle)]
/// # Safety
/// `slice` must point to a valid `AuraSlice`.
pub unsafe extern "C" fn slice_ref_at(slice: *mut AuraSlice, index: usize) -> *mut AuraRef {
    let slice = unsafe { slice_ref(slice) };
    if index >= slice.len {
        return std::ptr::null_mut();
    }
    let Some(absolute) = slice.start.checked_add(index) else {
        return std::ptr::null_mut();
    };
    Box::into_raw(Box::new(AuraRef {
        alloc: slice.alloc,
        index: absolute,
    }))
}

#[unsafe(no_mangle)]
/// # Safety
/// `reference` must point to a valid `AuraRef`; `out` must point to writable storage of at least
/// the allocation element size.
pub unsafe extern "C" fn ref_get(reference: *const AuraRef, out: *mut u8) {
    let reference = unsafe { ref_ref(reference) };
    let alloc = unsafe { raw_alloc_ref(reference.alloc) };
    if let Some(range) = alloc.slot_range(reference.index) {
        unsafe {
            std::ptr::copy_nonoverlapping(
                alloc.storage[range.clone()].as_ptr(),
                out,
                alloc.elem_size,
            );
        }
    }
}

#[unsafe(no_mangle)]
/// # Safety
/// `reference` must point to a valid `AuraRef`; `value` must point to readable storage of at least
/// the allocation element size.
pub unsafe extern "C" fn ref_set(reference: *mut AuraRef, value: *const u8) {
    let reference = unsafe { ref_ref(reference) };
    let alloc = unsafe { raw_alloc_mut(reference.alloc) };
    if let Some(range) = alloc.slot_range(reference.index) {
        unsafe {
            std::ptr::copy_nonoverlapping(
                value,
                alloc.storage[range.clone()].as_mut_ptr(),
                alloc.elem_size,
            );
        }
    }
}

#[cfg(test)]
unsafe fn raw_alloc_ref_alloc(reference: *const AuraRef) -> *mut AuraRawAlloc {
    unsafe { ref_ref(reference).alloc }
}

#[unsafe(no_mangle)]
/// # Safety
/// `bytes` must point to a valid `AuraBytes`.
/// Out-of-bounds `index` values raise `aura_panic` and return `0`.
pub unsafe extern "C" fn bytes_get(bytes: *const AuraBytes, index: usize) -> u8 {
    let bytes = unsafe { bytes_ref(bytes) };
    if index >= bytes.len {
        unsafe { aura_panic(BYTES_GET_OOB_MSG.as_ptr()) };
        return 0;
    }
    bytes.storage[index]
}

#[unsafe(no_mangle)]
/// # Safety
/// `bytes` must point to a valid `AuraBytes`.
/// Out-of-bounds `index` values raise `aura_panic` and leave storage unchanged.
pub unsafe extern "C" fn bytes_set(bytes: *mut AuraBytes, index: usize, value: u8) {
    let bytes = unsafe { bytes_mut(bytes) };
    if index >= bytes.len {
        unsafe { aura_panic(BYTES_SET_OOB_MSG.as_ptr()) };
        return;
    }
    bytes.storage[index] = value;
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
/// `message` should point to a valid NUL-terminated UTF-8 byte sequence.
pub unsafe extern "C" fn aura_panic(message: *const u8) {
    let message = if message.is_null() {
        "panic".to_string()
    } else {
        let len = unsafe { c_string_len(message) };
        let bytes = unsafe { std::slice::from_raw_parts(message, len) };
        String::from_utf8_lossy(bytes).into_owned()
    };
    let _ = writeln!(std::io::stderr().lock(), "panic: {message}");
    PANIC_HOOK_ENABLED.with(|enabled| {
        if enabled.get() {
            let _ = writeln!(std::io::stderr().lock(), "panic hook invoked");
        }
    });
    PANIC_ACTIVE.with(|active| active.set(true));
}

#[unsafe(no_mangle)]
pub extern "C" fn aura_catch_begin() {
    PANIC_ACTIVE.with(|active| active.set(false));
}

#[unsafe(no_mangle)]
pub extern "C" fn aura_catch_end() -> i32 {
    PANIC_ACTIVE.with(|active| {
        let was_active = active.get();
        active.set(false);
        if was_active { 1 } else { 0 }
    })
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn aura_panic_set_hook(_message: *const u8) {
    PANIC_HOOK_ENABLED.with(|enabled| enabled.set(true));
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
    use super::{
        aura_catch_begin, aura_catch_end, bytes_get, bytes_new, bytes_set, raw_alloc_len,
        raw_alloc_new, raw_alloc_ref,
        raw_alloc_ref_alloc, raw_alloc_slice, ref_get, ref_set, slice_get, slice_ref_at, slice_set,
        string_into, syscall_write, AuraBytes,
    };

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
    fn bytes_get_out_of_bounds_marks_panic_state() {
        let bytes = bytes_new(1);
        aura_catch_begin();
        let value = unsafe { bytes_get(bytes, 9) };
        assert_eq!(value, 0);
        assert_eq!(aura_catch_end(), 1);
    }

    #[test]
    fn bytes_set_out_of_bounds_marks_panic_state() {
        let bytes = bytes_new(1);
        aura_catch_begin();
        unsafe { bytes_set(bytes, 9, 1) };
        assert_eq!(aura_catch_end(), 1);
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

    #[test]
    fn raw_alloc_new_allocates_zeroed_stable_storage() {
        let alloc = raw_alloc_new(3, 4, 4);
        assert_eq!(unsafe { raw_alloc_len(alloc) }, 3);
        assert_eq!(unsafe { raw_alloc_ref(alloc).elem_align }, 4);

        let slice = unsafe { raw_alloc_slice(alloc) };
        let mut value = [255u8; 4];
        assert!(unsafe { slice_get(slice, 2, value.as_mut_ptr()) });
        assert_eq!(value, [0, 0, 0, 0]);
        assert_eq!(alloc, unsafe {
            raw_alloc_ref_alloc(slice_ref_at(slice, 2))
        });
    }

    #[test]
    fn slice_set_get_and_ref_at_are_bounds_checked() {
        let alloc = raw_alloc_new(2, 4, 4);
        let slice = unsafe { raw_alloc_slice(alloc) };
        let value = 42u32.to_le_bytes();
        assert!(unsafe { slice_set(slice, 1, value.as_ptr()) });

        let mut out = [0u8; 4];
        assert!(unsafe { slice_get(slice, 1, out.as_mut_ptr()) });
        assert_eq!(u32::from_le_bytes(out), 42);

        assert!(!unsafe { slice_get(slice, 2, out.as_mut_ptr()) });
        assert!(!unsafe { slice_set(slice, 2, value.as_ptr()) });
        assert!(unsafe { slice_ref_at(slice, 2) }.is_null());
    }

    #[test]
    fn slice_operations_reject_start_plus_index_overflow() {
        let alloc = raw_alloc_new(1, 1, 1);
        let slice = Box::into_raw(Box::new(super::AuraSlice {
            alloc,
            start: usize::MAX,
            len: 2,
        }));
        let mut out = [0u8; 1];
        let value = [7u8; 1];
        assert!(!unsafe { slice_get(slice, 1, out.as_mut_ptr()) });
        assert!(!unsafe { slice_set(slice, 1, value.as_ptr()) });
        assert!(unsafe { slice_ref_at(slice, 1) }.is_null());
    }

    #[test]
    fn raw_alloc_new_returns_null_on_size_overflow() {
        let alloc = raw_alloc_new(usize::MAX, 2, 1);
        assert!(alloc.is_null());
    }

    #[test]
    fn refs_read_and_write_stable_alloc_slots() {
        let alloc = raw_alloc_new(1, 4, 4);
        let slice = unsafe { raw_alloc_slice(alloc) };
        let reference = unsafe { slice_ref_at(slice, 0) };
        let value = 7u32.to_le_bytes();
        unsafe { ref_set(reference, value.as_ptr()) };

        let mut out = [0u8; 4];
        unsafe { ref_get(reference, out.as_mut_ptr()) };
        assert_eq!(u32::from_le_bytes(out), 7);
        assert_eq!(alloc, unsafe { raw_alloc_ref_alloc(reference) });
    }
}
