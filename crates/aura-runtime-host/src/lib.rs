#[unsafe(no_mangle)]
pub extern "C" fn syscall_exit(code: i32) -> ! {
    std::process::exit(code)
}
