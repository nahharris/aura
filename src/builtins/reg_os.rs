use super::*;

pub(super) fn register(vm: &mut Vm) {
    vm.register_native("os_args", os_args);
    vm.register_native("os_env", os_env);
    vm.register_native("os_cwd", os_cwd);
    vm.register_native("os_now", os_now);
    vm.register_native("os_exists", os_exists);
    vm.register_native("os_is_file", os_is_file);
    vm.register_native("os_is_dir", os_is_dir);
    vm.register_native("os_ls", os_ls);
    vm.register_native("os_exit", os_exit);
    vm.register_native("os_delete_file", os_delete_file);
    vm.register_native("os_mkdir", os_mkdir);
    vm.register_native("os_sleep", os_sleep);
}
