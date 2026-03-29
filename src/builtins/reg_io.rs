use super::*;

pub(super) fn register(vm: &mut Vm) {
    vm.register_native("io_open", io_open);
    vm.register_native("io_close", io_close);
    vm.register_native("io_write", io_write);
    vm.register_native("io_read", io_read);
    vm.register_native("io_read_line", io_read_line);
    vm.register_native("io_read_all", io_read_all);
    vm.register_native("io_flush", io_flush);
}
