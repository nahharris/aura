use super::*;

pub(super) fn register(vm: &mut Vm) {
    vm.register_native("dict_keys", dict_keys);
    vm.register_native("dict_values", dict_values);
    vm.register_native("dict_entries", dict_entries);
    vm.register_native("dict_has", dict_has);
    vm.register_native("dict_delete", dict_delete);
    vm.register_native("dict_len", dict_len);
    vm.register_native("dict_merge", dict_merge);
}
