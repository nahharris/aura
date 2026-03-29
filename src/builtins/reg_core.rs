use super::*;

pub(super) fn register(vm: &mut Vm) {
    vm.register_native("type_of", core_type_of);
    vm.register_native("to_str", core_to_str);
    vm.register_native("to_int", core_to_int);
    vm.register_native("to_float", core_to_float);
    vm.register_native("to_bool", core_to_bool);
    vm.register_native("is_null", core_is_null);
    vm.register_native("assert", core_assert);
    vm.register_native("panic", core_panic);
}
