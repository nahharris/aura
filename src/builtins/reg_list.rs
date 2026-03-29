use super::*;

pub(super) fn register(vm: &mut Vm) {
    vm.register_native("list_len", list_len);
    vm.register_native("list_push", list_push);
    vm.register_native("list_pop", list_pop);
    vm.register_native("list_insert", list_insert);
    vm.register_native("list_remove", list_remove);
    vm.register_native("list_contains", list_contains);
    vm.register_native("list_reverse", list_reverse);
    vm.register_native("list_sort", list_sort);
    vm.register_native("list_concat", list_concat);
    vm.register_native("list_slice", list_slice);
    vm.register_native("list_first", list_first);
    vm.register_native("list_last", list_last);
    vm.register_native("list_flatten", list_flatten);
    vm.register_native("list_range", list_range);
    vm.register_native("list_index_of", list_index_of);
}
