use super::*;

pub(super) fn register(vm: &mut Vm) {
    vm.register_native("str_len", str_len);
    vm.register_native("str_upper", str_upper);
    vm.register_native("str_lower", str_lower);
    vm.register_native("str_trim", str_trim);
    vm.register_native("str_trim_start", str_trim_start);
    vm.register_native("str_trim_end", str_trim_end);
    vm.register_native("str_starts_with", str_starts_with);
    vm.register_native("str_ends_with", str_ends_with);
    vm.register_native("str_contains", str_contains);
    vm.register_native("str_split", str_split);
    vm.register_native("str_join", str_join);
    vm.register_native("str_replace", str_replace);
    vm.register_native("str_slice", str_slice);
    vm.register_native("str_find", str_find);
    vm.register_native("str_repeat", str_repeat);
    vm.register_native("str_chars", str_chars);
    vm.register_native("str_bytes", str_bytes);
    vm.register_native("str_from_chars", str_from_chars);
    vm.register_native("str_parse_int", str_parse_int);
    vm.register_native("str_parse_float", str_parse_float);
}
