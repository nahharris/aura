use super::*;

pub(super) fn register(vm: &mut Vm) {
    vm.register_native("math_abs", math_abs);
    vm.register_native("math_floor", math_floor);
    vm.register_native("math_ceil", math_ceil);
    vm.register_native("math_round", math_round);
    vm.register_native("math_sqrt", math_sqrt);
    vm.register_native("math_pow", math_pow);
    vm.register_native("math_log", math_log);
    vm.register_native("math_log2", math_log2);
    vm.register_native("math_log10", math_log10);
    vm.register_native("math_sin", math_sin);
    vm.register_native("math_cos", math_cos);
    vm.register_native("math_tan", math_tan);
    vm.register_native("math_asin", math_asin);
    vm.register_native("math_acos", math_acos);
    vm.register_native("math_atan", math_atan);
    vm.register_native("math_atan2", math_atan2);
    vm.register_native("math_min", math_min);
    vm.register_native("math_max", math_max);
    vm.register_native("math_clamp", math_clamp);
    vm.register_native("math_random", math_random);
    vm.register_native("math_pi", math_pi);
    vm.register_native("math_e", math_e);
    vm.register_native("math_inf", math_inf);
    vm.register_native("math_is_nan", math_is_nan);
    vm.register_native("math_is_inf", math_is_inf);
    vm.register_native("math_trunc", math_trunc);
    vm.register_native("math_fract", math_fract);
    vm.register_native("math_sign", math_sign);
}
