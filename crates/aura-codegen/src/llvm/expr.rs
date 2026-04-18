#[cfg(feature = "llvm-backend")]
use aura_typecheck::checked_ir::BinaryOpKind;
use aura_typecheck::checked_ir::CheckedExpr;

#[cfg(feature = "llvm-backend")]
use super::error::CodegenError;

#[cfg(feature = "llvm-backend")]
use inkwell::{
    AddressSpace,
    module::Linkage,
    types::BasicTypeEnum,
    values::{BasicMetadataValueEnum, BasicValue, BasicValueEnum},
};

#[cfg(feature = "llvm-backend")]
use super::context::CodegenContext;

pub fn classify_expr_kind(expr: &CheckedExpr) -> &'static str {
    match expr {
        CheckedExpr::Ident(_) => "ident",
        CheckedExpr::Int(_) => "int",
        CheckedExpr::Float(_) => "float",
        CheckedExpr::Char(_) => "char",
        CheckedExpr::String(_) => "string",
        CheckedExpr::Call { .. } => "call",
        CheckedExpr::BinaryOp { .. } => "binary_op",
        CheckedExpr::DotIdent { .. } => "dot_ident",
        CheckedExpr::Tuple(_) => "tuple",
        CheckedExpr::Struct(_) => "struct",
        CheckedExpr::Block(_) => "block",
        CheckedExpr::Closure { .. } => "closure",
        CheckedExpr::Any => "any",
        CheckedExpr::List(_) => "list",
        CheckedExpr::Dict(_) => "dict",
        CheckedExpr::MacroApply { .. } => "macro_apply",
        CheckedExpr::Label { .. } => "label",
        CheckedExpr::MultiArm(_) => "multi_arm",
        CheckedExpr::If { .. } => "if",
        CheckedExpr::Cases { .. } => "cases",
        CheckedExpr::Return { .. } => "return",
        CheckedExpr::Break { .. } => "break",
        CheckedExpr::Continue => "continue",
        CheckedExpr::Coerce { .. } => "coerce",
        CheckedExpr::Cast { .. } => "cast",
    }
}

#[cfg(feature = "llvm-backend")]
pub fn lower_expr<'ctx, 'm>(
    cg: &CodegenContext<'ctx, 'm>,
    expr: &CheckedExpr,
) -> Result<BasicValueEnum<'ctx>, CodegenError> {
    match expr {
        CheckedExpr::Int(value) => {
            let parsed = value
                .parse::<i64>()
                .map_err(|_| CodegenError::UnsupportedExpression("int"))?;
            Ok(cg
                .context
                .i64_type()
                .const_int(parsed as u64, true)
                .as_basic_value_enum())
        }
        CheckedExpr::Float(value) => {
            let parsed = value
                .parse::<f64>()
                .map_err(|_| CodegenError::UnsupportedExpression("float"))?;
            Ok(cg
                .context
                .f64_type()
                .const_float(parsed)
                .as_basic_value_enum())
        }
        CheckedExpr::Char(value) => {
            let ch = value
                .chars()
                .next()
                .ok_or(CodegenError::UnsupportedExpression("char"))?;
            Ok(cg
                .context
                .i8_type()
                .const_int(ch as u64, false)
                .as_basic_value_enum())
        }
        CheckedExpr::String(value) => {
            let ptr = cg
                .builder
                .build_global_string_ptr(value, "str")
                .map_err(|_| CodegenError::UnsupportedExpression("string"))?;
            Ok(ptr.as_pointer_value().as_basic_value_enum())
        }
        CheckedExpr::Block(items) => {
            let mut last = cg
                .context
                .ptr_type(AddressSpace::default())
                .const_null()
                .as_basic_value_enum();
            for item in items {
                last = lower_expr(cg, item)?;
            }
            Ok(last)
        }
        CheckedExpr::DotIdent { name, payload } => match (name.as_str(), payload.as_deref()) {
            ("ok", _) => Ok(cg.context.i32_type().const_zero().as_basic_value_enum()),
            ("err", Some(CheckedExpr::Int(v))) => {
                let parsed = v
                    .parse::<u8>()
                    .map_err(|_| CodegenError::UnsupportedExpression("result_err_u8"))?;
                Ok(cg
                    .context
                    .i32_type()
                    .const_int(parsed as u64, false)
                    .as_basic_value_enum())
            }
            _ => Err(CodegenError::UnsupportedExpression("dot_ident")),
        },
        CheckedExpr::Ident(name) => {
            if name == "main" {
                if let Some(function) = cg.module.get_function("aura_user_main") {
                    return Ok(function
                        .as_global_value()
                        .as_pointer_value()
                        .as_basic_value_enum());
                }
            }
            if let Some(global) = cg.module.get_global(name) {
                let value_ty: inkwell::types::BasicTypeEnum<'ctx> = global
                    .get_value_type()
                    .try_into()
                    .map_err(|_| CodegenError::UnsupportedExpression("ident"))?;
                let loaded = cg
                    .builder
                    .build_load(value_ty, global.as_pointer_value(), &format!("load_{name}"))
                    .map_err(|_| CodegenError::UnsupportedExpression("ident"))?;
                return Ok(loaded);
            }
            Err(CodegenError::UnsupportedExpression("ident"))
        }
        CheckedExpr::Call { callee, args } => lower_call(cg, callee, args),
        CheckedExpr::BinaryOp { op, lhs, rhs, .. } => lower_binary_op(cg, *op, lhs, rhs),
        _ => Err(CodegenError::UnsupportedExpression(classify_expr_kind(
            expr,
        ))),
    }
}

#[cfg(feature = "llvm-backend")]
fn lower_call<'ctx, 'm>(
    cg: &CodegenContext<'ctx, 'm>,
    callee: &CheckedExpr,
    args: &[CheckedExpr],
) -> Result<BasicValueEnum<'ctx>, CodegenError> {
    if let CheckedExpr::DotIdent { name, payload } = callee {
        if let Some(payload_expr) = payload {
            let _ = lower_expr(cg, payload_expr)?;
        }

        return match name.as_str() {
            "ok" => Ok(cg.context.i32_type().const_zero().as_basic_value_enum()),
            "err" => {
                let err_u8 = match args.first() {
                    Some(CheckedExpr::Int(v)) => v
                        .parse::<u8>()
                        .map_err(|_| CodegenError::UnsupportedExpression("result_err_u8"))?,
                    _ => 1u8,
                };
                Ok(cg
                    .context
                    .i32_type()
                    .const_int(err_u8 as u64, false)
                    .as_basic_value_enum())
            }
            _ => Err(CodegenError::UnsupportedExpression("call")),
        };
    }

    let CheckedExpr::Ident(name) = callee else {
        return Err(CodegenError::UnsupportedExpression("call"));
    };
    let resolved_name = if name == "main" {
        "aura_user_main"
    } else {
        name.as_str()
    };

    let function = if let Some(function) = cg.module.get_function(resolved_name) {
        function
    } else if let Some(fn_ty) = runtime_builtin_function_type(cg, resolved_name) {
        cg.module
            .add_function(resolved_name, fn_ty, Some(Linkage::External))
    } else {
        return Err(CodegenError::UnsupportedExpression("call"));
    };

    let param_tys = function.get_type().get_param_types();
    let mut lowered_args = Vec::with_capacity(args.len());
    for (idx, arg) in args.iter().enumerate() {
        let mut lowered = lower_expr(cg, arg)?;
        if let Some(param_ty) = param_tys.get(idx)
            && let (BasicValueEnum::IntValue(int_val), BasicTypeEnum::IntType(target_int_ty)) =
                (lowered, *param_ty)
        {
            let from_w = int_val.get_type().get_bit_width();
            let to_w = target_int_ty.get_bit_width();
            if from_w != to_w {
                lowered = if from_w > to_w {
                    cg.builder
                        .build_int_truncate(int_val, target_int_ty, "arg_trunc")
                        .map_err(|_| CodegenError::UnsupportedExpression("call"))?
                        .as_basic_value_enum()
                } else {
                    cg.builder
                        .build_int_z_extend(int_val, target_int_ty, "arg_zext")
                        .map_err(|_| CodegenError::UnsupportedExpression("call"))?
                        .as_basic_value_enum()
                };
            }
        }
        lowered_args.push(BasicMetadataValueEnum::from(lowered));
    }

    let call = cg
        .builder
        .build_call(function, &lowered_args, &format!("call_{resolved_name}"))
        .map_err(|_| CodegenError::UnsupportedExpression("call"))?;
    if let Some(value) = call.try_as_basic_value().left() {
        return Ok(value);
    }
    Ok(cg
        .context
        .ptr_type(AddressSpace::default())
        .const_null()
        .as_basic_value_enum())
}

#[cfg(feature = "llvm-backend")]
fn runtime_builtin_function_type<'ctx, 'm>(
    cg: &CodegenContext<'ctx, 'm>,
    name: &str,
) -> Option<inkwell::types::FunctionType<'ctx>> {
    let i32_ty = cg.context.i32_type();
    let void_ty = cg.context.void_type();

    let ty = match name {
        "syscall_exit" => void_ty.fn_type(&[i32_ty.into()], false),
        _ => return None,
    };
    Some(ty)
}

#[cfg(feature = "llvm-backend")]
fn lower_binary_op<'ctx, 'm>(
    cg: &CodegenContext<'ctx, 'm>,
    op: BinaryOpKind,
    lhs: &CheckedExpr,
    rhs: &CheckedExpr,
) -> Result<BasicValueEnum<'ctx>, CodegenError> {
    let lhs = lower_expr(cg, lhs)?;
    let rhs = lower_expr(cg, rhs)?;

    if let (BasicValueEnum::IntValue(l), BasicValueEnum::IntValue(r)) = (lhs, rhs) {
        let v = match op {
            BinaryOpKind::Add => cg.builder.build_int_add(l, r, "add"),
            BinaryOpKind::Sub => cg.builder.build_int_sub(l, r, "sub"),
            BinaryOpKind::Mul => cg.builder.build_int_mul(l, r, "mul"),
            BinaryOpKind::Div => cg.builder.build_int_signed_div(l, r, "div"),
            BinaryOpKind::Mod => cg.builder.build_int_signed_rem(l, r, "mod"),
            BinaryOpKind::Eq => cg
                .builder
                .build_int_compare(inkwell::IntPredicate::EQ, l, r, "eq"),
            BinaryOpKind::Neq => {
                cg.builder
                    .build_int_compare(inkwell::IntPredicate::NE, l, r, "ne")
            }
            BinaryOpKind::Lt => {
                cg.builder
                    .build_int_compare(inkwell::IntPredicate::SLT, l, r, "lt")
            }
            BinaryOpKind::Gt => {
                cg.builder
                    .build_int_compare(inkwell::IntPredicate::SGT, l, r, "gt")
            }
            BinaryOpKind::Le => {
                cg.builder
                    .build_int_compare(inkwell::IntPredicate::SLE, l, r, "le")
            }
            BinaryOpKind::Ge => {
                cg.builder
                    .build_int_compare(inkwell::IntPredicate::SGE, l, r, "ge")
            }
            BinaryOpKind::And => cg.builder.build_and(l, r, "and"),
            BinaryOpKind::Or => cg.builder.build_or(l, r, "or"),
        }
        .map_err(|_| CodegenError::UnsupportedExpression("binary_op"))?;
        return Ok(v.as_basic_value_enum());
    }

    if let (BasicValueEnum::FloatValue(l), BasicValueEnum::FloatValue(r)) = (lhs, rhs) {
        let v = match op {
            BinaryOpKind::Add => cg.builder.build_float_add(l, r, "fadd"),
            BinaryOpKind::Sub => cg.builder.build_float_sub(l, r, "fsub"),
            BinaryOpKind::Mul => cg.builder.build_float_mul(l, r, "fmul"),
            BinaryOpKind::Div => cg.builder.build_float_div(l, r, "fdiv"),
            BinaryOpKind::Mod => cg.builder.build_float_rem(l, r, "frem"),
            BinaryOpKind::Eq => {
                return cg
                    .builder
                    .build_float_compare(inkwell::FloatPredicate::OEQ, l, r, "feq")
                    .map(|v| v.as_basic_value_enum())
                    .map_err(|_| CodegenError::UnsupportedExpression("binary_op"));
            }
            BinaryOpKind::Neq => {
                return cg
                    .builder
                    .build_float_compare(inkwell::FloatPredicate::ONE, l, r, "fne")
                    .map(|v| v.as_basic_value_enum())
                    .map_err(|_| CodegenError::UnsupportedExpression("binary_op"));
            }
            BinaryOpKind::Lt => {
                return cg
                    .builder
                    .build_float_compare(inkwell::FloatPredicate::OLT, l, r, "flt")
                    .map(|v| v.as_basic_value_enum())
                    .map_err(|_| CodegenError::UnsupportedExpression("binary_op"));
            }
            BinaryOpKind::Gt => {
                return cg
                    .builder
                    .build_float_compare(inkwell::FloatPredicate::OGT, l, r, "fgt")
                    .map(|v| v.as_basic_value_enum())
                    .map_err(|_| CodegenError::UnsupportedExpression("binary_op"));
            }
            BinaryOpKind::Le => {
                return cg
                    .builder
                    .build_float_compare(inkwell::FloatPredicate::OLE, l, r, "fle")
                    .map(|v| v.as_basic_value_enum())
                    .map_err(|_| CodegenError::UnsupportedExpression("binary_op"));
            }
            BinaryOpKind::Ge => {
                return cg
                    .builder
                    .build_float_compare(inkwell::FloatPredicate::OGE, l, r, "fge")
                    .map(|v| v.as_basic_value_enum())
                    .map_err(|_| CodegenError::UnsupportedExpression("binary_op"));
            }
            BinaryOpKind::And | BinaryOpKind::Or => {
                return Err(CodegenError::UnsupportedExpression("binary_op"));
            }
        }
        .map_err(|_| CodegenError::UnsupportedExpression("binary_op"))?;
        return Ok(v.as_basic_value_enum());
    }

    Err(CodegenError::UnsupportedExpression("binary_op"))
}
