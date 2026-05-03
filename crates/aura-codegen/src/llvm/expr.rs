#[cfg(feature = "llvm-backend")]
use aura_runtime_host::{RuntimeTypeRef, runtime_function};
#[cfg(feature = "llvm-backend")]
use aura_typecheck::Ty;
use aura_typecheck::checked_ir::CheckedExpr;
#[cfg(feature = "llvm-backend")]
use aura_typecheck::checked_ir::{BinaryOpKind, MemoryOpKind};
#[cfg(feature = "llvm-backend")]
use aura_typecheck::checked_ir::{CheckedCaseArm, CheckedEnumArm};

#[cfg(feature = "llvm-backend")]
use super::error::CodegenError;

#[cfg(feature = "llvm-backend")]
use inkwell::{
    AddressSpace,
    module::Linkage,
    types::BasicTypeEnum,
    values::{
        BasicMetadataValueEnum, BasicValue, BasicValueEnum, FunctionValue, IntValue, PointerValue,
    },
};

#[cfg(feature = "llvm-backend")]
use super::context::{CodegenContext, LoopTarget};
#[cfg(feature = "llvm-backend")]
use super::types::{
    AuraFunctionType, AuraValueType, aggregate_storage_type, lower_basic_type, type_layout,
    type_layout_id, type_trace_kind,
};

pub fn classify_expr_kind(expr: &CheckedExpr) -> &'static str {
    match expr {
        CheckedExpr::Ident(_) => "ident",
        CheckedExpr::Int(_) => "int",
        CheckedExpr::Float(_) => "float",
        CheckedExpr::Char(_) => "char",
        CheckedExpr::String(_) => "string",
        CheckedExpr::EnumCtor { .. } => "enum_ctor",
        CheckedExpr::Call { .. } => "call",
        CheckedExpr::MemoryOp { .. } => "memory_op",
        CheckedExpr::BinaryOp { .. } => "binary_op",
        CheckedExpr::DotIdent { .. } => "dot_ident",
        CheckedExpr::Tuple(_) => "tuple",
        CheckedExpr::Struct(_) => "struct",
        CheckedExpr::Block(_) => "block",
        CheckedExpr::LocalBind { .. } => "local_bind",
        CheckedExpr::AssignLocal { .. } => "assign_local",
        CheckedExpr::FieldAccess { .. } => "field_access",
        CheckedExpr::ForceUnwrap { .. } => "force_unwrap",
        CheckedExpr::Panic { .. } => "panic",
        CheckedExpr::Catch { .. } => "catch",
        CheckedExpr::AssignField { .. } => "assign_field",
        CheckedExpr::Closure { .. } => "closure",
        CheckedExpr::Any => "any",
        CheckedExpr::List(_) => "list",
        CheckedExpr::Dict(_) => "dict",
        CheckedExpr::MacroApply { .. } => "macro_apply",
        CheckedExpr::Label { .. } => "label",
        CheckedExpr::EnumMatch { .. } => "enum_match",
        CheckedExpr::MultiArm(_) => "multi_arm",
        CheckedExpr::If { .. } => "if",
        CheckedExpr::Cases { .. } => "cases",
        CheckedExpr::Loop { .. } => "loop",
        CheckedExpr::Return { .. } => "return",
        CheckedExpr::Break { .. } => "break",
        CheckedExpr::Continue { .. } => "continue",
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
        CheckedExpr::EnumCtor {
            enum_ty,
            variant_index,
            payload,
        } => lower_enum_ctor(cg, *enum_ty, *variant_index, payload.as_deref()),
        CheckedExpr::Tuple(items) if items.is_empty() => Ok(cg
            .context
            .ptr_type(AddressSpace::default())
            .const_null()
            .as_basic_value_enum()),
        CheckedExpr::Tuple(items) => lower_tuple_value(cg, items),
        CheckedExpr::Struct(fields) => lower_struct_value(cg, fields),
        CheckedExpr::Block(items) => {
            cg.push_local_scope();
            let mut last = cg
                .context
                .ptr_type(AddressSpace::default())
                .const_null()
                .as_basic_value_enum();
            for item in items {
                last = lower_expr(cg, item)?;
            }
            cg.pop_local_scope();
            Ok(last)
        }
        CheckedExpr::LocalBind { bindings, .. } => {
            let mut last = cg
                .context
                .ptr_type(AddressSpace::default())
                .const_null()
                .as_basic_value_enum();
            for binding in bindings {
                let lowered = lower_expr(cg, &binding.value)?;
                last = lowered;
                let Some(name) = binding.name.as_ref() else {
                    continue;
                };
                let slot = allocate_local_slot(cg, name, binding.ty)?;
                let stored = coerce_basic_value_for_slot(cg, lowered, binding.ty)?;
                cg.builder
                    .build_store(slot.ptr, stored)
                    .map_err(|_| CodegenError::UnsupportedExpression("local_bind"))?;
                cg.insert_local(name.clone(), slot);
            }
            Ok(last)
        }
        CheckedExpr::DotIdent { .. } => Err(CodegenError::UnsupportedExpression("dot_ident")),
        CheckedExpr::AssignLocal { name, value, ty } => {
            let slot = cg
                .lookup_local(name)
                .ok_or(CodegenError::UnsupportedExpression("assign_local"))?;
            let lowered = lower_expr(cg, value)?;
            let stored = coerce_basic_value_for_slot(cg, lowered, *ty)?;
            cg.builder
                .build_store(slot.ptr, stored)
                .map_err(|_| CodegenError::UnsupportedExpression("assign_local"))?;
            load_local_slot(cg, slot, name)
        }
        CheckedExpr::FieldAccess {
            object,
            object_ty,
            field_index,
            ty,
        } => {
            let field_ptr = field_ptr(cg, object, *object_ty, *field_index, "field_access")?;
            let field_ty = lower_basic_type(cg.context, &cg.checked.types, *ty)?;
            cg.builder
                .build_load(field_ty, field_ptr, "load_field")
                .map_err(|_| CodegenError::UnsupportedExpression("field_access"))
        }
        CheckedExpr::ForceUnwrap {
            expr,
            enum_ty,
            payload_ty,
            payload_variant_index,
        } => lower_force_unwrap(cg, expr, *enum_ty, *payload_ty, *payload_variant_index),
        CheckedExpr::Panic { message } => lower_panic_expr(cg, message),
        CheckedExpr::Catch {
            result_ty,
            expr,
            fallback,
        } => lower_catch_expr(cg, *result_ty, expr, fallback),
        CheckedExpr::AssignField {
            object,
            object_ty,
            field_index,
            value,
            ty,
        } => {
            let field_ptr = field_ptr(cg, object, *object_ty, *field_index, "assign_field")?;
            let lowered = lower_expr(cg, value)?;
            let stored = coerce_basic_value_for_slot(cg, lowered, *ty)?;
            cg.builder
                .build_store(field_ptr, stored)
                .map_err(|_| CodegenError::UnsupportedExpression("assign_field"))?;
            let field_ty = lower_basic_type(cg.context, &cg.checked.types, *ty)?;
            cg.builder
                .build_load(field_ty, field_ptr, "load_assigned_field")
                .map_err(|_| CodegenError::UnsupportedExpression("assign_field"))
        }
        CheckedExpr::Ident(name) => {
            if let Some(slot) = cg.lookup_local(name) {
                return load_local_slot(cg, slot, name);
            }
            let symbol_name = cg.resolve_symbol_name(name);
            if let Some(function) = cg.module.get_function(symbol_name) {
                return Ok(function
                    .as_global_value()
                    .as_pointer_value()
                    .as_basic_value_enum());
            }
            if let Some(global) = cg.module.get_global(&format!("{symbol_name}_global")) {
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
            if name == "true" {
                return Ok(cg
                    .context
                    .bool_type()
                    .const_int(1, false)
                    .as_basic_value_enum());
            }
            if name == "false" {
                return Ok(cg.context.bool_type().const_zero().as_basic_value_enum());
            }
            Err(CodegenError::UnsupportedExpression("ident"))
        }
        CheckedExpr::EnumMatch {
            scrutinee,
            enum_ty,
            result_ty,
            arms,
            default_arm,
        } => lower_enum_match(
            cg,
            scrutinee,
            *enum_ty,
            *result_ty,
            arms,
            default_arm.as_deref(),
        ),
        CheckedExpr::If {
            result_ty,
            condition,
            then_branch,
            else_branch,
        } => lower_if_expr(
            cg,
            *result_ty,
            condition,
            then_branch,
            else_branch.as_deref(),
        ),
        CheckedExpr::Cases { result_ty, arms } => lower_cases_expr(cg, *result_ty, arms),
        CheckedExpr::Loop {
            target,
            result_ty,
            condition,
            body,
        } => lower_loop_expr(cg, target, *result_ty, condition.as_deref(), body),
        CheckedExpr::Return { value, .. } => lower_return_expr(cg, value),
        CheckedExpr::Break { target, value } => lower_break_expr(cg, target, value.as_deref()),
        CheckedExpr::Continue { target } => lower_continue_expr(cg, target),
        CheckedExpr::Label { expr, .. } => lower_expr(cg, expr),
        CheckedExpr::Call { callee, args } => lower_call(cg, callee, args),
        CheckedExpr::MemoryOp {
            op,
            item_ty,
            result_ty,
            args,
        } => lower_memory_op(cg, *op, *item_ty, *result_ty, args),
        CheckedExpr::BinaryOp { op, lhs, rhs, .. } => lower_binary_op(cg, *op, lhs, rhs),
        _ => Err(CodegenError::UnsupportedExpression(classify_expr_kind(
            expr,
        ))),
    }
}

#[cfg(feature = "llvm-backend")]
fn allocate_local_slot<'ctx, 'm>(
    cg: &CodegenContext<'ctx, 'm>,
    name: &str,
    ty: aura_typecheck::TyId,
) -> Result<super::context::LocalSlot<'ctx>, CodegenError> {
    let basic_ty = lower_basic_type(cg.context, &cg.checked.types, ty)?;
    let ptr = cg
        .builder
        .build_alloca(basic_ty, &format!("local_{name}"))
        .map_err(|_| CodegenError::UnsupportedExpression("local_bind"))?;
    Ok(super::context::LocalSlot { ptr, ty })
}

#[cfg(feature = "llvm-backend")]
fn load_local_slot<'ctx, 'm>(
    cg: &CodegenContext<'ctx, 'm>,
    slot: super::context::LocalSlot<'ctx>,
    name: &str,
) -> Result<BasicValueEnum<'ctx>, CodegenError> {
    let basic_ty = lower_basic_type(cg.context, &cg.checked.types, slot.ty)?;
    cg.builder
        .build_load(basic_ty, slot.ptr, &format!("load_{name}"))
        .map_err(|_| CodegenError::UnsupportedExpression("ident"))
}

#[cfg(feature = "llvm-backend")]
fn lower_tuple_value<'ctx, 'm>(
    cg: &CodegenContext<'ctx, 'm>,
    items: &[CheckedExpr],
) -> Result<BasicValueEnum<'ctx>, CodegenError> {
    let values = items
        .iter()
        .map(|item| lower_expr(cg, item))
        .collect::<Result<Vec<_>, _>>()?;
    lower_aggregate_values(cg, &values, "tuple")
}

#[cfg(feature = "llvm-backend")]
fn lower_struct_value<'ctx, 'm>(
    cg: &CodegenContext<'ctx, 'm>,
    fields: &[(String, CheckedExpr)],
) -> Result<BasicValueEnum<'ctx>, CodegenError> {
    let values = fields
        .iter()
        .map(|(_, value)| lower_expr(cg, value))
        .collect::<Result<Vec<_>, _>>()?;
    lower_aggregate_values(cg, &values, "struct")
}

#[cfg(feature = "llvm-backend")]
fn lower_aggregate_values<'ctx, 'm>(
    cg: &CodegenContext<'ctx, 'm>,
    values: &[BasicValueEnum<'ctx>],
    label: &'static str,
) -> Result<BasicValueEnum<'ctx>, CodegenError> {
    let field_types = values
        .iter()
        .map(BasicValueEnum::get_type)
        .collect::<Vec<_>>();
    let storage_ty = cg.context.struct_type(&field_types, false);
    let slot = cg
        .builder
        .build_malloc(storage_ty, &format!("{label}_value"))
        .map_err(|_| CodegenError::UnsupportedExpression(label))?;
    for (index, value) in values.iter().enumerate() {
        let field_ptr = cg
            .builder
            .build_struct_gep(
                storage_ty,
                slot,
                index as u32,
                &format!("{label}_field_{index}"),
            )
            .map_err(|_| CodegenError::UnsupportedExpression(label))?;
        cg.builder
            .build_store(field_ptr, *value)
            .map_err(|_| CodegenError::UnsupportedExpression(label))?;
    }
    Ok(slot.as_basic_value_enum())
}

#[cfg(feature = "llvm-backend")]
fn field_ptr<'ctx, 'm>(
    cg: &CodegenContext<'ctx, 'm>,
    object: &CheckedExpr,
    object_ty: aura_typecheck::TyId,
    field_index: usize,
    label: &'static str,
) -> Result<PointerValue<'ctx>, CodegenError> {
    let object_value = lower_expr(cg, object)?;
    let BasicValueEnum::PointerValue(object_ptr) = object_value else {
        return Err(CodegenError::UnsupportedExpression(label));
    };
    let storage_ty = aggregate_storage_type(cg.context, &cg.checked.types, object_ty)?;
    cg.builder
        .build_struct_gep(
            storage_ty,
            object_ptr,
            field_index as u32,
            &format!("{label}_ptr"),
        )
        .map_err(|_| CodegenError::UnsupportedExpression(label))
}

#[cfg(feature = "llvm-backend")]
fn coerce_basic_value_for_slot<'ctx, 'm>(
    cg: &CodegenContext<'ctx, 'm>,
    value: BasicValueEnum<'ctx>,
    target_ty: aura_typecheck::TyId,
) -> Result<BasicValueEnum<'ctx>, CodegenError> {
    let target_basic_ty = lower_basic_type(cg.context, &cg.checked.types, target_ty)?;
    match (value, target_basic_ty) {
        (BasicValueEnum::IntValue(int_val), BasicTypeEnum::IntType(target_int_ty)) => {
            let from_w = int_val.get_type().get_bit_width();
            let to_w = target_int_ty.get_bit_width();
            if from_w == to_w {
                Ok(int_val.as_basic_value_enum())
            } else if from_w > to_w {
                cg.builder
                    .build_int_truncate(int_val, target_int_ty, "local_trunc")
                    .map(|v| v.as_basic_value_enum())
                    .map_err(|_| CodegenError::UnsupportedExpression("assign_local"))
            } else {
                cg.builder
                    .build_int_z_extend(int_val, target_int_ty, "local_zext")
                    .map(|v| v.as_basic_value_enum())
                    .map_err(|_| CodegenError::UnsupportedExpression("assign_local"))
            }
        }
        (value, _) => Ok(value),
    }
}

#[cfg(feature = "llvm-backend")]
fn memory_runtime_function<'ctx, 'm>(
    cg: &CodegenContext<'ctx, 'm>,
    name: &str,
) -> Result<FunctionValue<'ctx>, CodegenError> {
    if let Some(function) = cg.module.get_function(name) {
        return Ok(function);
    }

    let ptr = cg.context.ptr_type(AddressSpace::default());
    let usize_ty = cg.context.i64_type();
    let bool_ty = cg.context.bool_type();
    let fn_ty = match name {
        "raw_alloc_new" => ptr.fn_type(
            &[
                usize_ty.into(),
                usize_ty.into(),
                usize_ty.into(),
                usize_ty.into(),
                usize_ty.into(),
            ],
            false,
        ),
        "raw_alloc_slice" => ptr.fn_type(&[ptr.into()], false),
        "slice_get" => bool_ty.fn_type(&[ptr.into(), usize_ty.into(), ptr.into()], false),
        "slice_set" => bool_ty.fn_type(&[ptr.into(), usize_ty.into(), ptr.into()], false),
        "slice_ref_at" => ptr.fn_type(&[ptr.into(), usize_ty.into()], false),
        "ref_get" => cg
            .context
            .void_type()
            .fn_type(&[ptr.into(), ptr.into()], false),
        "ref_set" => cg
            .context
            .void_type()
            .fn_type(&[ptr.into(), ptr.into()], false),
        "gc_register_root" => cg
            .context
            .void_type()
            .fn_type(&[ptr.into(), usize_ty.into()], false),
        "gc_unregister_root" => cg.context.void_type().fn_type(&[ptr.into()], false),
        "gc_safepoint" => cg.context.void_type().fn_type(&[], false),
        _ => return Err(CodegenError::UnsupportedExpression("memory_op")),
    };

    Ok(cg.module.add_function(name, fn_ty, Some(Linkage::External)))
}

#[cfg(feature = "llvm-backend")]
fn call_memory_runtime<'ctx, 'm>(
    cg: &CodegenContext<'ctx, 'm>,
    name: &str,
    args: &[BasicValueEnum<'ctx>],
) -> Result<Option<BasicValueEnum<'ctx>>, CodegenError> {
    let function = memory_runtime_function(cg, name)?;
    let args = args
        .iter()
        .copied()
        .map(BasicMetadataValueEnum::from)
        .collect::<Vec<_>>();
    let call = cg
        .builder
        .build_call(function, &args, &format!("call_{name}"))
        .map_err(|_| CodegenError::UnsupportedExpression("memory_op"))?;
    Ok(call.try_as_basic_value().left())
}

#[cfg(feature = "llvm-backend")]
fn coerce_to_usize<'ctx, 'm>(
    cg: &CodegenContext<'ctx, 'm>,
    value: BasicValueEnum<'ctx>,
) -> Result<IntValue<'ctx>, CodegenError> {
    let BasicValueEnum::IntValue(int_val) = value else {
        return Err(CodegenError::UnsupportedExpression("memory_op"));
    };
    let usize_ty = cg.context.i64_type();
    let from_w = int_val.get_type().get_bit_width();
    let to_w = usize_ty.get_bit_width();
    if from_w == to_w {
        Ok(int_val)
    } else if from_w > to_w {
        cg.builder
            .build_int_truncate(int_val, usize_ty, "memory_usize_trunc")
            .map_err(|_| CodegenError::UnsupportedExpression("memory_op"))
    } else {
        cg.builder
            .build_int_z_extend(int_val, usize_ty, "memory_usize_zext")
            .map_err(|_| CodegenError::UnsupportedExpression("memory_op"))
    }
}

#[cfg(feature = "llvm-backend")]
fn build_option_from_payload<'ctx, 'm>(
    cg: &CodegenContext<'ctx, 'm>,
    option_ty: aura_typecheck::TyId,
    present: IntValue<'ctx>,
    payload_value: BasicValueEnum<'ctx>,
) -> Result<BasicValueEnum<'ctx>, CodegenError> {
    let current_block = cg
        .builder
        .get_insert_block()
        .ok_or(CodegenError::UnsupportedExpression("memory_op"))?;
    let function = current_block
        .get_parent()
        .ok_or(CodegenError::UnsupportedExpression("memory_op"))?;
    let option_basic_ty =
        lower_basic_type(cg.context, &cg.checked.types, option_ty)?.into_struct_type();
    let slot = cg
        .builder
        .build_alloca(option_basic_ty, "memory_option")
        .map_err(|_| CodegenError::UnsupportedExpression("memory_op"))?;
    cg.builder
        .build_store(slot, option_basic_ty.const_zero())
        .map_err(|_| CodegenError::UnsupportedExpression("memory_op"))?;

    let tag_ptr = cg
        .builder
        .build_struct_gep(option_basic_ty, slot, 0, "memory_option_tag_ptr")
        .map_err(|_| CodegenError::UnsupportedExpression("memory_op"))?;
    let tag = cg
        .builder
        .build_int_z_extend(present, cg.context.i32_type(), "memory_option_tag")
        .map_err(|_| CodegenError::UnsupportedExpression("memory_op"))?;
    cg.builder
        .build_store(tag_ptr, tag)
        .map_err(|_| CodegenError::UnsupportedExpression("memory_op"))?;

    let some_block = cg
        .context
        .append_basic_block(function, "memory_option_some");
    let merge_block = cg
        .context
        .append_basic_block(function, "memory_option_merge");
    cg.builder
        .build_conditional_branch(present, some_block, merge_block)
        .map_err(|_| CodegenError::UnsupportedExpression("memory_op"))?;

    cg.builder.position_at_end(some_block);
    let payload_ptr = cg
        .builder
        .build_struct_gep(option_basic_ty, slot, 1, "memory_option_payload_ptr")
        .map_err(|_| CodegenError::UnsupportedExpression("memory_op"))?;
    let typed_payload_ptr = cg
        .builder
        .build_bit_cast(
            payload_ptr,
            cg.context.ptr_type(AddressSpace::default()),
            "memory_option_payload_cast",
        )
        .map_err(|_| CodegenError::UnsupportedExpression("memory_op"))?
        .into_pointer_value();
    cg.builder
        .build_store(typed_payload_ptr, payload_value)
        .map_err(|_| CodegenError::UnsupportedExpression("memory_op"))?;
    cg.builder
        .build_unconditional_branch(merge_block)
        .map_err(|_| CodegenError::UnsupportedExpression("memory_op"))?;

    cg.builder.position_at_end(merge_block);
    cg.builder
        .build_load(option_basic_ty, slot, "memory_option_load")
        .map_err(|_| CodegenError::UnsupportedExpression("memory_op"))
}

#[cfg(feature = "llvm-backend")]
fn lower_memory_op<'ctx, 'm>(
    cg: &CodegenContext<'ctx, 'm>,
    op: MemoryOpKind,
    item_ty: aura_typecheck::TyId,
    result_ty: aura_typecheck::TyId,
    args: &[CheckedExpr],
) -> Result<BasicValueEnum<'ctx>, CodegenError> {
    match op {
        MemoryOpKind::RawAllocNew => {
            let count = args
                .first()
                .ok_or(CodegenError::UnsupportedExpression("memory_op"))
                .and_then(|arg| lower_expr(cg, arg))
                .and_then(|value| coerce_to_usize(cg, value))?;
            let layout = type_layout(&cg.checked.types, item_ty)?;
            let layout_id = type_layout_id(&cg.checked.types, item_ty);
            let trace_kind = type_trace_kind(&cg.checked.types, item_ty)?;
            let size = cg.context.i64_type().const_int(layout.size, false);
            let align = cg.context.i64_type().const_int(layout.align, false);
            let layout_id = cg.context.i64_type().const_int(layout_id, false);
            let trace_kind = cg.context.i64_type().const_int(trace_kind, false);
            call_memory_runtime(
                cg,
                "raw_alloc_new",
                &[
                    count.as_basic_value_enum(),
                    size.as_basic_value_enum(),
                    align.as_basic_value_enum(),
                    layout_id.as_basic_value_enum(),
                    trace_kind.as_basic_value_enum(),
                ],
            )?
            .ok_or(CodegenError::UnsupportedExpression("memory_op"))
        }
        MemoryOpKind::RawAllocSlice => {
            let alloc = args
                .first()
                .ok_or(CodegenError::UnsupportedExpression("memory_op"))
                .and_then(|arg| lower_expr(cg, arg))?;
            call_memory_runtime(cg, "raw_alloc_slice", &[alloc])?
                .ok_or(CodegenError::UnsupportedExpression("memory_op"))
        }
        MemoryOpKind::SliceGet => {
            let slice = args
                .first()
                .ok_or(CodegenError::UnsupportedExpression("memory_op"))
                .and_then(|arg| lower_expr(cg, arg))?;
            let index = args
                .get(1)
                .ok_or(CodegenError::UnsupportedExpression("memory_op"))
                .and_then(|arg| lower_expr(cg, arg))
                .and_then(|value| coerce_to_usize(cg, value))?;
            let item_basic_ty = lower_basic_type(cg.context, &cg.checked.types, item_ty)?;
            let out_slot = cg
                .builder
                .build_alloca(item_basic_ty, "slice_get_out")
                .map_err(|_| CodegenError::UnsupportedExpression("memory_op"))?;
            cg.builder
                .build_store(out_slot, item_basic_ty.const_zero())
                .map_err(|_| CodegenError::UnsupportedExpression("memory_op"))?;
            let ok = call_memory_runtime(
                cg,
                "slice_get",
                &[
                    slice,
                    index.as_basic_value_enum(),
                    out_slot.as_basic_value_enum(),
                ],
            )?
            .ok_or(CodegenError::UnsupportedExpression("memory_op"))?
            .into_int_value();
            let payload = cg
                .builder
                .build_load(item_basic_ty, out_slot, "slice_get_value")
                .map_err(|_| CodegenError::UnsupportedExpression("memory_op"))?;
            build_option_from_payload(cg, result_ty, ok, payload)
        }
        MemoryOpKind::SliceSet => {
            let slice = args
                .first()
                .ok_or(CodegenError::UnsupportedExpression("memory_op"))
                .and_then(|arg| lower_expr(cg, arg))?;
            let index = args
                .get(1)
                .ok_or(CodegenError::UnsupportedExpression("memory_op"))
                .and_then(|arg| lower_expr(cg, arg))
                .and_then(|value| coerce_to_usize(cg, value))?;
            let value = args
                .get(2)
                .ok_or(CodegenError::UnsupportedExpression("memory_op"))
                .and_then(|arg| lower_expr(cg, arg))?;
            let item_basic_ty = lower_basic_type(cg.context, &cg.checked.types, item_ty)?;
            let value_slot = cg
                .builder
                .build_alloca(item_basic_ty, "slice_set_value")
                .map_err(|_| CodegenError::UnsupportedExpression("memory_op"))?;
            let stored = coerce_basic_value_for_slot(cg, value, item_ty)?;
            cg.builder
                .build_store(value_slot, stored)
                .map_err(|_| CodegenError::UnsupportedExpression("memory_op"))?;
            call_memory_runtime(
                cg,
                "slice_set",
                &[
                    slice,
                    index.as_basic_value_enum(),
                    value_slot.as_basic_value_enum(),
                ],
            )?
            .ok_or(CodegenError::UnsupportedExpression("memory_op"))
        }
        MemoryOpKind::SliceRefAt => {
            let slice = args
                .first()
                .ok_or(CodegenError::UnsupportedExpression("memory_op"))
                .and_then(|arg| lower_expr(cg, arg))?;
            let index = args
                .get(1)
                .ok_or(CodegenError::UnsupportedExpression("memory_op"))
                .and_then(|arg| lower_expr(cg, arg))
                .and_then(|value| coerce_to_usize(cg, value))?;
            let reference =
                call_memory_runtime(cg, "slice_ref_at", &[slice, index.as_basic_value_enum()])?
                    .ok_or(CodegenError::UnsupportedExpression("memory_op"))?
                    .into_pointer_value();
            let present = cg
                .builder
                .build_is_not_null(reference, "slice_ref_at_present")
                .map_err(|_| CodegenError::UnsupportedExpression("memory_op"))?;
            build_option_from_payload(cg, result_ty, present, reference.as_basic_value_enum())
        }
        MemoryOpKind::RefGet => {
            let reference = args
                .first()
                .ok_or(CodegenError::UnsupportedExpression("memory_op"))
                .and_then(|arg| lower_expr(cg, arg))?;
            let item_basic_ty = lower_basic_type(cg.context, &cg.checked.types, item_ty)?;
            let out_slot = cg
                .builder
                .build_alloca(item_basic_ty, "ref_get_out")
                .map_err(|_| CodegenError::UnsupportedExpression("memory_op"))?;
            cg.builder
                .build_store(out_slot, item_basic_ty.const_zero())
                .map_err(|_| CodegenError::UnsupportedExpression("memory_op"))?;
            let _ =
                call_memory_runtime(cg, "ref_get", &[reference, out_slot.as_basic_value_enum()])?;
            cg.builder
                .build_load(item_basic_ty, out_slot, "ref_get_value")
                .map_err(|_| CodegenError::UnsupportedExpression("memory_op"))
        }
        MemoryOpKind::RefSet => {
            let reference = args
                .first()
                .ok_or(CodegenError::UnsupportedExpression("memory_op"))
                .and_then(|arg| lower_expr(cg, arg))?;
            let value = args
                .get(1)
                .ok_or(CodegenError::UnsupportedExpression("memory_op"))
                .and_then(|arg| lower_expr(cg, arg))?;
            let item_basic_ty = lower_basic_type(cg.context, &cg.checked.types, item_ty)?;
            let value_slot = cg
                .builder
                .build_alloca(item_basic_ty, "ref_set_value")
                .map_err(|_| CodegenError::UnsupportedExpression("memory_op"))?;
            let stored = coerce_basic_value_for_slot(cg, value, item_ty)?;
            cg.builder
                .build_store(value_slot, stored)
                .map_err(|_| CodegenError::UnsupportedExpression("memory_op"))?;
            let _ = call_memory_runtime(
                cg,
                "ref_set",
                &[reference, value_slot.as_basic_value_enum()],
            )?;
            Ok(cg
                .context
                .ptr_type(AddressSpace::default())
                .const_null()
                .as_basic_value_enum())
        }
        MemoryOpKind::GcRegisterRoot => {
            let slot = args
                .first()
                .ok_or(CodegenError::UnsupportedExpression("memory_op"))
                .and_then(|arg| lower_expr(cg, arg))?;
            let layout_id = match args.get(1) {
                Some(arg) => coerce_to_usize(cg, lower_expr(cg, arg)?)?.as_basic_value_enum(),
                None => cg.context.i64_type().const_zero().as_basic_value_enum(),
            };
            let _ = call_memory_runtime(cg, "gc_register_root", &[slot, layout_id])?;
            Ok(cg
                .context
                .ptr_type(AddressSpace::default())
                .const_null()
                .as_basic_value_enum())
        }
        MemoryOpKind::GcUnregisterRoot => {
            let slot = args
                .first()
                .ok_or(CodegenError::UnsupportedExpression("memory_op"))
                .and_then(|arg| lower_expr(cg, arg))?;
            let _ = call_memory_runtime(cg, "gc_unregister_root", &[slot])?;
            Ok(cg
                .context
                .ptr_type(AddressSpace::default())
                .const_null()
                .as_basic_value_enum())
        }
        MemoryOpKind::GcSafepoint => {
            let _ = call_memory_runtime(cg, "gc_safepoint", &[])?;
            Ok(cg
                .context
                .ptr_type(AddressSpace::default())
                .const_null()
                .as_basic_value_enum())
        }
    }
}

#[cfg(feature = "llvm-backend")]
fn lower_enum_ctor<'ctx, 'm>(
    cg: &CodegenContext<'ctx, 'm>,
    enum_ty: aura_typecheck::TyId,
    variant_index: usize,
    payload: Option<&CheckedExpr>,
) -> Result<BasicValueEnum<'ctx>, CodegenError> {
    let enum_basic_ty =
        lower_basic_type(cg.context, &cg.checked.types, enum_ty)?.into_struct_type();
    let slot = cg
        .builder
        .build_alloca(enum_basic_ty, "enum_ctor")
        .map_err(|_| CodegenError::UnsupportedExpression("enum_ctor"))?;
    cg.builder
        .build_store(slot, enum_basic_ty.const_zero())
        .map_err(|_| CodegenError::UnsupportedExpression("enum_ctor"))?;

    let tag_ptr = cg
        .builder
        .build_struct_gep(enum_basic_ty, slot, 0, "enum_tag_ptr")
        .map_err(|_| CodegenError::UnsupportedExpression("enum_ctor"))?;
    cg.builder
        .build_store(
            tag_ptr,
            cg.context.i32_type().const_int(variant_index as u64, false),
        )
        .map_err(|_| CodegenError::UnsupportedExpression("enum_ctor"))?;

    if let Some(payload_expr) = payload {
        let Ty::Enum(variants) = cg
            .checked
            .types
            .get(enum_ty)
            .ok_or(CodegenError::InvalidTypeId(enum_ty.0))?
        else {
            return Err(CodegenError::UnsupportedExpression("enum_ctor"));
        };
        if let Some(_payload_ty) = variants
            .get(variant_index)
            .and_then(|(_, payload)| *payload)
        {
            let payload_value = lower_expr(cg, payload_expr)?;
            let payload_ptr = cg
                .builder
                .build_struct_gep(enum_basic_ty, slot, 1, "enum_payload_ptr")
                .map_err(|_| CodegenError::UnsupportedExpression("enum_ctor"))?;
            let typed_payload_ptr = cg
                .builder
                .build_bit_cast(
                    payload_ptr,
                    cg.context.ptr_type(AddressSpace::default()),
                    "enum_payload_cast",
                )
                .map_err(|_| CodegenError::UnsupportedExpression("enum_ctor"))?
                .into_pointer_value();
            cg.builder
                .build_store(typed_payload_ptr, payload_value)
                .map_err(|_| CodegenError::UnsupportedExpression("enum_ctor"))?;
        }
    }

    cg.builder
        .build_load(enum_basic_ty, slot, "enum_ctor_load")
        .map_err(|_| CodegenError::UnsupportedExpression("enum_ctor"))
}

#[cfg(feature = "llvm-backend")]
fn lower_enum_match<'ctx, 'm>(
    cg: &CodegenContext<'ctx, 'm>,
    scrutinee: &CheckedExpr,
    enum_ty: aura_typecheck::TyId,
    result_ty: aura_typecheck::TyId,
    arms: &[CheckedEnumArm],
    default_arm: Option<&CheckedExpr>,
) -> Result<BasicValueEnum<'ctx>, CodegenError> {
    let current_block = cg
        .builder
        .get_insert_block()
        .ok_or(CodegenError::UnsupportedExpression("enum_match"))?;
    let function = current_block
        .get_parent()
        .ok_or(CodegenError::UnsupportedExpression("enum_match"))?;
    let enum_basic_ty =
        lower_basic_type(cg.context, &cg.checked.types, enum_ty)?.into_struct_type();
    let scrutinee_value = lower_expr(cg, scrutinee)?;
    let scrutinee_slot = cg
        .builder
        .build_alloca(enum_basic_ty, "enum_match_scrutinee")
        .map_err(|_| CodegenError::UnsupportedExpression("enum_match"))?;
    cg.builder
        .build_store(scrutinee_slot, scrutinee_value)
        .map_err(|_| CodegenError::UnsupportedExpression("enum_match"))?;

    let result_is_void = matches!(cg.checked.types.get(result_ty), Some(Ty::Void));
    let result_slot = if result_is_void {
        None
    } else {
        let result_basic_ty = lower_basic_type(cg.context, &cg.checked.types, result_ty)?;
        let slot = cg
            .builder
            .build_alloca(result_basic_ty, "enum_match_result")
            .map_err(|_| CodegenError::UnsupportedExpression("enum_match"))?;
        cg.builder
            .build_store(slot, result_basic_ty.const_zero())
            .map_err(|_| CodegenError::UnsupportedExpression("enum_match"))?;
        Some(slot)
    };

    let merge_block = cg.context.append_basic_block(function, "enum_match_merge");
    let mut next_block = current_block;
    let Ty::Enum(variants) = cg
        .checked
        .types
        .get(enum_ty)
        .ok_or(CodegenError::InvalidTypeId(enum_ty.0))?
    else {
        return Err(CodegenError::UnsupportedExpression("enum_match"));
    };

    for arm in arms {
        let arm_block = cg.context.append_basic_block(function, "enum_match_arm");
        let else_block = cg.context.append_basic_block(function, "enum_match_next");
        cg.builder.position_at_end(next_block);
        let tag = load_enum_tag(cg, scrutinee_slot, enum_basic_ty)?;
        let cond = cg
            .builder
            .build_int_compare(
                inkwell::IntPredicate::EQ,
                tag,
                cg.context
                    .i32_type()
                    .const_int(arm.variant_index as u64, false),
                "enum_match_tag_eq",
            )
            .map_err(|_| CodegenError::UnsupportedExpression("enum_match"))?;
        cg.builder
            .build_conditional_branch(cond, arm_block, else_block)
            .map_err(|_| CodegenError::UnsupportedExpression("enum_match"))?;

        cg.builder.position_at_end(arm_block);
        cg.push_local_scope();
        if let Some(name) = &arm.binding_name {
            if let Some(payload_ty) = variants
                .get(arm.variant_index)
                .and_then(|(_, payload)| *payload)
            {
                let payload_value =
                    load_enum_payload(cg, scrutinee_slot, enum_basic_ty, payload_ty)?;
                let slot = allocate_local_slot(cg, name, payload_ty)?;
                cg.builder
                    .build_store(slot.ptr, payload_value)
                    .map_err(|_| CodegenError::UnsupportedExpression("enum_match"))?;
                cg.insert_local(name.clone(), slot);
            }
        }
        if !arm.struct_bindings.is_empty() {
            if let Some(payload_ty) = variants
                .get(arm.variant_index)
                .and_then(|(_, payload)| *payload)
            {
                let payload_value =
                    load_enum_payload(cg, scrutinee_slot, enum_basic_ty, payload_ty)?;
                let BasicValueEnum::StructValue(payload_struct) = payload_value else {
                    return Err(CodegenError::UnsupportedExpression("enum_match"));
                };
                for binding in &arm.struct_bindings {
                    let field_value = cg
                        .builder
                        .build_extract_value(
                            payload_struct,
                            binding.field_index as u32,
                            &format!("enum_match_{}", binding.name),
                        )
                        .map_err(|_| CodegenError::UnsupportedExpression("enum_match"))?;
                    let slot = allocate_local_slot(cg, &binding.name, binding.ty)?;
                    let stored = coerce_basic_value_for_slot(cg, field_value, binding.ty)?;
                    cg.builder
                        .build_store(slot.ptr, stored)
                        .map_err(|_| CodegenError::UnsupportedExpression("enum_match"))?;
                    cg.insert_local(binding.name.clone(), slot);
                }
            }
        }
        let arm_value = lower_expr(cg, &arm.body)?;
        if let Some(result_slot) = result_slot {
            let stored = coerce_basic_value_for_slot(cg, arm_value, result_ty)?;
            cg.builder
                .build_store(result_slot, stored)
                .map_err(|_| CodegenError::UnsupportedExpression("enum_match"))?;
        }
        cg.builder
            .build_unconditional_branch(merge_block)
            .map_err(|_| CodegenError::UnsupportedExpression("enum_match"))?;
        cg.pop_local_scope();
        next_block = else_block;
    }

    cg.builder.position_at_end(next_block);
    if let Some(default_arm) = default_arm {
        let default_block = cg
            .context
            .append_basic_block(function, "enum_match_default");
        cg.builder
            .build_unconditional_branch(default_block)
            .map_err(|_| CodegenError::UnsupportedExpression("enum_match"))?;
        cg.builder.position_at_end(default_block);
        let default_value = lower_expr(cg, default_arm)?;
        if let Some(result_slot) = result_slot {
            let stored = coerce_basic_value_for_slot(cg, default_value, result_ty)?;
            cg.builder
                .build_store(result_slot, stored)
                .map_err(|_| CodegenError::UnsupportedExpression("enum_match"))?;
        }
        cg.builder
            .build_unconditional_branch(merge_block)
            .map_err(|_| CodegenError::UnsupportedExpression("enum_match"))?;
    } else {
        cg.builder
            .build_unconditional_branch(merge_block)
            .map_err(|_| CodegenError::UnsupportedExpression("enum_match"))?;
    }

    cg.builder.position_at_end(merge_block);
    if let Some(result_slot) = result_slot {
        let result_basic_ty = lower_basic_type(cg.context, &cg.checked.types, result_ty)?;
        return cg
            .builder
            .build_load(result_basic_ty, result_slot, "enum_match_result_load")
            .map_err(|_| CodegenError::UnsupportedExpression("enum_match"));
    }
    Ok(cg
        .context
        .ptr_type(AddressSpace::default())
        .const_null()
        .as_basic_value_enum())
}

#[cfg(feature = "llvm-backend")]
fn load_enum_tag<'ctx, 'm>(
    cg: &CodegenContext<'ctx, 'm>,
    enum_slot: inkwell::values::PointerValue<'ctx>,
    enum_basic_ty: inkwell::types::StructType<'ctx>,
) -> Result<inkwell::values::IntValue<'ctx>, CodegenError> {
    let tag_ptr = cg
        .builder
        .build_struct_gep(enum_basic_ty, enum_slot, 0, "enum_tag_ptr")
        .map_err(|_| CodegenError::UnsupportedExpression("enum_match"))?;
    cg.builder
        .build_load(cg.context.i32_type(), tag_ptr, "enum_tag_load")
        .map(|value| value.into_int_value())
        .map_err(|_| CodegenError::UnsupportedExpression("enum_match"))
}

#[cfg(feature = "llvm-backend")]
fn load_enum_payload<'ctx, 'm>(
    cg: &CodegenContext<'ctx, 'm>,
    enum_slot: inkwell::values::PointerValue<'ctx>,
    enum_basic_ty: inkwell::types::StructType<'ctx>,
    payload_ty: aura_typecheck::TyId,
) -> Result<BasicValueEnum<'ctx>, CodegenError> {
    let payload_basic_ty = lower_basic_type(cg.context, &cg.checked.types, payload_ty)?;
    let payload_ptr = cg
        .builder
        .build_struct_gep(enum_basic_ty, enum_slot, 1, "enum_payload_ptr")
        .map_err(|_| CodegenError::UnsupportedExpression("enum_match"))?;
    let typed_payload_ptr = cg
        .builder
        .build_bit_cast(
            payload_ptr,
            cg.context.ptr_type(AddressSpace::default()),
            "enum_payload_cast",
        )
        .map_err(|_| CodegenError::UnsupportedExpression("enum_match"))?
        .into_pointer_value();
    cg.builder
        .build_load(payload_basic_ty, typed_payload_ptr, "enum_payload_load")
        .map_err(|_| CodegenError::UnsupportedExpression("enum_match"))
}

#[cfg(feature = "llvm-backend")]
fn lower_force_unwrap<'ctx, 'm>(
    cg: &CodegenContext<'ctx, 'm>,
    expr: &CheckedExpr,
    enum_ty: aura_typecheck::TyId,
    payload_ty: aura_typecheck::TyId,
    payload_variant_index: usize,
) -> Result<BasicValueEnum<'ctx>, CodegenError> {
    let current_block = cg
        .builder
        .get_insert_block()
        .ok_or(CodegenError::UnsupportedExpression("force_unwrap"))?;
    let function = current_block
        .get_parent()
        .ok_or(CodegenError::UnsupportedExpression("force_unwrap"))?;
    let enum_basic_ty =
        lower_basic_type(cg.context, &cg.checked.types, enum_ty)?.into_struct_type();
    let payload_basic_ty = lower_basic_type(cg.context, &cg.checked.types, payload_ty)?;
    let value = lower_expr(cg, expr)?;
    let slot = cg
        .builder
        .build_alloca(enum_basic_ty, "force_unwrap_value")
        .map_err(|_| CodegenError::UnsupportedExpression("force_unwrap"))?;
    let result_slot = cg
        .builder
        .build_alloca(payload_basic_ty, "force_unwrap_result")
        .map_err(|_| CodegenError::UnsupportedExpression("force_unwrap"))?;
    cg.builder
        .build_store(slot, value)
        .map_err(|_| CodegenError::UnsupportedExpression("force_unwrap"))?;
    let tag = load_enum_tag(cg, slot, enum_basic_ty)?;
    let expected = cg
        .context
        .i32_type()
        .const_int(payload_variant_index as u64, false);
    let ok = cg
        .builder
        .build_int_compare(inkwell::IntPredicate::EQ, tag, expected, "force_unwrap_ok")
        .map_err(|_| CodegenError::UnsupportedExpression("force_unwrap"))?;
    let some_block = cg.context.append_basic_block(function, "force_unwrap_some");
    let null_block = cg.context.append_basic_block(function, "force_unwrap_null");
    let merge_block = cg.context.append_basic_block(function, "force_unwrap_merge");
    cg.builder
        .build_conditional_branch(ok, some_block, null_block)
        .map_err(|_| CodegenError::UnsupportedExpression("force_unwrap"))?;
    cg.builder.position_at_end(null_block);
    let panic_message = CheckedExpr::String("force unwrap failed".to_string());
    let _ = lower_panic_expr(cg, &panic_message)?;
    cg.builder
        .build_store(result_slot, payload_basic_ty.const_zero())
        .map_err(|_| CodegenError::UnsupportedExpression("force_unwrap"))?;
    cg.builder
        .build_unconditional_branch(merge_block)
        .map_err(|_| CodegenError::UnsupportedExpression("force_unwrap"))?;
    cg.builder.position_at_end(some_block);
    let payload = load_enum_payload(cg, slot, enum_basic_ty, payload_ty)?;
    cg.builder
        .build_store(result_slot, payload)
        .map_err(|_| CodegenError::UnsupportedExpression("force_unwrap"))?;
    cg.builder
        .build_unconditional_branch(merge_block)
        .map_err(|_| CodegenError::UnsupportedExpression("force_unwrap"))?;
    cg.builder.position_at_end(merge_block);
    cg.builder
        .build_load(payload_basic_ty, result_slot, "force_unwrap_result_load")
        .map_err(|_| CodegenError::UnsupportedExpression("force_unwrap"))
}

#[cfg(feature = "llvm-backend")]
fn lower_panic_expr<'ctx, 'm>(
    cg: &CodegenContext<'ctx, 'm>,
    message: &CheckedExpr,
) -> Result<BasicValueEnum<'ctx>, CodegenError> {
    let panic_fn = if let Some(function) = cg.module.get_function("aura_panic") {
        function
    } else {
        let Some(fn_ty) = runtime_builtin_function_type(cg, "aura_panic") else {
            return Err(CodegenError::UnsupportedExpression("panic"));
        };
        cg.module
            .add_function("aura_panic", fn_ty, Some(Linkage::External))
    };
    let msg_value = lower_expr(cg, message)?;
    let args = [BasicMetadataValueEnum::from(msg_value)];
    cg.builder
        .build_call(panic_fn, &args, "call_aura_panic")
        .map_err(|_| CodegenError::UnsupportedExpression("panic"))?;
    Ok(cg
        .context
        .ptr_type(AddressSpace::default())
        .const_null()
        .as_basic_value_enum())
}

#[cfg(feature = "llvm-backend")]
fn lower_catch_expr<'ctx, 'm>(
    cg: &CodegenContext<'ctx, 'm>,
    result_ty: aura_typecheck::TyId,
    expr: &CheckedExpr,
    fallback: &CheckedExpr,
) -> Result<BasicValueEnum<'ctx>, CodegenError> {
    let current_block = cg
        .builder
        .get_insert_block()
        .ok_or(CodegenError::UnsupportedExpression("catch"))?;
    let function = current_block
        .get_parent()
        .ok_or(CodegenError::UnsupportedExpression("catch"))?;
    let then_block = cg.context.append_basic_block(function, "catch_ok");
    let else_block = cg.context.append_basic_block(function, "catch_fallback");
    let merge_block = cg.context.append_basic_block(function, "catch_merge");

    let has_result = !matches!(cg.checked.types.get(result_ty), Some(Ty::Void | Ty::Never));
    let result_slot = if has_result {
        let result_basic_ty = lower_basic_type(cg.context, &cg.checked.types, result_ty)?;
        Some(
            cg.builder
                .build_alloca(result_basic_ty, "catch_result")
                .map_err(|_| CodegenError::UnsupportedExpression("catch"))?,
        )
    } else {
        None
    };

    let begin_fn = if let Some(function) = cg.module.get_function("aura_catch_begin") {
        function
    } else {
        let Some(fn_ty) = runtime_builtin_function_type(cg, "aura_catch_begin") else {
            return Err(CodegenError::UnsupportedExpression("catch"));
        };
        cg.module
            .add_function("aura_catch_begin", fn_ty, Some(Linkage::External))
    };
    cg.builder
        .build_call(begin_fn, &[], "call_aura_catch_begin")
        .map_err(|_| CodegenError::UnsupportedExpression("catch"))?;

    let try_value = lower_expr(cg, expr)?;

    let end_fn = if let Some(function) = cg.module.get_function("aura_catch_end") {
        function
    } else {
        let Some(fn_ty) = runtime_builtin_function_type(cg, "aura_catch_end") else {
            return Err(CodegenError::UnsupportedExpression("catch"));
        };
        cg.module
            .add_function("aura_catch_end", fn_ty, Some(Linkage::External))
    };
    let panicked = cg
        .builder
        .build_call(end_fn, &[], "call_aura_catch_end")
        .map_err(|_| CodegenError::UnsupportedExpression("catch"))?
        .try_as_basic_value()
        .left()
        .ok_or(CodegenError::UnsupportedExpression("catch"))?
        .into_int_value();
    let panicked_cond = cg
        .builder
        .build_int_compare(
            inkwell::IntPredicate::NE,
            panicked,
            panicked.get_type().const_zero(),
            "catch_panicked_cond",
        )
        .map_err(|_| CodegenError::UnsupportedExpression("catch"))?;
    cg.builder
        .build_conditional_branch(panicked_cond, else_block, then_block)
        .map_err(|_| CodegenError::UnsupportedExpression("catch"))?;

    cg.builder.position_at_end(then_block);
    if let Some(result_slot) = result_slot {
        let stored = coerce_basic_value_for_slot(cg, try_value, result_ty)?;
        cg.builder
            .build_store(result_slot, stored)
            .map_err(|_| CodegenError::UnsupportedExpression("catch"))?;
    }
    branch_to_if_open(cg, merge_block, "catch")?;

    cg.builder.position_at_end(else_block);
    let fallback_value = lower_expr(cg, fallback)?;
    if let Some(result_slot) = result_slot {
        let stored = coerce_basic_value_for_slot(cg, fallback_value, result_ty)?;
        cg.builder
            .build_store(result_slot, stored)
            .map_err(|_| CodegenError::UnsupportedExpression("catch"))?;
    }
    branch_to_if_open(cg, merge_block, "catch")?;

    cg.builder.position_at_end(merge_block);
    if let Some(result_slot) = result_slot {
        let result_basic_ty = lower_basic_type(cg.context, &cg.checked.types, result_ty)?;
        return cg
            .builder
            .build_load(result_basic_ty, result_slot, "catch_result_load")
            .map_err(|_| CodegenError::UnsupportedExpression("catch"));
    }
    Ok(cg
        .context
        .ptr_type(AddressSpace::default())
        .const_null()
        .as_basic_value_enum())
}

#[cfg(feature = "llvm-backend")]
fn lower_if_expr<'ctx, 'm>(
    cg: &CodegenContext<'ctx, 'm>,
    result_ty: aura_typecheck::TyId,
    condition: &CheckedExpr,
    then_branch: &CheckedExpr,
    else_branch: Option<&CheckedExpr>,
) -> Result<BasicValueEnum<'ctx>, CodegenError> {
    let current_block = cg
        .builder
        .get_insert_block()
        .ok_or(CodegenError::UnsupportedExpression("if"))?;
    let function = current_block
        .get_parent()
        .ok_or(CodegenError::UnsupportedExpression("if"))?;
    let then_block = cg.context.append_basic_block(function, "if_then");
    let else_block = cg.context.append_basic_block(function, "if_else");
    let merge_block = cg.context.append_basic_block(function, "if_merge");
    let cond = lower_expr(cg, condition)?.into_int_value();
    cg.builder
        .build_conditional_branch(cond, then_block, else_block)
        .map_err(|_| CodegenError::UnsupportedExpression("if"))?;

    let has_result = !matches!(cg.checked.types.get(result_ty), Some(Ty::Void | Ty::Never));
    let result_slot = if has_result {
        let result_basic_ty = lower_basic_type(cg.context, &cg.checked.types, result_ty)?;
        Some(
            cg.builder
                .build_alloca(result_basic_ty, "if_result")
                .map_err(|_| CodegenError::UnsupportedExpression("if"))?,
        )
    } else {
        None
    };

    cg.builder.position_at_end(then_block);
    let then_value = lower_expr(cg, then_branch)?;
    if let Some(result_slot) = result_slot {
        let stored = coerce_basic_value_for_slot(cg, then_value, result_ty)?;
        cg.builder
            .build_store(result_slot, stored)
            .map_err(|_| CodegenError::UnsupportedExpression("if"))?;
    }
    branch_to_if_open(cg, merge_block, "if")?;

    cg.builder.position_at_end(else_block);
    if let Some(else_branch) = else_branch {
        let else_value = lower_expr(cg, else_branch)?;
        if let Some(result_slot) = result_slot {
            let stored = coerce_basic_value_for_slot(cg, else_value, result_ty)?;
            cg.builder
                .build_store(result_slot, stored)
                .map_err(|_| CodegenError::UnsupportedExpression("if"))?;
        }
    }
    branch_to_if_open(cg, merge_block, "if")?;

    cg.builder.position_at_end(merge_block);
    if let Some(result_slot) = result_slot {
        let result_basic_ty = lower_basic_type(cg.context, &cg.checked.types, result_ty)?;
        return cg
            .builder
            .build_load(result_basic_ty, result_slot, "if_result_load")
            .map_err(|_| CodegenError::UnsupportedExpression("if"));
    }
    Ok(cg
        .context
        .ptr_type(AddressSpace::default())
        .const_null()
        .as_basic_value_enum())
}

#[cfg(feature = "llvm-backend")]
fn branch_to_if_open<'ctx, 'm>(
    cg: &CodegenContext<'ctx, 'm>,
    target: inkwell::basic_block::BasicBlock<'ctx>,
    context: &'static str,
) -> Result<(), CodegenError> {
    let Some(block) = cg.builder.get_insert_block() else {
        return Err(CodegenError::UnsupportedExpression(context));
    };
    if block.get_terminator().is_none() {
        cg.builder
            .build_unconditional_branch(target)
            .map_err(|_| CodegenError::UnsupportedExpression(context))?;
    }
    Ok(())
}

#[cfg(feature = "llvm-backend")]
fn lower_cases_expr<'ctx, 'm>(
    cg: &CodegenContext<'ctx, 'm>,
    result_ty: aura_typecheck::TyId,
    arms: &[CheckedCaseArm],
) -> Result<BasicValueEnum<'ctx>, CodegenError> {
    let current_block = cg
        .builder
        .get_insert_block()
        .ok_or(CodegenError::UnsupportedExpression("cases"))?;
    let function = current_block
        .get_parent()
        .ok_or(CodegenError::UnsupportedExpression("cases"))?;
    let merge_block = cg.context.append_basic_block(function, "cases_merge");
    let has_result = !matches!(cg.checked.types.get(result_ty), Some(Ty::Void | Ty::Never));
    let result_slot = if has_result {
        let result_basic_ty = lower_basic_type(cg.context, &cg.checked.types, result_ty)?;
        Some(
            cg.builder
                .build_alloca(result_basic_ty, "cases_result")
                .map_err(|_| CodegenError::UnsupportedExpression("cases"))?,
        )
    } else {
        None
    };

    let mut next_block = current_block;
    for arm in arms {
        let arm_block = cg.context.append_basic_block(function, "cases_arm");
        let else_block = cg.context.append_basic_block(function, "cases_next");
        cg.builder.position_at_end(next_block);
        let guard = lower_expr(cg, &arm.guard)?.into_int_value();
        cg.builder
            .build_conditional_branch(guard, arm_block, else_block)
            .map_err(|_| CodegenError::UnsupportedExpression("cases"))?;

        cg.builder.position_at_end(arm_block);
        let arm_value = lower_expr(cg, &arm.body)?;
        if let Some(result_slot) = result_slot {
            let stored = coerce_basic_value_for_slot(cg, arm_value, result_ty)?;
            cg.builder
                .build_store(result_slot, stored)
                .map_err(|_| CodegenError::UnsupportedExpression("cases"))?;
        }
        cg.builder
            .build_unconditional_branch(merge_block)
            .map_err(|_| CodegenError::UnsupportedExpression("cases"))?;
        next_block = else_block;
    }

    cg.builder.position_at_end(next_block);
    cg.builder
        .build_unreachable()
        .map_err(|_| CodegenError::UnsupportedExpression("cases"))?;
    cg.builder.position_at_end(merge_block);
    if let Some(result_slot) = result_slot {
        let result_basic_ty = lower_basic_type(cg.context, &cg.checked.types, result_ty)?;
        return cg
            .builder
            .build_load(result_basic_ty, result_slot, "cases_result_load")
            .map_err(|_| CodegenError::UnsupportedExpression("cases"));
    }
    Ok(cg
        .context
        .ptr_type(AddressSpace::default())
        .const_null()
        .as_basic_value_enum())
}

#[cfg(feature = "llvm-backend")]
fn lower_loop_expr<'ctx, 'm>(
    cg: &CodegenContext<'ctx, 'm>,
    target: &str,
    result_ty: aura_typecheck::TyId,
    condition: Option<&CheckedExpr>,
    body: &CheckedExpr,
) -> Result<BasicValueEnum<'ctx>, CodegenError> {
    let current_block = cg
        .builder
        .get_insert_block()
        .ok_or(CodegenError::UnsupportedExpression("loop"))?;
    let function = current_block
        .get_parent()
        .ok_or(CodegenError::UnsupportedExpression("loop"))?;
    let cond_block = cg.context.append_basic_block(function, "loop_cond");
    let body_block = cg.context.append_basic_block(function, "loop_body");
    let break_block = cg.context.append_basic_block(function, "loop_break");

    let has_result = !matches!(cg.checked.types.get(result_ty), Some(Ty::Void | Ty::Never));
    let result_slot = if has_result {
        let result_basic_ty = lower_basic_type(cg.context, &cg.checked.types, result_ty)?;
        Some(
            cg.builder
                .build_alloca(result_basic_ty, "loop_result")
                .map_err(|_| CodegenError::UnsupportedExpression("loop"))?,
        )
    } else {
        None
    };

    cg.builder
        .build_unconditional_branch(cond_block)
        .map_err(|_| CodegenError::UnsupportedExpression("loop"))?;

    cg.push_loop_target(
        target.to_string(),
        LoopTarget {
            continue_block: cond_block,
            break_block,
            result_slot,
            result_ty,
        },
    );

    cg.builder.position_at_end(cond_block);
    if let Some(condition) = condition {
        let cond = lower_expr(cg, condition)?.into_int_value();
        cg.builder
            .build_conditional_branch(cond, body_block, break_block)
            .map_err(|_| CodegenError::UnsupportedExpression("loop"))?;
    } else {
        cg.builder
            .build_unconditional_branch(body_block)
            .map_err(|_| CodegenError::UnsupportedExpression("loop"))?;
    }

    cg.builder.position_at_end(body_block);
    let _ = lower_expr(cg, body)?;
    cg.builder
        .build_unconditional_branch(cond_block)
        .map_err(|_| CodegenError::UnsupportedExpression("loop"))?;

    cg.pop_loop_target();
    cg.builder.position_at_end(break_block);
    if let Some(result_slot) = result_slot {
        let result_basic_ty = lower_basic_type(cg.context, &cg.checked.types, result_ty)?;
        return cg
            .builder
            .build_load(result_basic_ty, result_slot, "loop_result_load")
            .map_err(|_| CodegenError::UnsupportedExpression("loop"));
    }
    Ok(cg
        .context
        .ptr_type(AddressSpace::default())
        .const_null()
        .as_basic_value_enum())
}

#[cfg(feature = "llvm-backend")]
fn lower_return_expr<'ctx, 'm>(
    cg: &CodegenContext<'ctx, 'm>,
    value: &CheckedExpr,
) -> Result<BasicValueEnum<'ctx>, CodegenError> {
    let lowered = lower_expr(cg, value)?;
    let current_block = cg
        .builder
        .get_insert_block()
        .ok_or(CodegenError::UnsupportedExpression("return"))?;
    let function = current_block
        .get_parent()
        .ok_or(CodegenError::UnsupportedExpression("return"))?;
    if function.get_type().get_return_type().is_some() {
        cg.builder
            .build_return(Some(&lowered))
            .map_err(|_| CodegenError::UnsupportedExpression("return"))?;
    } else {
        cg.builder
            .build_return(None)
            .map_err(|_| CodegenError::UnsupportedExpression("return"))?;
    }
    position_after_terminator(cg, "after_return")?;
    Ok(cg
        .context
        .ptr_type(AddressSpace::default())
        .const_null()
        .as_basic_value_enum())
}

#[cfg(feature = "llvm-backend")]
fn lower_break_expr<'ctx, 'm>(
    cg: &CodegenContext<'ctx, 'm>,
    target: &str,
    value: Option<&CheckedExpr>,
) -> Result<BasicValueEnum<'ctx>, CodegenError> {
    let loop_target = cg
        .lookup_loop_target(target)
        .ok_or(CodegenError::UnsupportedExpression("break"))?;
    if let (Some(value), Some(result_slot)) = (value, loop_target.result_slot) {
        let lowered = lower_expr(cg, value)?;
        let stored = coerce_basic_value_for_slot(cg, lowered, loop_target.result_ty)?;
        cg.builder
            .build_store(result_slot, stored)
            .map_err(|_| CodegenError::UnsupportedExpression("break"))?;
    }
    cg.builder
        .build_unconditional_branch(loop_target.break_block)
        .map_err(|_| CodegenError::UnsupportedExpression("break"))?;
    position_after_terminator(cg, "after_break")?;
    Ok(cg
        .context
        .ptr_type(AddressSpace::default())
        .const_null()
        .as_basic_value_enum())
}

#[cfg(feature = "llvm-backend")]
fn lower_continue_expr<'ctx, 'm>(
    cg: &CodegenContext<'ctx, 'm>,
    target: &str,
) -> Result<BasicValueEnum<'ctx>, CodegenError> {
    let loop_target = cg
        .lookup_loop_target(target)
        .ok_or(CodegenError::UnsupportedExpression("continue"))?;
    cg.builder
        .build_unconditional_branch(loop_target.continue_block)
        .map_err(|_| CodegenError::UnsupportedExpression("continue"))?;
    position_after_terminator(cg, "after_continue")?;
    Ok(cg
        .context
        .ptr_type(AddressSpace::default())
        .const_null()
        .as_basic_value_enum())
}

#[cfg(feature = "llvm-backend")]
fn position_after_terminator<'ctx, 'm>(
    cg: &CodegenContext<'ctx, 'm>,
    name: &'static str,
) -> Result<(), CodegenError> {
    let current_block = cg
        .builder
        .get_insert_block()
        .ok_or(CodegenError::UnsupportedExpression(name))?;
    let function = current_block
        .get_parent()
        .ok_or(CodegenError::UnsupportedExpression(name))?;
    let next = cg.context.append_basic_block(function, name);
    cg.builder.position_at_end(next);
    Ok(())
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
    let resolved_name = cg.resolve_symbol_name(name);

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
        if let Some(param_ty) = param_tys.get(idx) {
            if let (BasicValueEnum::IntValue(int_val), BasicTypeEnum::IntType(target_int_ty)) =
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
    let abi = runtime_function(name)?;
    AuraFunctionType {
        params: abi.params.iter().map(runtime_value_type).collect(),
        ret: runtime_value_type(&abi.ret),
    }
    .to_llvm_fn_type(cg.context, &cg.checked.types, false)
    .ok()
}

#[cfg(feature = "llvm-backend")]
fn runtime_value_type(ty: &RuntimeTypeRef) -> AuraValueType {
    match ty {
        RuntimeTypeRef::Int32 => AuraValueType::Int32,
        RuntimeTypeRef::ISize | RuntimeTypeRef::USize => AuraValueType::Int64,
        RuntimeTypeRef::UInt8 => AuraValueType::Int8,
        RuntimeTypeRef::Void | RuntimeTypeRef::Never => AuraValueType::Void,
        RuntimeTypeRef::Bytes | RuntimeTypeRef::String => AuraValueType::Pointer,
    }
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
