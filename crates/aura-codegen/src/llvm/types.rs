use aura_typecheck::{Ty, TyId, TyInterner};

use super::error::CodegenError;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AuraValueType {
    Void,
    Int1,
    Int8,
    Int16,
    Int32,
    Int64,
    Int128,
    Float32,
    Float64,
    Pointer,
    Aggregate(TyId),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AuraFunctionType {
    pub params: Vec<AuraValueType>,
    pub ret: AuraValueType,
}

pub fn classify_type(types: &TyInterner, ty_id: TyId) -> Result<AuraValueType, CodegenError> {
    let ty = types
        .get(ty_id)
        .ok_or(CodegenError::InvalidTypeId(ty_id.0))?;

    match ty {
        Ty::Bool => Ok(AuraValueType::Int1),
        Ty::Int8 | Ty::UInt8 | Ty::Char => Ok(AuraValueType::Int8),
        Ty::Int16 | Ty::UInt16 => Ok(AuraValueType::Int16),
        Ty::Int32 | Ty::UInt32 => Ok(AuraValueType::Int32),
        Ty::Int64 | Ty::UInt64 | Ty::ISize | Ty::USize => Ok(AuraValueType::Int64),
        Ty::Int128 | Ty::UInt128 => Ok(AuraValueType::Int128),
        Ty::Float32 => Ok(AuraValueType::Float32),
        Ty::Float64 => Ok(AuraValueType::Float64),
        Ty::Void => Ok(AuraValueType::Void),
        Ty::Enum(_) => Ok(AuraValueType::Aggregate(ty_id)),
        Ty::Never
        | Ty::Any
        | Ty::Nominal(_)
        | Ty::List(_)
        | Ty::Dict { .. }
        | Ty::Set(_)
        | Ty::Array { .. }
        | Ty::Func { .. }
        | Ty::Macro { .. }
        | Ty::Tuple(_)
        | Ty::Struct(_)
        | Ty::Union(_)
        | Ty::GenericParam(_)
        | Ty::InferVar(_) => Ok(AuraValueType::Pointer),
    }
}

pub fn classify_function_type(
    types: &TyInterner,
    ty_id: TyId,
) -> Result<AuraFunctionType, CodegenError> {
    let ty = types
        .get(ty_id)
        .ok_or(CodegenError::InvalidTypeId(ty_id.0))?;
    let Ty::Func { params, ret } = ty else {
        return Err(CodegenError::UnsupportedType(format!(
            "expected function type, got {ty:?}"
        )));
    };

    let params = params
        .iter()
        .map(|param| classify_type(types, param.ty))
        .collect::<Result<Vec<_>, _>>()?;
    let ret = if matches!(types.get(*ret), Some(Ty::Never)) {
        AuraValueType::Void
    } else {
        classify_type(types, *ret)?
    };
    Ok(AuraFunctionType { params, ret })
}

#[cfg(feature = "llvm-backend")]
mod llvm_lowering {
    use aura_typecheck::{Ty, TyId, TyInterner};
    use inkwell::{
        AddressSpace,
        context::Context,
        types::{BasicMetadataTypeEnum, BasicType, BasicTypeEnum, FunctionType},
    };

    use super::{
        AuraFunctionType, AuraValueType, CodegenError, classify_function_type, classify_type,
    };

    impl AuraValueType {
        pub fn to_basic_type<'ctx>(
            self,
            context: &'ctx Context,
            types: &TyInterner,
        ) -> Result<BasicTypeEnum<'ctx>, CodegenError> {
            let ty = match self {
                AuraValueType::Int1 => context.bool_type().as_basic_type_enum(),
                AuraValueType::Int8 => context.i8_type().as_basic_type_enum(),
                AuraValueType::Int16 => context.i16_type().as_basic_type_enum(),
                AuraValueType::Int32 => context.i32_type().as_basic_type_enum(),
                AuraValueType::Int64 => context.i64_type().as_basic_type_enum(),
                AuraValueType::Int128 => context.i128_type().as_basic_type_enum(),
                AuraValueType::Float32 => context.f32_type().as_basic_type_enum(),
                AuraValueType::Float64 => context.f64_type().as_basic_type_enum(),
                AuraValueType::Pointer => context
                    .ptr_type(AddressSpace::default())
                    .as_basic_type_enum(),
                AuraValueType::Aggregate(ty_id) => enum_basic_type(context, types, ty_id)?,
                AuraValueType::Void => {
                    return Err(CodegenError::UnsupportedType(
                        "void cannot be lowered as a basic value type".to_string(),
                    ));
                }
            };
            Ok(ty)
        }

        pub fn to_metadata_type<'ctx>(
            self,
            context: &'ctx Context,
            types: &TyInterner,
        ) -> Result<BasicMetadataTypeEnum<'ctx>, CodegenError> {
            Ok(self.to_basic_type(context, types)?.into())
        }
    }

    impl AuraFunctionType {
        pub fn to_llvm_fn_type<'ctx>(
            &self,
            context: &'ctx Context,
            types: &TyInterner,
            is_var_arg: bool,
        ) -> Result<FunctionType<'ctx>, CodegenError> {
            let params = self
                .params
                .iter()
                .map(|ty| ty.to_metadata_type(context, types))
                .collect::<Result<Vec<_>, _>>()?;

            let fn_type = match self.ret {
                AuraValueType::Void => context.void_type().fn_type(&params, is_var_arg),
                _ => self
                    .ret
                    .to_basic_type(context, types)?
                    .fn_type(&params, is_var_arg),
            };
            Ok(fn_type)
        }
    }

    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub struct TypeLayout {
        pub size: u64,
        pub align: u64,
    }

    pub fn lower_basic_type<'ctx>(
        context: &'ctx Context,
        types: &TyInterner,
        ty_id: TyId,
    ) -> Result<BasicTypeEnum<'ctx>, CodegenError> {
        classify_type(types, ty_id)?.to_basic_type(context, types)
    }

    pub fn lower_function_type<'ctx>(
        context: &'ctx Context,
        types: &TyInterner,
        ty_id: TyId,
        is_var_arg: bool,
    ) -> Result<FunctionType<'ctx>, CodegenError> {
        classify_function_type(types, ty_id)?.to_llvm_fn_type(context, types, is_var_arg)
    }

    pub fn enum_basic_type<'ctx>(
        context: &'ctx Context,
        types: &TyInterner,
        ty_id: TyId,
    ) -> Result<BasicTypeEnum<'ctx>, CodegenError> {
        let Ty::Enum(variants) = types
            .get(ty_id)
            .ok_or(CodegenError::InvalidTypeId(ty_id.0))?
        else {
            return Err(CodegenError::UnsupportedType(format!(
                "expected enum type for aggregate lowering, got {:?}",
                types.get(ty_id)
            )));
        };

        let payload_layout = variants
            .iter()
            .filter_map(|variant: &(String, Option<TyId>)| {
                variant.1.map(|payload| type_layout(types, payload))
            })
            .collect::<Result<Vec<_>, _>>()?;
        let max_payload_size = payload_layout
            .iter()
            .map(|layout| layout.size)
            .max()
            .unwrap_or(0);
        let max_payload_align = payload_layout
            .iter()
            .map(|layout| layout.align)
            .max()
            .unwrap_or(1);
        let payload_field = payload_storage_type(context, max_payload_size, max_payload_align)?;
        Ok(context
            .struct_type(&[context.i32_type().into(), payload_field.into()], false)
            .as_basic_type_enum())
    }

    pub fn type_layout(types: &TyInterner, ty_id: TyId) -> Result<TypeLayout, CodegenError> {
        Ok(match classify_type(types, ty_id)? {
            AuraValueType::Void => TypeLayout { size: 0, align: 1 },
            AuraValueType::Int1 | AuraValueType::Int8 => TypeLayout { size: 1, align: 1 },
            AuraValueType::Int16 => TypeLayout { size: 2, align: 2 },
            AuraValueType::Int32 | AuraValueType::Float32 => TypeLayout { size: 4, align: 4 },
            AuraValueType::Int64 | AuraValueType::Float64 | AuraValueType::Pointer => {
                TypeLayout { size: 8, align: 8 }
            }
            AuraValueType::Int128 => TypeLayout {
                size: 16,
                align: 16,
            },
            AuraValueType::Aggregate(enum_ty) => {
                let Ty::Enum(variants) = types
                    .get(enum_ty)
                    .ok_or(CodegenError::InvalidTypeId(enum_ty.0))?
                else {
                    return Err(CodegenError::UnsupportedType(
                        "non-enum aggregate".to_string(),
                    ));
                };
                let payload_layout = variants
                    .iter()
                    .filter_map(|variant: &(String, Option<TyId>)| {
                        variant.1.map(|payload| type_layout(types, payload))
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                let max_payload_size = payload_layout
                    .iter()
                    .map(|layout| layout.size)
                    .max()
                    .unwrap_or(0);
                let max_payload_align = payload_layout
                    .iter()
                    .map(|layout| layout.align)
                    .max()
                    .unwrap_or(1);
                let payload_offset = align_to(4, max_payload_align.max(1));
                let size = align_to(payload_offset + max_payload_size, 4.max(max_payload_align));
                TypeLayout {
                    size,
                    align: 4.max(max_payload_align),
                }
            }
        })
    }

    fn payload_storage_type<'ctx>(
        context: &'ctx Context,
        size: u64,
        align: u64,
    ) -> Result<BasicTypeEnum<'ctx>, CodegenError> {
        if size == 0 {
            return Ok(context.i8_type().array_type(0).as_basic_type_enum());
        }

        let cell_align = align.max(1).next_power_of_two();
        let cell_ty = match cell_align {
            1 => context.i8_type().as_basic_type_enum(),
            2 => context.i16_type().as_basic_type_enum(),
            4 => context.i32_type().as_basic_type_enum(),
            8 => context.i64_type().as_basic_type_enum(),
            16 => context.i128_type().as_basic_type_enum(),
            other => {
                return Err(CodegenError::UnsupportedType(format!(
                    "enum payload alignment {other} is not supported"
                )));
            }
        };
        let cell_size = cell_align;
        let cells = size.div_ceil(cell_size) as u32;
        Ok(cell_ty.array_type(cells).as_basic_type_enum())
    }

    fn align_to(size: u64, align: u64) -> u64 {
        if align <= 1 {
            size
        } else {
            let rem = size % align;
            if rem == 0 { size } else { size + (align - rem) }
        }
    }
}

#[cfg(feature = "llvm-backend")]
pub use llvm_lowering::{enum_basic_type, lower_basic_type, lower_function_type, type_layout};

#[cfg(test)]
mod tests {
    use aura_typecheck::types::FuncParam;
    use aura_typecheck::{Ty, TyInterner};

    use super::{AuraValueType, classify_function_type, classify_type};

    #[test]
    fn classify_primitives_into_llvm_scalars() {
        let mut types = TyInterner::new();
        let bool_ty = types.intern(Ty::Bool);
        let i32_ty = types.intern(Ty::Int32);
        let f64_ty = types.intern(Ty::Float64);

        assert_eq!(
            classify_type(&types, bool_ty).expect("bool type"),
            AuraValueType::Int1
        );
        assert_eq!(
            classify_type(&types, i32_ty).expect("i32 type"),
            AuraValueType::Int32
        );
        assert_eq!(
            classify_type(&types, f64_ty).expect("f64 type"),
            AuraValueType::Float64
        );
    }

    #[test]
    fn classify_aggregate_like_types_as_pointers() {
        let mut types = TyInterner::new();
        let elem_ty = types.intern(Ty::Int32);
        let list_ty = types.intern(Ty::List(elem_ty));
        assert_eq!(
            classify_type(&types, list_ty).expect("list type"),
            AuraValueType::Pointer
        );
    }

    #[test]
    fn classify_enums_as_aggregate_values() {
        let mut types = TyInterner::new();
        let uint8 = types.intern(Ty::UInt8);
        let result_ty = types.intern(Ty::Enum(vec![
            ("ok".to_string(), None),
            ("err".to_string(), Some(uint8)),
        ]));

        assert_eq!(
            classify_type(&types, result_ty).expect("result type"),
            AuraValueType::Aggregate(result_ty)
        );
    }

    #[test]
    fn classify_function_type_maps_params_and_return() {
        let mut types = TyInterner::new();
        let bool_ty = types.intern(Ty::Bool);
        let i32_ty = types.intern(Ty::Int32);
        let f64_ty = types.intern(Ty::Float64);
        let fn_ty = types.intern(Ty::Func {
            params: vec![
                FuncParam::positional(bool_ty),
                FuncParam::positional(i32_ty),
            ],
            ret: f64_ty,
        });

        let lowered = classify_function_type(&types, fn_ty).expect("function type");
        assert_eq!(
            lowered.params,
            vec![AuraValueType::Int1, AuraValueType::Int32]
        );
        assert_eq!(lowered.ret, AuraValueType::Float64);
    }
}
