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
        Ty::Never
        | Ty::Any
        | Ty::Ptr(_)
        | Ty::Slice(_)
        | Ty::Nominal(_)
        | Ty::List(_)
        | Ty::Dict { .. }
        | Ty::Set(_)
        | Ty::Array { .. }
        | Ty::Func { .. }
        | Ty::Tuple(_)
        | Ty::Struct(_)
        | Ty::Union(_)
        | Ty::Enum(_)
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
        .map(|param| classify_type(types, *param))
        .collect::<Result<Vec<_>, _>>()?;
    let ret = classify_type(types, *ret)?;
    Ok(AuraFunctionType { params, ret })
}

#[cfg(feature = "llvm-backend")]
mod llvm_lowering {
    use inkwell::{
        AddressSpace,
        context::Context,
        types::{BasicMetadataTypeEnum, BasicType, BasicTypeEnum, FunctionType},
    };

    use super::{AuraFunctionType, AuraValueType, CodegenError};

    impl AuraValueType {
        pub fn to_basic_type<'ctx>(
            self,
            context: &'ctx Context,
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
        ) -> Result<BasicMetadataTypeEnum<'ctx>, CodegenError> {
            Ok(self.to_basic_type(context)?.into())
        }
    }

    impl AuraFunctionType {
        pub fn to_llvm_fn_type<'ctx>(
            &self,
            context: &'ctx Context,
            is_var_arg: bool,
        ) -> Result<FunctionType<'ctx>, CodegenError> {
            let params = self
                .params
                .iter()
                .map(|ty| ty.to_metadata_type(context))
                .collect::<Result<Vec<_>, _>>()?;

            let fn_type = match self.ret {
                AuraValueType::Void => context.void_type().fn_type(&params, is_var_arg),
                _ => self
                    .ret
                    .to_basic_type(context)?
                    .fn_type(&params, is_var_arg),
            };
            Ok(fn_type)
        }
    }
}

#[cfg(test)]
mod tests {
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
    fn classify_function_type_maps_params_and_return() {
        let mut types = TyInterner::new();
        let bool_ty = types.intern(Ty::Bool);
        let i32_ty = types.intern(Ty::Int32);
        let f64_ty = types.intern(Ty::Float64);
        let fn_ty = types.intern(Ty::Func {
            params: vec![bool_ty, i32_ty],
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
