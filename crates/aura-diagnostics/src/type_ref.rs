use core::fmt;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum PrimitiveType {
    Int8,
    Int16,
    Int32,
    Int64,
    Int128,
    ISize,
    UInt8,
    UInt16,
    UInt32,
    UInt64,
    UInt128,
    USize,
    Float32,
    Float64,
    Bool,
    Char,
    Void,
    Never,
    Any,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct FuncParamRef {
    pub name: Option<String>,
    pub label: Option<String>,
    pub trailing: bool,
    pub ty: Box<TypeRef>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TypeRef {
    Primitive(PrimitiveType),
    InferVar(u32),
    GenericParam(String),
    Nominal(String),
    List(Box<TypeRef>),
    Dict {
        key: Box<TypeRef>,
        value: Box<TypeRef>,
    },
    Set(Box<TypeRef>),
    Array {
        item: Box<TypeRef>,
        size: u64,
    },
    Func {
        params: Vec<FuncParamRef>,
        ret: Box<TypeRef>,
    },
    Macro {
        params: Vec<FuncParamRef>,
        ret: Box<TypeRef>,
    },
    Tuple(Vec<TypeRef>),
    Struct(Vec<(String, TypeRef)>),
    Union(Vec<TypeRef>),
    Enum(Vec<(String, Option<TypeRef>)>),
    Unknown,
}

impl fmt::Display for PrimitiveType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let name = match self {
            Self::Int8 => "Int8",
            Self::Int16 => "Int16",
            Self::Int32 => "Int32",
            Self::Int64 => "Int64",
            Self::Int128 => "Int128",
            Self::ISize => "ISize",
            Self::UInt8 => "UInt8",
            Self::UInt16 => "UInt16",
            Self::UInt32 => "UInt32",
            Self::UInt64 => "UInt64",
            Self::UInt128 => "UInt128",
            Self::USize => "USize",
            Self::Float32 => "Float32",
            Self::Float64 => "Float64",
            Self::Bool => "Bool",
            Self::Char => "Char",
            Self::Void => "Void",
            Self::Never => "Never",
            Self::Any => "Any",
        };
        f.write_str(name)
    }
}

impl fmt::Display for TypeRef {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Primitive(p) => write!(f, "{p}"),
            Self::InferVar(v) => write!(f, "_t{v}"),
            Self::GenericParam(name) => f.write_str(name),
            Self::Nominal(name) => f.write_str(name),
            Self::List(item) => write!(f, "List[{item}]"),
            Self::Dict { key, value } => write!(f, "Dict[{key}, {value}]"),
            Self::Set(item) => write!(f, "Set[{item}]"),
            Self::Array { item, size } => write!(f, "Array[{item}, {size}]"),
            Self::Func { params, ret } => {
                let joined = params
                    .iter()
                    .map(format_func_param)
                    .collect::<Vec<_>>()
                    .join(", ");
                write!(f, "({joined}) -> {ret}")
            }
            Self::Macro { params, ret } => {
                let joined = params
                    .iter()
                    .map(format_func_param)
                    .collect::<Vec<_>>()
                    .join(", ");
                write!(f, "macro({joined}) -> {ret}")
            }
            Self::Tuple(items) => {
                let joined = items
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
                    .join(", ");
                write!(f, "({joined})")
            }
            Self::Struct(fields) => {
                let joined = fields
                    .iter()
                    .map(|(name, ty)| format!("{name}: {ty}"))
                    .collect::<Vec<_>>()
                    .join(", ");
                write!(f, "{{{joined}}}")
            }
            Self::Union(items) => {
                let joined = items
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
                    .join(" | ");
                write!(f, "union({joined})")
            }
            Self::Enum(variants) => {
                let joined = variants
                    .iter()
                    .map(|(name, ty)| match ty {
                        Some(inner) => format!("{name}: {inner}"),
                        None => name.clone(),
                    })
                    .collect::<Vec<_>>()
                    .join(", ");
                write!(f, "enum({joined})")
            }
            Self::Unknown => f.write_str("<unknown>"),
        }
    }
}

fn format_func_param(param: &FuncParamRef) -> String {
    let mut out = String::new();
    if let Some(label) = &param.label {
        out.push_str(label);
        out.push(' ');
    }
    if let Some(name) = &param.name {
        out.push_str(name);
        out.push_str(": ");
    }
    out.push_str(&param.ty.to_string());
    if param.trailing {
        out.push_str(" (trailing)");
    }
    out
}
