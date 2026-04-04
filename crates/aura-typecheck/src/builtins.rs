use std::collections::HashMap;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BuiltinTypeRef {
    Int32,
    Int64,
    ISize,
    UInt8,
    UInt32,
    UInt64,
    USize,
    Never,
    Ptr(Box<BuiltinTypeRef>),
    Slice(Box<BuiltinTypeRef>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BuiltinSignature {
    pub name: String,
    pub params: Vec<BuiltinTypeRef>,
    pub ret: BuiltinTypeRef,
}

#[derive(Debug, Clone)]
pub struct BuiltinRegistry {
    entries: HashMap<String, BuiltinSignature>,
}

impl BuiltinRegistry {
    pub fn with_prelude() -> Self {
        let mut entries = HashMap::new();
        let ptr_u8 = BuiltinTypeRef::Ptr(Box::new(BuiltinTypeRef::UInt8));
        let slice_u8 = BuiltinTypeRef::Slice(Box::new(BuiltinTypeRef::UInt8));
        let path_bytes = BuiltinTypeRef::Slice(Box::new(BuiltinTypeRef::UInt8));

        entries.insert(
            "rt_exit".to_string(),
            BuiltinSignature {
                name: "rt_exit".to_string(),
                params: vec![BuiltinTypeRef::Int32],
                ret: BuiltinTypeRef::Never,
            },
        );
        entries.insert(
            "rt_fd_read".to_string(),
            BuiltinSignature {
                name: "rt_fd_read".to_string(),
                params: vec![BuiltinTypeRef::Int32, slice_u8.clone()],
                ret: BuiltinTypeRef::ISize,
            },
        );
        entries.insert(
            "rt_fd_write".to_string(),
            BuiltinSignature {
                name: "rt_fd_write".to_string(),
                params: vec![BuiltinTypeRef::Int32, slice_u8.clone()],
                ret: BuiltinTypeRef::ISize,
            },
        );
        entries.insert(
            "rt_fd_open".to_string(),
            BuiltinSignature {
                name: "rt_fd_open".to_string(),
                params: vec![path_bytes, BuiltinTypeRef::UInt32, BuiltinTypeRef::UInt32],
                ret: BuiltinTypeRef::Int32,
            },
        );
        entries.insert(
            "rt_fd_close".to_string(),
            BuiltinSignature {
                name: "rt_fd_close".to_string(),
                params: vec![BuiltinTypeRef::Int32],
                ret: BuiltinTypeRef::Int32,
            },
        );
        entries.insert(
            "rt_fd_seek".to_string(),
            BuiltinSignature {
                name: "rt_fd_seek".to_string(),
                params: vec![
                    BuiltinTypeRef::Int32,
                    BuiltinTypeRef::Int64,
                    BuiltinTypeRef::UInt32,
                ],
                ret: BuiltinTypeRef::Int64,
            },
        );
        entries.insert(
            "rt_mem_map".to_string(),
            BuiltinSignature {
                name: "rt_mem_map".to_string(),
                params: vec![
                    BuiltinTypeRef::USize,
                    BuiltinTypeRef::UInt32,
                    BuiltinTypeRef::UInt32,
                ],
                ret: ptr_u8.clone(),
            },
        );
        entries.insert(
            "rt_mem_unmap".to_string(),
            BuiltinSignature {
                name: "rt_mem_unmap".to_string(),
                params: vec![ptr_u8.clone(), BuiltinTypeRef::USize],
                ret: BuiltinTypeRef::Int32,
            },
        );
        entries.insert(
            "rt_mem_protect".to_string(),
            BuiltinSignature {
                name: "rt_mem_protect".to_string(),
                params: vec![ptr_u8, BuiltinTypeRef::USize, BuiltinTypeRef::UInt32],
                ret: BuiltinTypeRef::Int32,
            },
        );
        entries.insert(
            "rt_time_now_ns".to_string(),
            BuiltinSignature {
                name: "rt_time_now_ns".to_string(),
                params: vec![],
                ret: BuiltinTypeRef::UInt64,
            },
        );
        entries.insert(
            "rt_random_fill".to_string(),
            BuiltinSignature {
                name: "rt_random_fill".to_string(),
                params: vec![slice_u8],
                ret: BuiltinTypeRef::Int32,
            },
        );
        Self { entries }
    }

    pub fn get(&self, name: &str) -> Option<&BuiltinSignature> {
        self.entries.get(name)
    }
}

impl Default for BuiltinRegistry {
    fn default() -> Self {
        Self::with_prelude()
    }
}

#[cfg(test)]
mod tests {
    use crate::builtins::BuiltinRegistry;

    #[test]
    fn prelude_registry_contains_expected_builtins() {
        let registry = BuiltinRegistry::with_prelude();
        assert!(registry.get("rt_fd_write").is_some());
        assert!(registry.get("rt_mem_map").is_some());
        assert!(registry.get("rt_random_fill").is_some());
        assert!(registry.get("missing_builtin").is_none());
    }
}
