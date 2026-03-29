use crate::types::Ty;

pub fn can_implicitly_widen(from: &Ty, to: &Ty) -> bool {
    if from == to {
        return true;
    }

    matches!(
        (from, to),
        (Ty::Int8, Ty::Int16)
            | (Ty::Int8, Ty::Int32)
            | (Ty::Int8, Ty::Int64)
            | (Ty::Int8, Ty::Int128)
            | (Ty::Int16, Ty::Int32)
            | (Ty::Int16, Ty::Int64)
            | (Ty::Int16, Ty::Int128)
            | (Ty::Int32, Ty::Int64)
            | (Ty::Int32, Ty::Int128)
            | (Ty::Int64, Ty::Int128)
            | (Ty::UInt8, Ty::UInt16)
            | (Ty::UInt8, Ty::UInt32)
            | (Ty::UInt8, Ty::UInt64)
            | (Ty::UInt8, Ty::UInt128)
            | (Ty::UInt16, Ty::UInt32)
            | (Ty::UInt16, Ty::UInt64)
            | (Ty::UInt16, Ty::UInt128)
            | (Ty::UInt32, Ty::UInt64)
            | (Ty::UInt32, Ty::UInt128)
            | (Ty::UInt64, Ty::UInt128)
            | (Ty::Float32, Ty::Float64)
    )
}

#[cfg(test)]
mod tests {
    use crate::numeric::can_implicitly_widen;
    use crate::types::Ty;

    #[test]
    fn numeric_widening_allows_safe_promotions() {
        assert!(can_implicitly_widen(&Ty::Int32, &Ty::Int64));
        assert!(can_implicitly_widen(&Ty::UInt16, &Ty::UInt64));
        assert!(can_implicitly_widen(&Ty::Float32, &Ty::Float64));
    }

    #[test]
    fn numeric_widening_rejects_cross_domain_or_narrowing() {
        assert!(!can_implicitly_widen(&Ty::Int64, &Ty::Int32));
        assert!(!can_implicitly_widen(&Ty::Int32, &Ty::UInt32));
        assert!(!can_implicitly_widen(&Ty::Int32, &Ty::Float64));
        assert!(!can_implicitly_widen(&Ty::Float64, &Ty::Float32));
    }
}
