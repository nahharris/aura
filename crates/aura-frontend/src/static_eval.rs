use crate::ast::StaticValueExpr;

pub trait StaticSatisfies {
    fn is_compile_time_known(&self, expr: &StaticValueExpr) -> bool;
}

#[derive(Debug, Default, Clone, Copy)]
pub struct MinimalStaticChecker;

impl StaticSatisfies for MinimalStaticChecker {
    fn is_compile_time_known(&self, expr: &StaticValueExpr) -> bool {
        match expr {
            StaticValueExpr::Int(_) => true,
            StaticValueExpr::Float(_) => true,
            StaticValueExpr::Ident(_) => true,
            StaticValueExpr::Label(_) => true,
            StaticValueExpr::String(_) => true,
            StaticValueExpr::Char(_) => true,
        }
    }
}
