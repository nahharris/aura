pub mod project;

pub fn backend_name() -> &'static str {
    "aura-codegen"
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn crate_is_wired_in_workspace() {
        assert_eq!(backend_name(), "aura-codegen");
    }
}
