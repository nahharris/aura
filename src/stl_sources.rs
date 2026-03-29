/// Embedded source for canonical `@stl/*` modules.
///
/// Keeping this table centralized avoids resolver drift between runtime module
/// loading and static type-signature extraction.
pub fn stl_source(path: &str) -> Option<&'static str> {
    match path {
        "@stl/core" => Some(include_str!("../stl/core.aura")),
        "@stl/io" => Some(include_str!("../stl/io.aura")),
        "@stl/string" => Some(include_str!("../stl/string.aura")),
        "@stl/list" => Some(include_str!("../stl/list.aura")),
        "@stl/collections" => Some(include_str!("../stl/collections.aura")),
        "@stl/bool" => Some(include_str!("../stl/bool.aura")),
        "@stl/option" => Some(include_str!("../stl/option.aura")),
        "@stl/result" => Some(include_str!("../stl/result.aura")),
        // Test-only cycle fixtures used by VM import-cycle tests.
        "@stl/cycle_a" => Some(include_str!("../stl/cycle_a.aura")),
        "@stl/cycle_b" => Some(include_str!("../stl/cycle_b.aura")),
        _ => None,
    }
}

/// Canonical STL modules that participate in static signature generation.
pub const STL_SIGNATURE_PATHS: [&str; 8] = [
    "@stl/core",
    "@stl/io",
    "@stl/string",
    "@stl/list",
    "@stl/collections",
    "@stl/bool",
    "@stl/option",
    "@stl/result",
];
