pub mod compile;
pub mod discover;
pub mod manifest;

use std::path::PathBuf;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProjectLayout {
    pub root: PathBuf,
    pub build_file: PathBuf,
    pub src_dir: PathBuf,
    pub vendor_dir: PathBuf,
    pub target_dir: PathBuf,
}
