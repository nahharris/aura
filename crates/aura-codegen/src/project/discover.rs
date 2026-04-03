use std::path::{Path, PathBuf};

use crate::project::ProjectLayout;

pub fn find_project_root(start: &Path) -> Option<PathBuf> {
    let mut current = if start.is_file() {
        start.parent().map(Path::to_path_buf)?
    } else {
        start.to_path_buf()
    };

    loop {
        if current.join("build.aura").is_file() {
            return Some(current);
        }
        match current.parent() {
            Some(parent) => current = parent.to_path_buf(),
            None => return None,
        }
    }
}

pub fn discover_layout(start: &Path) -> Option<ProjectLayout> {
    let root = find_project_root(start)?;
    Some(ProjectLayout {
        build_file: root.join("build.aura"),
        src_dir: root.join("src"),
        vendor_dir: root.join("vendor"),
        target_dir: root.join("target"),
        root,
    })
}

#[cfg(test)]
mod tests {
    use std::fs;
    use std::path::Path;
    use std::time::{SystemTime, UNIX_EPOCH};

    use super::{discover_layout, find_project_root};

    fn temp_test_dir(prefix: &str) -> std::path::PathBuf {
        let mut dir = std::env::temp_dir();
        let nanos = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("clock must be after unix epoch")
            .as_nanos();
        dir.push(format!("aura_codegen_{prefix}_{nanos}"));
        dir
    }

    fn create_file(path: &Path, content: &str) {
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent).expect("should create parent dirs");
        }
        fs::write(path, content).expect("should write test file");
    }

    #[test]
    fn finds_root_from_nested_directory() {
        let root = temp_test_dir("find_root_nested");
        let nested = root.join("src").join("app").join("feature");
        fs::create_dir_all(&nested).expect("should create nested dirs");
        create_file(&root.join("build.aura"), "def project = [];");

        let discovered = find_project_root(&nested).expect("must discover project root");
        assert_eq!(discovered, root);

        fs::remove_dir_all(discovered).expect("should cleanup temp project");
    }

    #[test]
    fn finds_root_from_file_path() {
        let root = temp_test_dir("find_root_file");
        let file = root.join("src").join("main.aura");
        create_file(&root.join("build.aura"), "def project = [];");
        create_file(&file, "def main = 1;");

        let discovered = find_project_root(&file).expect("must discover from file path");
        assert_eq!(discovered, root);

        fs::remove_dir_all(discovered).expect("should cleanup temp project");
    }

    #[test]
    fn returns_none_when_no_build_file_exists() {
        let root = temp_test_dir("find_root_none");
        let nested = root.join("src");
        fs::create_dir_all(&nested).expect("should create dir");

        let discovered = find_project_root(&nested);
        assert!(discovered.is_none());

        fs::remove_dir_all(root).expect("should cleanup temp dir");
    }

    #[test]
    fn discovers_standard_layout_paths() {
        let root = temp_test_dir("layout");
        create_file(&root.join("build.aura"), "def project = [];");

        let layout = discover_layout(&root).expect("must discover layout");
        assert_eq!(layout.root, root);
        assert_eq!(layout.build_file, root.join("build.aura"));
        assert_eq!(layout.src_dir, root.join("src"));
        assert_eq!(layout.vendor_dir, root.join("vendor"));
        assert_eq!(layout.target_dir, root.join("target"));

        fs::remove_dir_all(root).expect("should cleanup temp project");
    }
}
