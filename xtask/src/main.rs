mod docs;

use std::env;
use std::fs;
use std::fs::File;
use std::io::{BufReader, BufWriter, Write};
use std::path::{Path, PathBuf};
use std::process::Command;

use anyhow::{Context, Result, bail};
use clap::{Parser, Subcommand};
use docs::DocsCommands;
use reqwest::blocking::Client;
use tar::Archive;
use xshell::{Shell, cmd};
use xz2::read::XzDecoder;

const LLVM_VERSION: &str = "18.1.8";
const LLVM_MAJOR: &str = "18";

#[derive(Parser, Debug)]
#[command(name = "cargo xtask")]
#[command(about = "Aura project automation tasks", long_about = None)]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand, Debug)]
enum Commands {
    Dev {
        #[command(subcommand)]
        command: DevCommands,
    },
    Docs {
        #[command(subcommand)]
        command: DocsCommands,
    },
    #[command(name = "llvm")]
    Llvm {
        #[command(subcommand)]
        command: LlvmCommands,
    },
}

#[derive(Subcommand, Debug)]
enum DevCommands {
    Check,
    Build,
    Test,
    Lint,
    Fmt,
    /// Fail if the workspace is not rustfmt-clean (does not modify files).
    FmtCheck,
    /// Full CI parity: fmt check, clippy, tests, docs check, then LLVM doctor + clippy + tests.
    Ci,
    Qa,
}

#[derive(Subcommand, Debug)]
enum LlvmCommands {
    Setup,
    Doctor,
    /// LLVM doctor, clippy, and tests (expects toolchain already installed; use `llvm setup` first on a fresh machine).
    Ci,
    Check,
    Build,
    Test,
    Clippy,
    Run {
        #[arg(trailing_var_arg = true, allow_hyphen_values = true)]
        args: Vec<String>,
    },
    Cargo {
        #[arg(trailing_var_arg = true, allow_hyphen_values = true)]
        args: Vec<String>,
    },
    Clean,
}

fn main() -> Result<()> {
    let cli = Cli::parse();
    let sh = Shell::new()?;
    let root = workspace_root()?;
    sh.change_dir(&root);

    match cli.command {
        Commands::Dev { command } => match command {
            DevCommands::Check => dev_check(&sh),
            DevCommands::Build => dev_build(&sh),
            DevCommands::Test => dev_test(&sh),
            DevCommands::Lint => dev_lint(&sh),
            DevCommands::Fmt => dev_fmt(&sh),
            DevCommands::FmtCheck => dev_fmt_check(&sh),
            DevCommands::Ci => dev_ci(&sh, &root),
            DevCommands::Qa => dev_qa(&sh),
        },
        Commands::Docs { command } => docs::run(command, &root),
        Commands::Llvm { command } => match command {
            LlvmCommands::Setup => llvm_setup(&sh),
            LlvmCommands::Doctor => llvm_doctor(&sh),
            LlvmCommands::Ci => llvm_ci(&sh),
            LlvmCommands::Check => llvm_check(&sh),
            LlvmCommands::Build => llvm_build(&sh),
            LlvmCommands::Test => llvm_test(&sh),
            LlvmCommands::Clippy => llvm_clippy(&sh),
            LlvmCommands::Run { args } => llvm_run(&args),
            LlvmCommands::Cargo { args } => llvm_cargo(&args),
            LlvmCommands::Clean => llvm_clean(),
        },
    }
}

fn dev_check(sh: &Shell) -> Result<()> {
    cmd!(sh, "cargo check --workspace").run()?;
    Ok(())
}

fn dev_build(sh: &Shell) -> Result<()> {
    cmd!(sh, "cargo build --workspace").run()?;
    Ok(())
}

fn dev_test(sh: &Shell) -> Result<()> {
    cmd!(sh, "cargo test --workspace").run()?;
    Ok(())
}

fn dev_lint(sh: &Shell) -> Result<()> {
    cmd!(sh, "cargo clippy --workspace --all-targets -- -D warnings").run()?;
    Ok(())
}

fn dev_fmt(sh: &Shell) -> Result<()> {
    cmd!(sh, "cargo fmt --all").run()?;
    Ok(())
}

fn dev_fmt_check(sh: &Shell) -> Result<()> {
    cmd!(sh, "cargo fmt --all -- --check").run()?;
    Ok(())
}

fn dev_ci(sh: &Shell, root: &Path) -> Result<()> {
    dev_fmt_check(sh)?;
    dev_lint(sh)?;
    dev_test(sh)?;
    docs::run(DocsCommands::Check, root)?;
    llvm_ci(sh)?;
    Ok(())
}

fn llvm_ci(sh: &Shell) -> Result<()> {
    llvm_doctor(sh)?;
    llvm_clippy(sh)?;
    llvm_test(sh)?;
    Ok(())
}

fn dev_qa(sh: &Shell) -> Result<()> {
    dev_fmt(sh)?;
    dev_lint(sh)?;
    dev_test(sh)
}

fn workspace_root() -> Result<PathBuf> {
    let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    manifest_dir
        .parent()
        .map(Path::to_path_buf)
        .context("failed to resolve workspace root from xtask crate path")
}

fn llvm_setup(sh: &Shell) -> Result<()> {
    let paths = LlvmPaths::new();
    ensure_llvm_toolchain(&paths)?;
    validate_install(&paths)?;
    let prefix = prefix_env_value(&paths)?;
    println!("LLVM {LLVM_VERSION} ready at {prefix}");
    let _ = sh;
    Ok(())
}

fn llvm_doctor(_sh: &Shell) -> Result<()> {
    let paths = LlvmPaths::new();
    ensure_llvm_toolchain(&paths)?;
    validate_install(&paths)?;
    let prefix = prefix_env_value(&paths)?;
    println!("LLVM toolchain healthy: {prefix}");
    Ok(())
}

fn llvm_check(sh: &Shell) -> Result<()> {
    let prefix = llvm_env_prefix()?;
    ensure_windows_libxml2_stub(&prefix)?;
    let _guard = sh.push_env("LLVM_SYS_180_PREFIX", &prefix);
    cmd!(sh, "cargo check -p aura-codegen --features llvm-backend").run()?;
    Ok(())
}

fn llvm_build(sh: &Shell) -> Result<()> {
    let prefix = llvm_env_prefix()?;
    ensure_windows_libxml2_stub(&prefix)?;
    let _guard = sh.push_env("LLVM_SYS_180_PREFIX", &prefix);
    cmd!(sh, "cargo build -p aura-codegen --features llvm-backend").run()?;
    Ok(())
}

fn llvm_test(sh: &Shell) -> Result<()> {
    let prefix = llvm_env_prefix()?;
    ensure_windows_libxml2_stub(&prefix)?;
    let _guard = sh.push_env("LLVM_SYS_180_PREFIX", &prefix);
    cmd!(sh, "cargo test -p aura-codegen --features llvm-backend").run()?;
    Ok(())
}

fn llvm_clippy(sh: &Shell) -> Result<()> {
    let prefix = llvm_env_prefix()?;
    ensure_windows_libxml2_stub(&prefix)?;
    let _guard = sh.push_env("LLVM_SYS_180_PREFIX", &prefix);
    cmd!(
        sh,
        "cargo clippy -p aura-codegen --features llvm-backend --all-targets -- -D warnings"
    )
    .run()?;
    Ok(())
}

fn llvm_run(args: &[String]) -> Result<()> {
    let prefix = llvm_env_prefix()?;
    ensure_windows_libxml2_stub(&prefix)?;
    llvm_build_runtime_host(&prefix)?;
    run_cargo_with_llvm_env("run", &inject_llvm_backend_for_aura_cli(args), &prefix)
}

fn llvm_cargo(args: &[String]) -> Result<()> {
    let prefix = llvm_env_prefix()?;
    ensure_windows_libxml2_stub(&prefix)?;
    llvm_build_runtime_host(&prefix)?;
    run_cargo_with_llvm_env("", args, &prefix)
}

fn llvm_build_runtime_host(prefix: &str) -> Result<()> {
    let mut cmd = Command::new("cargo");
    cmd.arg("build").arg("-p").arg("aura-runtime-host");
    cmd.env("LLVM_SYS_180_PREFIX", prefix);
    let status = cmd
        .status()
        .context("failed to build aura-runtime-host for LLVM flow")?;
    if !status.success() {
        bail!("failed to build aura-runtime-host (cargo status {status})");
    }
    Ok(())
}

fn inject_llvm_backend_for_aura_cli(args: &[String]) -> Vec<String> {
    let mut out = args.to_vec();
    let is_aura_cli_run = out.windows(2).any(|w| w[0] == "-p" && w[1] == "aura-cli")
        || out.iter().any(|a| a == "aura-cli");
    let already_has_features = out.iter().any(|a| a == "--features");
    if is_aura_cli_run && !already_has_features {
        let insert_at = out.iter().position(|a| a == "--").unwrap_or(out.len());
        out.insert(insert_at, "llvm-backend".to_string());
        out.insert(insert_at, "--features".to_string());
    }
    out
}

fn run_cargo_with_llvm_env(mode: &str, args: &[String], prefix: &str) -> Result<()> {
    let mut cmd = Command::new("cargo");
    if !mode.is_empty() {
        cmd.arg(mode);
    }
    cmd.args(args);
    cmd.env("LLVM_SYS_180_PREFIX", prefix);
    let status = cmd.status().context("failed to start cargo command")?;
    if !status.success() {
        bail!("cargo command failed with status {status}");
    }
    Ok(())
}

fn llvm_env_prefix() -> Result<String> {
    let paths = LlvmPaths::new();
    ensure_llvm_toolchain(&paths)?;
    validate_install(&paths)?;
    prefix_env_value(&paths)
}

fn ensure_windows_libxml2_stub(prefix: &str) -> Result<()> {
    if !cfg!(windows) {
        return Ok(());
    }

    let system_libs = llvm_config_system_libs(prefix)?;
    if !system_libs
        .iter()
        .any(|lib| lib.eq_ignore_ascii_case("libxml2s.lib"))
    {
        return Ok(());
    }

    let mut stub_path = PathBuf::from(prefix);
    stub_path.push("lib");
    stub_path.push("libxml2s.lib");

    let mut llvm_lib = PathBuf::from(prefix);
    llvm_lib.push("bin");
    llvm_lib.push("llvm-lib.exe");
    if !llvm_lib.exists() {
        bail!(
            "missing '{}' needed to create Windows libxml2s stub",
            llvm_lib.display()
        );
    }

    let mut clang_cl = PathBuf::from(prefix);
    clang_cl.push("bin");
    clang_cl.push("clang-cl.exe");
    if !clang_cl.exists() {
        bail!(
            "missing '{}' needed to create Windows libxml2s stub",
            clang_cl.display()
        );
    }

    if stub_path.exists() {
        fs::remove_file(&stub_path)
            .with_context(|| format!("failed to remove stale '{}'", stub_path.display()))?;
    }

    let mut temp_dir = PathBuf::from(prefix);
    temp_dir.push("lib");
    temp_dir.push(format!(".aura-libxml2-stub-{}", std::process::id()));
    fs::create_dir_all(&temp_dir)
        .with_context(|| format!("failed to create '{}'", temp_dir.display()))?;

    let source_path = temp_dir.join("stub.c");
    let object_path = temp_dir.join("stub.obj");
    fs::write(&source_path, "void aura_llvm_xml2_stub(void) {}\n")
        .with_context(|| format!("failed to write '{}'", source_path.display()))?;

    let compile_status = Command::new(&clang_cl)
        .arg("/nologo")
        .arg("/c")
        .arg("/TC")
        .arg(&source_path)
        .arg(format!("/Fo{}", object_path.display()))
        .status()
        .with_context(|| format!("failed to run '{}'", clang_cl.display()))?;
    if !compile_status.success() {
        bail!(
            "failed to compile '{}' with '{}'",
            source_path.display(),
            clang_cl.display()
        );
    }

    let status = Command::new(&llvm_lib)
        .arg("/nologo")
        .arg(format!("/OUT:{}", stub_path.display()))
        .arg(&object_path)
        .status()
        .with_context(|| format!("failed to run '{}'", llvm_lib.display()))?;
    if !status.success() {
        bail!(
            "failed to create '{}' using '{}'",
            stub_path.display(),
            llvm_lib.display()
        );
    }

    println!(
        "created Windows LLVM compatibility stub at {}",
        stub_path.display()
    );

    let _ = fs::remove_file(&source_path);
    let _ = fs::remove_file(&object_path);
    let _ = fs::remove_dir(&temp_dir);
    Ok(())
}

fn llvm_config_system_libs(prefix: &str) -> Result<Vec<String>> {
    let mut llvm_config = PathBuf::from(prefix);
    llvm_config.push("bin");
    llvm_config.push(if cfg!(windows) {
        "llvm-config.exe"
    } else {
        "llvm-config"
    });

    let output = Command::new(&llvm_config)
        .arg("--system-libs")
        .arg("--link-static")
        .output()
        .with_context(|| format!("failed to run '{}'", llvm_config.display()))?;
    if !output.status.success() {
        bail!(
            "'{} --system-libs --link-static' failed with status {}",
            llvm_config.display(),
            output.status
        );
    }

    let stdout = String::from_utf8(output.stdout)
        .context("llvm-config --system-libs output is not valid UTF-8")?;
    Ok(stdout
        .split_whitespace()
        .map(|s| s.to_string())
        .collect::<Vec<_>>())
}

fn llvm_clean() -> Result<()> {
    let toolchains = PathBuf::from("toolchains");
    if toolchains.exists() {
        fs::remove_dir_all(&toolchains)
            .with_context(|| format!("failed to remove '{}'", toolchains.display()))?;
        println!("removed {}", toolchains.display());
    } else {
        println!("{} does not exist, nothing to clean", toolchains.display());
    }
    Ok(())
}

#[derive(Debug, Clone)]
struct LlvmPaths {
    archive_name: String,
    archive_path: PathBuf,
    cache_dir: PathBuf,
    install_root: PathBuf,
    install_dir: PathBuf,
    major_link: PathBuf,
    temp_extract_dir: PathBuf,
    asset_url: String,
}

impl LlvmPaths {
    fn new() -> Self {
        let platform = host_platform_asset();
        let archive_name = format!("clang+llvm-{LLVM_VERSION}-{platform}.tar.xz");
        let asset_url = format!(
            "https://github.com/llvm/llvm-project/releases/download/llvmorg-{LLVM_VERSION}/{archive_name}"
        );

        let cache_dir = PathBuf::from("toolchains").join("cache");
        let archive_path = cache_dir.join(&archive_name);

        let install_root = PathBuf::from("toolchains")
            .join("llvm")
            .join(LLVM_VERSION)
            .join(platform);
        let install_dir = install_root.join(format!("clang+llvm-{LLVM_VERSION}-{platform}"));
        let temp_extract_dir = install_root.join(".extracting");
        let major_link = PathBuf::from("toolchains").join("llvm").join(LLVM_MAJOR);

        Self {
            archive_name,
            archive_path,
            cache_dir,
            install_root,
            install_dir,
            major_link,
            temp_extract_dir,
            asset_url,
        }
    }
}

fn host_platform_asset() -> &'static str {
    match (env::consts::OS, env::consts::ARCH) {
        ("windows", "x86_64") => "x86_64-pc-windows-msvc",
        ("linux", "x86_64") => "x86_64-linux-gnu-ubuntu-18.04",
        ("macos", "aarch64") => "arm64-apple-macos11",
        ("linux", "aarch64") => "aarch64-linux-gnu",
        (os, arch) => panic!("unsupported host platform for LLVM prebuilt binary: {os}/{arch}"),
    }
}

fn ensure_llvm_toolchain(paths: &LlvmPaths) -> Result<()> {
    if !is_valid_install(paths) {
        download_archive_if_missing(paths)?;
        extract_archive(paths)?;
    }

    ensure_major_link(paths)
}

fn is_valid_install(paths: &LlvmPaths) -> bool {
    llvm_config_path(&paths.install_dir).is_file()
}

fn llvm_config_path(prefix: &Path) -> PathBuf {
    let exe = if cfg!(windows) {
        "llvm-config.exe"
    } else {
        "llvm-config"
    };
    prefix.join("bin").join(exe)
}

fn download_archive_if_missing(paths: &LlvmPaths) -> Result<()> {
    if paths.archive_path.exists() {
        return Ok(());
    }

    fs::create_dir_all(&paths.cache_dir)
        .with_context(|| format!("failed to create '{}'", paths.cache_dir.display()))?;

    println!("downloading {}", paths.archive_name);
    let client = Client::builder().build()?;
    let mut response = client
        .get(&paths.asset_url)
        .send()
        .with_context(|| format!("failed to request '{}'", paths.asset_url))?
        .error_for_status()
        .with_context(|| format!("failed to download '{}'", paths.asset_url))?;

    let tmp_path = paths.archive_path.with_extension("tmp");
    let mut out = BufWriter::new(
        File::create(&tmp_path)
            .with_context(|| format!("failed to create '{}'", tmp_path.display()))?,
    );
    std::io::copy(&mut response, &mut out)
        .with_context(|| format!("failed to write '{}'", tmp_path.display()))?;
    out.flush()
        .with_context(|| format!("failed to flush '{}'", tmp_path.display()))?;

    fs::rename(&tmp_path, &paths.archive_path).with_context(|| {
        format!(
            "failed to move '{}' to '{}'",
            tmp_path.display(),
            paths.archive_path.display()
        )
    })?;
    Ok(())
}

fn extract_archive(paths: &LlvmPaths) -> Result<()> {
    fs::create_dir_all(&paths.install_root)
        .with_context(|| format!("failed to create '{}'", paths.install_root.display()))?;

    if paths.temp_extract_dir.exists() {
        fs::remove_dir_all(&paths.temp_extract_dir)
            .with_context(|| format!("failed to remove '{}'", paths.temp_extract_dir.display()))?;
    }
    fs::create_dir_all(&paths.temp_extract_dir)
        .with_context(|| format!("failed to create '{}'", paths.temp_extract_dir.display()))?;

    let file = File::open(&paths.archive_path)
        .with_context(|| format!("failed to open '{}'", paths.archive_path.display()))?;
    let decoder = XzDecoder::new(BufReader::new(file));
    let mut archive = Archive::new(decoder);
    archive
        .unpack(&paths.temp_extract_dir)
        .with_context(|| format!("failed to extract '{}'", paths.archive_path.display()))?;

    if paths.install_dir.exists() {
        fs::remove_dir_all(&paths.install_dir)
            .with_context(|| format!("failed to remove '{}'", paths.install_dir.display()))?;
    }

    let extracted_root = find_llvm_extract_root(&paths.temp_extract_dir)?;
    if extracted_root == paths.temp_extract_dir {
        fs::rename(&paths.temp_extract_dir, &paths.install_dir).with_context(|| {
            format!(
                "failed to finalize extracted LLVM directory '{}'",
                paths.install_dir.display()
            )
        })?;
    } else {
        fs::rename(&extracted_root, &paths.install_dir).with_context(|| {
            format!(
                "failed to finalize extracted LLVM directory '{}'",
                paths.install_dir.display()
            )
        })?;
        fs::remove_dir_all(&paths.temp_extract_dir)
            .with_context(|| format!("failed to remove '{}'", paths.temp_extract_dir.display()))?;
    }
    Ok(())
}

/// Prefer the directory that actually contains `bin/llvm-config` so we do not pick an unrelated
/// top-level folder when the archive has multiple entries, and support a flat unpack layout.
fn find_llvm_extract_root(extract_root: &Path) -> Result<PathBuf> {
    if llvm_config_path(extract_root).is_file() {
        return Ok(extract_root.to_path_buf());
    }
    let mut dirs = fs::read_dir(extract_root)
        .with_context(|| format!("failed to read '{}'", extract_root.display()))?
        .filter_map(|entry| entry.ok().map(|e| e.path()))
        .filter(|p| p.is_dir())
        .collect::<Vec<_>>();
    dirs.sort();
    for dir in dirs {
        if llvm_config_path(&dir).is_file() {
            return Ok(dir);
        }
    }
    let expected = if cfg!(windows) {
        "bin/llvm-config.exe"
    } else {
        "bin/llvm-config"
    };
    bail!(
        "extracted LLVM archive did not contain '{}' under '{}' or any subdirectory",
        expected,
        extract_root.display()
    );
}

fn ensure_major_link(paths: &LlvmPaths) -> Result<()> {
    let canonical_install = fs::canonicalize(&paths.install_dir)
        .with_context(|| format!("failed to canonicalize '{}'", paths.install_dir.display()))?;

    if paths.major_link.exists() {
        let canonical_link = fs::canonicalize(&paths.major_link);
        if let Err(err) = &canonical_link {
            eprintln!(
                "warning: failed to resolve '{}': {err}. recreating link",
                paths.major_link.display()
            );
            remove_path(&paths.major_link)?;
        }
        let canonical_link = canonical_link.ok();
        if let Some(canonical_link) = canonical_link {
            if canonical_link == canonical_install {
                return Ok(());
            }
            remove_path(&paths.major_link)?;
        }
    }

    if let Some(parent) = paths.major_link.parent() {
        fs::create_dir_all(parent)
            .with_context(|| format!("failed to create '{}'", parent.display()))?;
    }

    create_link(&canonical_install, &paths.major_link)
}

fn validate_install(paths: &LlvmPaths) -> Result<()> {
    let config = llvm_config_path(&paths.major_link);
    if !config.is_file() {
        bail!("llvm-config not found at '{}'", config.display());
    }
    Ok(())
}

fn prefix_env_value(paths: &LlvmPaths) -> Result<String> {
    let canonical = fs::canonicalize(&paths.major_link)
        .with_context(|| format!("failed to canonicalize '{}'", paths.major_link.display()))?;
    Ok(canonical.to_string_lossy().to_string())
}

fn remove_path(path: &Path) -> Result<()> {
    let meta = fs::symlink_metadata(path)
        .with_context(|| format!("failed to stat '{}'", path.display()))?;
    let file_type = meta.file_type();

    if file_type.is_symlink() {
        if file_type.is_dir() {
            fs::remove_dir(path)
                .with_context(|| format!("failed to remove symlink '{}'", path.display()))?;
        } else {
            fs::remove_file(path)
                .with_context(|| format!("failed to remove symlink '{}'", path.display()))?;
        }
        return Ok(());
    }

    if meta.is_dir() {
        fs::remove_dir_all(path)
            .with_context(|| format!("failed to remove directory '{}'", path.display()))?;
    } else {
        fs::remove_file(path)
            .with_context(|| format!("failed to remove file '{}'", path.display()))?;
    }

    Ok(())
}

#[cfg(windows)]
fn create_link(target: &Path, link_path: &Path) -> Result<()> {
    use std::process::Command;
    let status = Command::new("cmd")
        .arg("/C")
        .arg("mklink")
        .arg("/J")
        .arg(link_path)
        .arg(target)
        .status()
        .with_context(|| {
            format!(
                "failed to run mklink for '{}' -> '{}'",
                link_path.display(),
                target.display()
            )
        })?;
    if !status.success() {
        bail!(
            "failed to create junction '{}' -> '{}'",
            link_path.display(),
            target.display()
        );
    }
    Ok(())
}

#[cfg(not(windows))]
fn create_link(target: &Path, link_path: &Path) -> Result<()> {
    std::os::unix::fs::symlink(target, link_path).with_context(|| {
        format!(
            "failed to create symlink '{}' -> '{}'",
            link_path.display(),
            target.display()
        )
    })
}
