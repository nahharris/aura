use std::fmt::Write as _;
use std::fs;
use std::path::{Path, PathBuf};

use anyhow::{Context, Result, bail};
use clap::Subcommand;
use time::OffsetDateTime;
use time::format_description::well_known::Rfc3339;
use toml::Value;

#[derive(Subcommand, Debug)]
pub enum DocsCommands {
    Sync,
    Check,
    NewAdr {
        #[arg(long)]
        title: String,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct RepoInventory {
    workspace_members: Vec<String>,
    top_level_directories: Vec<String>,
    example_files: Vec<String>,
    test_files: Vec<String>,
}

#[derive(Clone, Copy)]
struct CuratedNoteSpec {
    path: &'static str,
    required_fields: &'static [&'static str],
    render: fn(&RepoInventory) -> String,
}

pub fn run(command: DocsCommands, root: &Path) -> Result<()> {
    match command {
        DocsCommands::Sync => sync(root),
        DocsCommands::Check => check(root),
        DocsCommands::NewAdr { title } => {
            let path = new_adr(root, &title)?;
            println!("created {}", display_rel(root, &path));
            Ok(())
        }
    }
}

fn sync(root: &Path) -> Result<()> {
    fs::create_dir_all(root.join("docs")).context("failed to create docs root")?;
    let inventory = discover_repo_inventory(root)?;
    let generated_at = now_rfc3339()?;

    for (path, contents) in expected_generated_files(&inventory, &generated_at) {
        write_string(root.join(path), &contents)?;
    }

    for spec in curated_note_specs() {
        let path = root.join(spec.path);
        if !path.exists() {
            write_string(path, &(spec.render)(&inventory))?;
        }
    }

    for (path, contents) in base_files() {
        let full = root.join(path);
        if !full.exists() {
            write_string(full, contents)?;
        }
    }

    println!("synced docs vault");
    Ok(())
}

fn check(root: &Path) -> Result<()> {
    let inventory = discover_repo_inventory(root)?;
    let generated_at = now_rfc3339()?;

    for (path, expected) in expected_generated_files(&inventory, &generated_at) {
        let full_path = root.join(&path);
        let actual = fs::read_to_string(&full_path)
            .with_context(|| format!("missing generated note '{}'", full_path.display()))?;
        if strip_generated_at_line(&actual) != strip_generated_at_line(&expected) {
            bail!("generated note is stale: {path}");
        }
    }

    for spec in curated_note_specs() {
        let full_path = root.join(spec.path);
        let contents = fs::read_to_string(&full_path)
            .with_context(|| format!("missing curated note '{}'", full_path.display()))?;
        for required in spec.required_fields {
            if !contents.contains(required) {
                bail!(
                    "curated note '{}' is missing required field '{}'",
                    spec.path,
                    required
                );
            }
        }
    }

    for (path, _) in base_files() {
        let full_path = root.join(path);
        if !full_path.is_file() {
            bail!("missing base view '{}'", full_path.display());
        }
    }

    Ok(())
}

fn new_adr(root: &Path, title: &str) -> Result<PathBuf> {
    let slug = slugify(title);
    let date = now_date()?;
    let rel = format!("docs/Decisions/{date}-{slug}.md");
    let path = root.join(&rel);
    if path.exists() {
        bail!("ADR already exists at '{rel}'");
    }

    let contents = format!(
        r#"---
title: "{title}"
kind: adr
status: proposed
date: {date}
related_paths: []
related_notes:
  - "Architecture/Repo Map"
---

# {title}

## Context

Describe the design pressure or problem that required a decision.

## Decision

State the decision in concrete engineering terms.

## Consequences

- Positive outcomes.
- Tradeoffs or follow-up work.
"#
    );
    write_string(&path, &contents)?;
    Ok(path)
}

fn discover_repo_inventory(root: &Path) -> Result<RepoInventory> {
    let manifest = fs::read_to_string(root.join("Cargo.toml"))
        .context("failed to read workspace Cargo.toml")?;
    let workspace_members = parse_workspace_members(&manifest)?;
    let top_level_directories = collect_top_level_directories(root)?;
    let example_files = collect_files_in_dir(root, "examples")?;
    let test_files = collect_test_files(root)?;

    Ok(RepoInventory {
        workspace_members,
        top_level_directories,
        example_files,
        test_files,
    })
}

fn parse_workspace_members(manifest: &str) -> Result<Vec<String>> {
    let value: Value = manifest.parse().context("failed to parse Cargo.toml")?;
    let members = value
        .get("workspace")
        .and_then(Value::as_table)
        .and_then(|table| table.get("members"))
        .and_then(Value::as_array)
        .context("workspace.members missing from Cargo.toml")?;

    let mut out = members
        .iter()
        .filter_map(Value::as_str)
        .map(ToOwned::to_owned)
        .collect::<Vec<_>>();
    out.sort();
    Ok(out)
}

fn collect_top_level_directories(root: &Path) -> Result<Vec<String>> {
    let mut out = Vec::new();
    for entry in fs::read_dir(root).context("failed to read workspace root")? {
        let entry = entry?;
        if !entry.file_type()?.is_dir() {
            continue;
        }
        let name = entry.file_name().to_string_lossy().to_string();
        if should_skip_relative_path(&name) {
            continue;
        }
        out.push(name);
    }
    out.sort();
    Ok(out)
}

fn collect_files_in_dir(root: &Path, rel_dir: &str) -> Result<Vec<String>> {
    let dir = root.join(rel_dir);
    if !dir.exists() {
        return Ok(Vec::new());
    }
    let mut out = Vec::new();
    collect_files_recursive(root, &dir, &mut out)?;
    out.sort();
    Ok(out)
}

fn collect_test_files(root: &Path) -> Result<Vec<String>> {
    let mut all_files = Vec::new();
    collect_files_recursive(root, root, &mut all_files)?;
    let mut tests = all_files
        .into_iter()
        .filter(|path| {
            let path_lower = path.to_ascii_lowercase();
            path_lower.contains("/tests/")
                || path_lower.ends_with(".test.aura")
                || path_lower.contains("_test.")
                || path_lower.contains("snapshot")
        })
        .collect::<Vec<_>>();
    tests.sort();
    Ok(tests)
}

fn collect_files_recursive(root: &Path, dir: &Path, out: &mut Vec<String>) -> Result<()> {
    for entry in fs::read_dir(dir).with_context(|| format!("failed to read '{}'", dir.display()))? {
        let entry = entry?;
        let path = entry.path();
        let rel = relative_path(root, &path)?;
        if should_skip_relative_path(&rel) {
            continue;
        }

        if entry.file_type()?.is_dir() {
            collect_files_recursive(root, &path, out)?;
        } else {
            out.push(rel);
        }
    }
    Ok(())
}

fn relative_path(root: &Path, path: &Path) -> Result<String> {
    let rel = path.strip_prefix(root).with_context(|| {
        format!(
            "failed to strip '{}' from '{}'",
            root.display(),
            path.display()
        )
    })?;
    Ok(rel.to_string_lossy().replace('\\', "/"))
}

fn should_skip_relative_path(path: &str) -> bool {
    let normalized = path.replace('\\', "/");
    let prefixes = [
        ".git",
        ".opencode",
        "target",
        "target2",
        "toolchains",
        "docs/.obsidian",
        "tool/tree-sitter-aura/node_modules",
    ];

    prefixes
        .iter()
        .any(|prefix| normalized == *prefix || normalized.starts_with(&format!("{prefix}/")))
}

fn expected_generated_files(
    inventory: &RepoInventory,
    generated_at: &str,
) -> Vec<(String, String)> {
    vec![
        (
            "docs/Generated/Workspace Inventory.md".to_string(),
            wrap_generated_note(
                "Workspace Inventory",
                generated_at,
                &render_workspace_inventory(&inventory.workspace_members),
            ),
        ),
        (
            "docs/Generated/Commands Inventory.md".to_string(),
            wrap_generated_note(
                "Commands Inventory",
                generated_at,
                &render_commands_inventory(),
            ),
        ),
        (
            "docs/Generated/Examples Inventory.md".to_string(),
            wrap_generated_note(
                "Examples Inventory",
                generated_at,
                &render_examples_inventory(&inventory.example_files),
            ),
        ),
        (
            "docs/Generated/Test Inventory.md".to_string(),
            wrap_generated_note(
                "Test Inventory",
                generated_at,
                &render_test_inventory(&inventory.test_files),
            ),
        ),
        (
            "docs/Generated/Directory Inventory.md".to_string(),
            wrap_generated_note(
                "Directory Inventory",
                generated_at,
                &render_directory_inventory(&inventory.top_level_directories),
            ),
        ),
    ]
}

fn curated_note_specs() -> Vec<CuratedNoteSpec> {
    vec![
        CuratedNoteSpec {
            path: "docs/Home.md",
            required_fields: &["title: Home", "kind: index"],
            render: render_home_note,
        },
        CuratedNoteSpec {
            path: "docs/Architecture/Repo Map.md",
            required_fields: &["kind: architecture"],
            render: render_repo_map_note,
        },
        CuratedNoteSpec {
            path: "docs/Architecture/Build And Dev Workflow.md",
            required_fields: &["kind: architecture"],
            render: render_build_workflow_note,
        },
        CuratedNoteSpec {
            path: "docs/Architecture/Testing Strategy.md",
            required_fields: &["kind: architecture"],
            render: render_testing_strategy_note,
        },
        CuratedNoteSpec {
            path: "docs/Language/Design Overview.md",
            required_fields: &["kind: language"],
            render: render_language_design_note,
        },
        CuratedNoteSpec {
            path: "docs/Language/Syntax And Semantics.md",
            required_fields: &["kind: language"],
            render: render_language_syntax_note,
        },
        CuratedNoteSpec {
            path: "docs/Language/Lexical Rules.md",
            required_fields: &["kind: language"],
            render: render_language_lexical_rules_note,
        },
        CuratedNoteSpec {
            path: "docs/Language/Type System.md",
            required_fields: &["kind: language"],
            render: render_language_type_system_note,
        },
        CuratedNoteSpec {
            path: "docs/Language/Literals And Data.md",
            required_fields: &["kind: language"],
            render: render_language_literals_and_data_note,
        },
        CuratedNoteSpec {
            path: "docs/Language/Bindings And Declarations.md",
            required_fields: &["kind: language"],
            render: render_language_bindings_and_declarations_note,
        },
        CuratedNoteSpec {
            path: "docs/Language/Functions And Closures.md",
            required_fields: &["kind: language"],
            render: render_language_functions_and_closures_note,
        },
        CuratedNoteSpec {
            path: "docs/Language/Calls Operators And Blocks.md",
            required_fields: &["kind: language"],
            render: render_language_calls_operators_and_blocks_note,
        },
        CuratedNoteSpec {
            path: "docs/Language/Control Flow.md",
            required_fields: &["kind: language"],
            render: render_language_control_flow_note,
        },
        CuratedNoteSpec {
            path: "docs/Language/Modules Projects And Runtime.md",
            required_fields: &["kind: language"],
            render: render_language_modules_projects_and_runtime_note,
        },
        CuratedNoteSpec {
            path: "docs/Language/Examples Index.md",
            required_fields: &["kind: language"],
            render: render_examples_index_note,
        },
        CuratedNoteSpec {
            path: "docs/Subsystems/Frontend.md",
            required_fields: &["kind: subsystem"],
            render: render_frontend_note,
        },
        CuratedNoteSpec {
            path: "docs/Subsystems/Typecheck.md",
            required_fields: &["kind: subsystem"],
            render: render_typecheck_note,
        },
        CuratedNoteSpec {
            path: "docs/Subsystems/Codegen.md",
            required_fields: &["kind: subsystem"],
            render: render_codegen_note,
        },
        CuratedNoteSpec {
            path: "docs/Subsystems/Diagnostics.md",
            required_fields: &["kind: subsystem"],
            render: render_diagnostics_note,
        },
        CuratedNoteSpec {
            path: "docs/Subsystems/CLI.md",
            required_fields: &["kind: subsystem"],
            render: render_cli_note,
        },
        CuratedNoteSpec {
            path: "docs/Subsystems/Runtime Host.md",
            required_fields: &["kind: subsystem"],
            render: render_runtime_host_note,
        },
        CuratedNoteSpec {
            path: "docs/Subsystems/Stdlib.md",
            required_fields: &["kind: subsystem"],
            render: render_stdlib_note,
        },
        CuratedNoteSpec {
            path: "docs/Subsystems/Xtask.md",
            required_fields: &["kind: subsystem"],
            render: render_xtask_note,
        },
        CuratedNoteSpec {
            path: "docs/Subsystems/Editor Tooling.md",
            required_fields: &["kind: subsystem"],
            render: render_editor_tooling_note,
        },
        CuratedNoteSpec {
            path: "docs/Contracts/Typecheck IR.md",
            required_fields: &["kind: contract"],
            render: render_typecheck_contract_note,
        },
        CuratedNoteSpec {
            path: "docs/Decisions/README.md",
            required_fields: &["kind: index"],
            render: render_decisions_index_note,
        },
        CuratedNoteSpec {
            path: "docs/Templates/Subsystem Note.md",
            required_fields: &["kind: template"],
            render: render_subsystem_template_note,
        },
        CuratedNoteSpec {
            path: "docs/Templates/ADR.md",
            required_fields: &["kind: template"],
            render: render_adr_template_note,
        },
    ]
}

fn base_files() -> Vec<(&'static str, &'static str)> {
    vec![
        (
            "docs/Bases/Subsystems.base",
            r#"filters:
  and:
    - 'kind == "subsystem"'

properties:
  status:
    displayName: Status
  source_paths:
    displayName: Source Paths
  depends_on:
    displayName: Depends On
  last_reviewed:
    displayName: Last Reviewed

views:
  - type: table
    name: "Subsystems"
    order:
      - file.name
      - status
      - source_paths
      - depends_on
      - last_reviewed
"#,
        ),
        (
            "docs/Bases/Decisions.base",
            r#"filters:
  and:
    - 'kind == "adr"'

properties:
  status:
    displayName: Status
  date:
    displayName: Date
  related_paths:
    displayName: Related Paths

views:
  - type: table
    name: "Decisions"
    order:
      - file.name
      - status
      - date
      - related_paths
"#,
        ),
    ]
}

fn wrap_generated_note(title: &str, generated_at: &str, body: &str) -> String {
    format!(
        r#"---
title: {title}
kind: generated
generated_by: cargo xtask docs sync
generated_at: {generated_at}
---

{body}
"#
    )
}

fn render_workspace_inventory(members: &[String]) -> String {
    let mut out = String::from("# Workspace Inventory\n\n");
    out.push_str("| Path | Role |\n| --- | --- |\n");
    for member in members {
        let _ = writeln!(
            out,
            "| `{member}` | {} |",
            describe_workspace_member(member)
        );
    }
    out.push_str(
        "\n## Companion Surfaces\n\n- `aura-stl/` holds the standard library package.\n- `tool/` holds editor integrations and the Tree-sitter grammar.\n- `examples/` holds compiler-facing sample programs.\n",
    );
    out
}

fn render_commands_inventory() -> String {
    r#"# Commands Inventory

## Workspace Dev

| Command | Purpose |
| --- | --- |
| `cargo xtask dev check` | Check the full workspace. |
| `cargo xtask dev build` | Build the full workspace. |
| `cargo xtask dev test` | Run the full workspace test suite. |
| `cargo xtask dev lint` | Run clippy with warnings denied. |
| `cargo xtask dev fmt` | Format the workspace. |
| `cargo xtask dev fmt-check` | Fail if sources are not rustfmt-clean (CI-safe). |
| `cargo xtask dev ci` | Full CI parity: fmt-check, lint, test, docs check, LLVM doctor + clippy + test. |
| `cargo xtask dev qa` | Format, lint, and test. |

## LLVM Flow

| Command | Purpose |
| --- | --- |
| `cargo xtask llvm setup` | Install or validate the managed LLVM toolchain. |
| `cargo xtask llvm doctor` | Check the managed LLVM toolchain. |
| `cargo xtask llvm ci` | Doctor, then clippy and tests (toolchain must already be installed). |
| `cargo xtask llvm check` | Check `aura-codegen` with the LLVM backend feature. |
| `cargo xtask llvm build` | Build `aura-codegen` with the LLVM backend feature. |
| `cargo xtask llvm test` | Test `aura-codegen` with the LLVM backend feature. |
| `cargo xtask llvm clippy` | Lint `aura-codegen` with the LLVM backend feature. |
| `cargo xtask llvm run -- -p aura-cli -- build examples/basic_ops.aura` | Run the CLI under the managed LLVM environment. |

## Docs Vault

| Command | Purpose |
| --- | --- |
| `cargo xtask docs sync` | Refresh generated inventories and scaffold missing vault notes. |
| `cargo xtask docs check` | Fail when generated inventory notes are stale or required curated notes are missing. |
| `cargo xtask docs new-adr --title "Decision Name"` | Create a dated ADR note. |

## QMD (Docker)

| Command | Purpose |
| --- | --- |
| `cargo xtask qmd build` | Build the local Docker image for qmd workflows. |
| `cargo xtask qmd start` | Start qmd MCP in HTTP mode with `docs/` mounted at `http://127.0.0.1:8181/mcp`. |
| `cargo xtask qmd stop` | Stop and remove the qmd MCP container. |
| `cargo xtask qmd cmd -- <args...>` | Pass through arbitrary `qmd` CLI commands to the running qmd container. |
| `cargo xtask qmd mcp` | Ensure MCP HTTP mode is running and print the endpoint URLs. |
"#
        .to_string()
}

fn render_examples_inventory(files: &[String]) -> String {
    let mut out = String::from("# Examples Inventory\n\n| Path | Notes |\n| --- | --- |\n");
    for file in files {
        let note = if file.ends_with(".ir.aura") {
            "checked IR example"
        } else if file.ends_with(".ir.json") {
            "serialized IR artifact"
        } else if file.contains("broken_") {
            "negative example for diagnostics"
        } else {
            "source example"
        };
        let _ = writeln!(out, "| `{file}` | {note} |");
    }
    out
}

fn render_test_inventory(files: &[String]) -> String {
    let mut out = String::from("# Test Inventory\n\n| Path | Surface |\n| --- | --- |\n");
    for file in files {
        let surface = if file.contains("aura-frontend") {
            "frontend"
        } else if file.contains("aura-typecheck") {
            "typecheck"
        } else if file.contains("aura-codegen") {
            "codegen"
        } else if file.contains("aura-cli") {
            "cli"
        } else if file.contains("aura-stl") {
            "stdlib"
        } else {
            "other"
        };
        let _ = writeln!(out, "| `{file}` | {surface} |");
    }
    out
}

fn render_directory_inventory(dirs: &[String]) -> String {
    let mut out = String::from("# Directory Inventory\n\n| Directory | Purpose |\n| --- | --- |\n");
    for dir in dirs {
        let _ = writeln!(out, "| `{dir}` | {} |", describe_directory(dir));
    }
    out
}

fn render_home_note(_: &RepoInventory) -> String {
    r#"---
title: Home
kind: index
tags:
  - aura
  - engineering-wiki
---

# Aura Vault

> [!note]
> This vault is the internal engineering map for the Aura codebase. It is optimized for fast recall, contributor onboarding, and agent handoff.

## Start Here

- [[Architecture/Repo Map]]
- [[Architecture/Build And Dev Workflow]]
- [[Architecture/Testing Strategy]]
- [[Language/Design Overview]]
- [[Language/Syntax And Semantics]]
- [[Contracts/Typecheck IR]]

## Subsystems

- [[Subsystems/Frontend]]
- [[Subsystems/Typecheck]]
- [[Subsystems/Codegen]]
- [[Subsystems/Diagnostics]]
- [[Subsystems/CLI]]
- [[Subsystems/Runtime Host]]
- [[Subsystems/Stdlib]]
- [[Subsystems/Xtask]]
- [[Subsystems/Editor Tooling]]

## Generated Views

- [[Generated/Workspace Inventory]]
- [[Generated/Commands Inventory]]
- [[Generated/Examples Inventory]]
- [[Generated/Test Inventory]]
- [[Generated/Directory Inventory]]
- ![[Bases/Subsystems.base#Subsystems]]

## Decisions

- [[Decisions/README]]

## Wiki Ops

- QMD MCP: `cargo xtask qmd start`, then use `http://127.0.0.1:8181/mcp`.
"#
        .to_string()
}

fn render_repo_map_note(_: &RepoInventory) -> String {
    r#"---
title: "Repo Map"
kind: architecture
tags:
  - aura
  - architecture
---

# Repo Map

## Top-Level Layout

- `crates/` contains the Rust workspace crates that implement the compiler pipeline and CLI surfaces.
- `aura-stl/` contains the Aura standard library package written in Aura.
- `examples/` contains positive and negative sample programs used to exercise frontend and pipeline behavior.
- `tool/` contains editor integrations and the Tree-sitter grammar.
- `xtask/` contains project automation and LLVM toolchain management.
- `docs/` is the Obsidian second brain for the repo.

## Main Navigation Paths

- Language rules: [[Language/Design Overview]] and [[Language/Syntax And Semantics]]
- Compiler subsystems: [[Subsystems/Frontend]], [[Subsystems/Typecheck]], [[Subsystems/Codegen]]
- Developer workflows: [[Architecture/Build And Dev Workflow]] and [[Architecture/Testing Strategy]]
- Current IR contract: [[Contracts/Typecheck IR]]

## Generated Support

Use ![[Generated/Directory Inventory]] and ![[Generated/Workspace Inventory]] when you need a quick filesystem map before diving into a specific subsystem note.
"#
        .to_string()
}

fn render_build_workflow_note(_: &RepoInventory) -> String {
    r#"---
title: "Build And Dev Workflow"
kind: architecture
tags:
  - aura
  - workflow
---

# Build And Dev Workflow

## Default Commands

- `cargo xtask dev check`
- `cargo xtask dev build`
- `cargo xtask dev test`
- `cargo xtask dev lint`
- `cargo xtask dev fmt`
- `cargo xtask dev qa`

## LLVM-Sensitive Work

Run LLVM-backed checks and CLI builds through `cargo xtask llvm ...` so the managed toolchain is injected consistently.

## Documentation Workflow

- Refresh generated vault content: `cargo xtask docs sync`
- Verify generated docs are current: `cargo xtask docs check`
- Record design decisions: `cargo xtask docs new-adr --title "Decision Name"`
- Search and retrieve vault context with QMD when docs work spans multiple notes.

## QMD Workflow

- Build qmd container tooling: `cargo xtask qmd build`
- Start HTTP MCP service: `cargo xtask qmd start`
- Stop it: `cargo xtask qmd stop`
- Pass through CLI commands: `cargo xtask qmd cmd -- <args...>`
- MCP endpoint for IDE clients: `http://127.0.0.1:8181/mcp`
- Health endpoint: `http://127.0.0.1:8181/health`

## Related Notes

- [[Subsystems/Xtask]]
- [[Generated/Commands Inventory]]
"#
        .to_string()
}

fn render_testing_strategy_note(_: &RepoInventory) -> String {
    r#"---
title: "Testing Strategy"
kind: architecture
tags:
  - aura
  - testing
---

# Testing Strategy

## Test Layers

- Frontend parser and formatter tests live under `crates/aura-frontend`.
- Typecheck contract and diagnostic coverage lives under `crates/aura-typecheck`.
- Codegen tests live under `crates/aura-codegen`.
- CLI behavior tests live in `crates/aura-cli`.
- Aura standard library tests live beside source modules in `aura-stl/src/*.test.aura`.

## Expectations

- Syntax changes should carry frontend parser coverage.
- IR contract changes should update both code and [[Contracts/Typecheck IR]].
- Use workspace-level checks for broad validation and subsystem-local commands for tight loops.

## Generated Support

![[Generated/Test Inventory]]
"#
    .to_string()
}

fn render_language_design_note(_: &RepoInventory) -> String {
    r#"---
title: "Design Overview"
kind: language
tags:
  - aura
  - language-design
---

# Design Overview

Aura's language design source of truth lives in this vault. The language notes are split by topic so syntax, semantics, implementation notes, and onboarding paths stay together.

## Core Principles

- Readable, familiar syntax with a small primitive core.
- Macros shape surface syntax without turning parser rules into a special-case maze.
- `static` is the shared compile-time interface concept.
- Function-like declarations normalize to assignment semantics.

## Spec Notes

- [[Language/Lexical Rules]]
- [[Language/Type System]]
- [[Language/Literals And Data]]
- [[Language/Bindings And Declarations]]
- [[Language/Functions And Closures]]
- [[Language/Calls Operators And Blocks]]
- [[Language/Control Flow]]
- [[Language/Modules Projects And Runtime]]

## Related Notes

- [[Language/Syntax And Semantics]]
- [[Language/AUON]]
- [[Contracts/Typecheck IR]]
- [[Subsystems/Frontend]]
- [[Subsystems/Typecheck]]
"#
        .to_string()
}

fn render_language_syntax_note(_: &RepoInventory) -> String {
    r#"---
title: "Syntax And Semantics"
kind: language
tags:
  - aura
  - syntax
---

# Syntax And Semantics

This note is the quick operational map for Aura's current observable language rules. The detailed source of truth is split across the linked language notes.

## Canonical Rules To Keep In View

- Macro declaration canonical form: `defmacro[static_args] macro_name(ast_node) -> T { ... }`
- Macro application canonical forms: `macro_name node` and `macro_name[args] node`
- Macro application consumes a single operand and chains right-associatively
- Macro symbols are final and non-shadowable
- Top-level scope is static-only: `def`, `defmacro`, and `use`
- `static` is a reusable compile-time interface concept shared across features
- Function-like declaration syntax is assignment sugar and normalizes to assignment semantics
- `if` and `cases` are inline function calls, not dedicated parser special cases
- trailing closure call arguments are labeled
- `defstub` declares typed extern or builtin contracts at top level; same-name overloads are allowed only for stubs

## Where These Rules Land In Code

- tokenization: `crates/aura-frontend/src/token.rs`
- lexing: `crates/aura-frontend/src/lexer.rs`
- parsing: `crates/aura-frontend/src/parser.rs`
- static constraints: `crates/aura-frontend/src/static_eval.rs`
- checked IR: `crates/aura-typecheck/src/checked_ir.rs`

## Spec Map

- [[Language/Lexical Rules]]
- [[Language/Type System]]
- [[Language/Literals And Data]]
- [[Language/Bindings And Declarations]]
- [[Language/Functions And Closures]]
- [[Language/Calls Operators And Blocks]]
- [[Language/Control Flow]]
- [[Language/Modules Projects And Runtime]]
"#
    .to_string()
}

fn render_language_lexical_rules_note(_: &RepoInventory) -> String {
    render_language_topic_note(
        "Lexical Rules",
        "lexical rules, comments, identifiers, brackets, macro application, calls, and statement termination",
    )
}

fn render_language_type_system_note(_: &RepoInventory) -> String {
    render_language_topic_note(
        "Type System",
        "type expressions, generics, constraints, product types, sum types, interfaces, casts, and fallible patterns",
    )
}

fn render_language_literals_and_data_note(_: &RepoInventory) -> String {
    render_language_topic_note(
        "Literals And Data",
        "primitive literals, strings, collection literals, product values, sum values, nullable values, and string templates",
    )
}

fn render_language_bindings_and_declarations_note(_: &RepoInventory) -> String {
    render_language_topic_note(
        "Bindings And Declarations",
        "local bindings, `let`, `def`, `defstub`, scope rules, module-level declarations, and declaration normalization",
    )
}

fn render_language_functions_and_closures_note(_: &RepoInventory) -> String {
    render_language_topic_note(
        "Functions And Closures",
        "block closures, multi-arm closures, named parameters, patterns, and captures",
    )
}

fn render_language_calls_operators_and_blocks_note(_: &RepoInventory) -> String {
    render_language_topic_note(
        "Calls Operators And Blocks",
        "operator precedence, range syntax, block expressions, labeled blocks, positional calls, named calls, and trailing closures",
    )
}

fn render_language_control_flow_note(_: &RepoInventory) -> String {
    render_language_topic_note(
        "Control Flow",
        "`if`, `cases`, `loop`, `return`, `break`, `continue`, and jump target scope resolution",
    )
}

fn render_language_modules_projects_and_runtime_note(_: &RepoInventory) -> String {
    render_language_topic_note(
        "Modules Projects And Runtime",
        "imports, project manifests, runtime extern stubs, and managed memory handles",
    )
}

fn render_language_topic_note(title: &str, summary: &str) -> String {
    format!(
        r#"---
title: "{title}"
kind: language
tags:
  - aura
  - language
---

# {title}

This curated note owns Aura {summary}. Fill it from [[Language/Design Overview]] when rebuilding the vault.

## Related Notes

- [[Language/Design Overview]]
- [[Language/Syntax And Semantics]]
"#
    )
}

fn render_examples_index_note(_: &RepoInventory) -> String {
    r#"---
title: "Examples Index"
kind: language
tags:
  - aura
  - examples
---

# Examples Index

`examples/` is the fastest way to sample the current language surface and compiler pipeline expectations.

## Example Families

- positive source programs such as `hello_world.aura` and `basic_ops.aura`
- IR-oriented examples such as `*.ir.aura` and `*.ir.json`
- negative examples prefixed with `broken_` for parser and typecheck diagnostics

## Related Notes

- [[Generated/Examples Inventory]]
- [[Subsystems/CLI]]
"#
        .to_string()
}

fn render_frontend_note(_: &RepoInventory) -> String {
    subsystem_note(
        "Frontend",
        "active",
        &[
            "crates/aura-frontend/src/token.rs",
            "crates/aura-frontend/src/lexer.rs",
            "crates/aura-frontend/src/ast.rs",
            "crates/aura-frontend/src/parser.rs",
            "crates/aura-frontend/src/static_eval.rs",
            "crates/aura-frontend/src/fmt.rs",
        ],
        &["Language/Design Overview"],
        &[],
        &["Contracts/Typecheck IR", "Language/Syntax And Semantics"],
        r#"## Purpose

Own the syntax-facing compiler surface: tokens, lexing, AST construction, parsing, static-evaluable constraints, and source formatting.

## Entry Points

- `Parser` is re-exported from `crates/aura-frontend/src/lib.rs`
- `format_source` and `unified_diff` expose formatter functionality

## Testing

Primary parser contract tests live in `crates/aura-frontend/src/parser.rs`. Snapshot diagnostics live in `crates/aura-frontend/tests/diagnostics_snapshot.rs`.
"#,
    )
}

fn render_typecheck_note(_: &RepoInventory) -> String {
    subsystem_note(
        "Typecheck",
        "active",
        &[
            "crates/aura-typecheck/src/checker.rs",
            "crates/aura-typecheck/src/checked_ir.rs",
            "crates/aura-typecheck/src/resolver.rs",
            "crates/aura-typecheck/src/types.rs",
            "crates/aura-typecheck/src/unify.rs",
        ],
        &["Subsystems/Frontend", "Subsystems/Diagnostics"],
        &["Contracts/Typecheck IR"],
        &["Language/Syntax And Semantics"],
        r#"## Purpose

Resolve symbols, enforce type rules, and emit checked IR for downstream codegen.

## Entry Points

- `check_module`
- `check_module_with_options`
- `Resolver`

## Testing

Contract snapshots and diagnostics snapshots live under `crates/aura-typecheck/tests/`.
"#,
    )
}

fn render_codegen_note(_: &RepoInventory) -> String {
    subsystem_note(
        "Codegen",
        "active",
        &[
            "crates/aura-codegen/src/lib.rs",
            "crates/aura-codegen/src/llvm/mod.rs",
            "crates/aura-codegen/src/project/discover.rs",
            "crates/aura-codegen/src/project/manifest.rs",
        ],
        &["Subsystems/Typecheck", "Subsystems/Runtime Host"],
        &["Contracts/Typecheck IR"],
        &["Architecture/Build And Dev Workflow"],
        r#"## Purpose

Turn checked Aura modules into backend artifacts, currently centered on the LLVM path and project layout discovery.

## Entry Points

- `emit_llvm_ir`
- `emit_object_file`
- project discovery under `project/`

## Testing

LLVM-specific validation runs through `cargo xtask llvm ...`.
"#,
    )
}

fn render_diagnostics_note(_: &RepoInventory) -> String {
    subsystem_note(
        "Diagnostics",
        "active",
        &[
            "crates/aura-diagnostics/src/lib.rs",
            "crates/aura-diagnostics/src/issue.rs",
            "crates/aura-diagnostics/src/type_ref.rs",
            "crates/aura-diagnostics/src/typing_context.rs",
        ],
        &[],
        &[],
        &[
            "Subsystems/Frontend",
            "Subsystems/Typecheck",
            "Subsystems/CLI",
        ],
        r#"## Purpose

Provide shared diagnostic types, severity/stage metadata, issue codes, and type references used across compiler surfaces.

## Key Concepts

- `Diagnostic`
- `Severity`
- `Stage`
- `Span`
"#,
    )
}

fn render_cli_note(_: &RepoInventory) -> String {
    subsystem_note(
        "CLI",
        "active",
        &["crates/aura-cli/src/main.rs", "crates/aura-cli/templates/"],
        &[
            "Subsystems/Frontend",
            "Subsystems/Typecheck",
            "Subsystems/Codegen",
        ],
        &[],
        &["Language/Examples Index"],
        r#"## Purpose

Expose end-user commands such as project init, build, formatting, and doc extraction.

## Main Commands

- `init`
- `build`
- `fmt`
- `doc`

## Testing

CLI-local unit tests live in `crates/aura-cli/src/main.rs`.
"#,
    )
}

fn render_runtime_host_note(_: &RepoInventory) -> String {
    subsystem_note(
        "Runtime Host",
        "active",
        &["crates/aura-runtime-host/src/lib.rs"],
        &[],
        &[],
        &["Subsystems/Codegen"],
        r#"## Purpose

Provide the native runtime boundary required by generated code. The current exported surface is intentionally minimal.

## Current Export

- `rt_exit`
"#,
    )
}

fn render_stdlib_note(_: &RepoInventory) -> String {
    subsystem_note(
        "Stdlib",
        "active",
        &["aura-stl/project.auon", "aura-stl/src/"],
        &[],
        &[],
        &["Language/Examples Index"],
        r#"## Purpose

Hold the Aura standard library package as Aura source rather than Rust implementation detail.

## Current Scope

- algebraic core types such as `Option` and `Result`
- small pure helpers
- test modules beside library modules
"#,
    )
}

fn render_xtask_note(_: &RepoInventory) -> String {
    subsystem_note(
        "Xtask",
        "active",
        &["xtask/src/main.rs", "xtask/src/docs.rs"],
        &[],
        &[],
        &["Architecture/Build And Dev Workflow"],
        r#"## Purpose

Centralize automation for the workspace, including dev commands, LLVM toolchain management, and vault maintenance.

## Command Families

- `dev`
- `llvm`
- `docs`
- `qmd`
"#,
    )
}

fn render_editor_tooling_note(_: &RepoInventory) -> String {
    subsystem_note(
        "Editor Tooling",
        "active",
        &[
            "tool/aura-vscode/",
            "tool/aura-zed/",
            "tool/aura-nvim/",
            "tool/tree-sitter-aura/",
        ],
        &["Subsystems/Frontend"],
        &[],
        &["Language/Syntax And Semantics"],
        r#"## Purpose

Bundle editor-facing language support and the Tree-sitter grammar that can be reused across tools.

## Surfaces

- VS Code extension
- Zed extension
- Neovim queries and ftplugin setup
- Tree-sitter grammar and generated parser
"#,
    )
}

fn render_typecheck_contract_note(_: &RepoInventory) -> String {
    r#"---
title: "Typecheck IR"
kind: contract
tags:
  - aura
  - contract
  - typecheck
---

# Aura Typecheck IR Contract (Frozen v1)

This document defines the current checked-IR contract emitted by `crates/aura-typecheck` and consumed by backend lowering.

Status: frozen v1.

## Goals

- Provide a typed, normalized representation with minimal semantic ambiguity.
- Make coercions and casts explicit for backend lowering.
- Preserve control-flow intent in dedicated IR nodes.

## Root Structure

- `CheckedIr`
  - `declarations: Vec<CheckedDecl>`

- `CheckedDecl`
  - `name: String`
  - `ty: TyId`
  - `value: CheckedExpr`

## Expression Nodes

- Literals and atoms: `Ident`, `Int`, `Float`, `Char`, `String`, `DotIdent`, `Any`
- Collections: `List`, `Dict`
- Invocation and macro surfaces: `Call`, `BinaryOp`, `MacroApply`
- Structured control flow: `If`, `Cases`, `Return`, `Break`, `Continue`
- Structural wrappers: `Label`, `MultiArm`
- Conversion wrappers: `Coerce`, `Cast`

## Static Arguments

- `CheckedStaticArg`
- `CheckedTypeExpr`
- `CheckedStaticValue`

## Invariants (Frozen v1)

1. Every `CheckedDecl` carries a resolved `TyId`.
2. Assignment compatibility may inject `Coerce` and `Cast` wrappers.
3. `if` and `cases` lower to dedicated control-flow nodes.
4. `return`, `break`, and `continue` lower to dedicated jump nodes.
5. Core conversion decisions are centralized in the checker.

## Compatibility Policy

- New `CheckedExpr` variants are breaking in v1.
- New `BinaryOpKind` variants are breaking in v1.
- Semantic reinterpretation of existing fields is breaking.

## Related Notes

- [[Subsystems/Typecheck]]
- [[Subsystems/Codegen]]
"#
        .to_string()
}

fn render_decisions_index_note(_: &RepoInventory) -> String {
    r#"---
title: Decisions
kind: index
tags:
  - aura
  - adr
---

# Decisions

Use this folder for architecture and workflow decisions that should outlive a single chat or branch.

## Workflow

- create a new note with `cargo xtask docs new-adr --title "Decision Name"`
- set `status` to `accepted` when the decision is live
- link the ADR from the affected subsystem or architecture notes

![[Bases/Decisions.base#Decisions]]
"#
    .to_string()
}

fn render_subsystem_template_note(_: &RepoInventory) -> String {
    r#"---
title: "Subsystem Template"
kind: template
---

# {{title}}

## Purpose

Describe what this subsystem owns and what it explicitly does not own.

## Entry Points

- key file
- key type or function

## Data Flow

Describe the main inputs, transformations, and outputs.

## Testing

List the fastest commands or files to validate this subsystem.
"#
    .to_string()
}

fn render_adr_template_note(_: &RepoInventory) -> String {
    r#"---
title: "ADR Template"
kind: template
status: proposed
date: 2026-01-01
related_paths: []
related_notes: []
---

# ADR Title

## Context

## Decision

## Consequences
"#
    .to_string()
}

fn subsystem_note(
    title: &str,
    status: &str,
    source_paths: &[&str],
    depends_on: &[&str],
    related_contracts: &[&str],
    related_notes: &[&str],
    body: &str,
) -> String {
    format!(
        r#"---
title: "{title}"
kind: subsystem
status: {status}
owner: repo
source_paths:
{source_paths}
depends_on:
{depends_on}
related_contracts:
{related_contracts}
related_notes:
{related_notes}
last_reviewed: 2026-04-18
---

# {title}

{body}
"#,
        source_paths = yaml_list(source_paths, 2),
        depends_on = yaml_list(depends_on, 2),
        related_contracts = yaml_list(related_contracts, 2),
        related_notes = yaml_list(related_notes, 2),
    )
}

fn yaml_list(values: &[&str], indent: usize) -> String {
    let spaces = " ".repeat(indent);
    if values.is_empty() {
        return format!("{spaces}[]");
    }

    let mut out = String::new();
    for value in values {
        let _ = writeln!(out, r#"{spaces}- "{value}""#);
    }
    out.trim_end().to_string()
}

fn write_string(path: impl AsRef<Path>, contents: &str) -> Result<()> {
    let path = path.as_ref();
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent)
            .with_context(|| format!("failed to create '{}'", parent.display()))?;
    }
    fs::write(path, contents).with_context(|| format!("failed to write '{}'", path.display()))?;
    Ok(())
}

fn strip_generated_at_line(input: &str) -> String {
    let mut out = String::new();
    for line in input.lines() {
        if !line.trim_start().starts_with("generated_at:") {
            let _ = writeln!(out, "{line}");
        }
    }
    out
}

fn now_rfc3339() -> Result<String> {
    OffsetDateTime::now_utc()
        .format(&Rfc3339)
        .context("failed to format current timestamp")
}

fn now_date() -> Result<String> {
    Ok(OffsetDateTime::now_utc().date().to_string())
}

fn slugify(input: &str) -> String {
    let mut slug = String::new();
    let mut last_was_dash = false;
    for ch in input.chars().flat_map(char::to_lowercase) {
        if ch.is_ascii_alphanumeric() {
            slug.push(ch);
            last_was_dash = false;
        } else if !last_was_dash {
            slug.push('-');
            last_was_dash = true;
        }
    }
    slug.trim_matches('-').to_string()
}

fn describe_workspace_member(member: &str) -> &'static str {
    match member {
        "crates/aura-cli" => "CLI entry point and end-user commands.",
        "crates/aura-codegen" => "Backend and project-layout lowering.",
        "crates/aura-diagnostics" => "Shared diagnostics and issue metadata.",
        "crates/aura-frontend" => "Tokens, AST, parser, static eval, formatter.",
        "crates/aura-runtime-host" => "Runtime boundary required by native execution.",
        "crates/aura-typecheck" => "Resolver, type checker, and checked IR emitter.",
        "xtask" => "Automation commands for dev, LLVM, and docs.",
        _ => "Workspace member.",
    }
}

fn describe_directory(dir: &str) -> &'static str {
    match dir {
        ".cargo" => "Cargo aliases and workspace command configuration.",
        ".cursor" => "Editor or assistant-specific local metadata.",
        ".vscode" => "VS Code workspace settings.",
        "aura-stl" => "Aura standard library package.",
        "crates" => "Rust workspace crates.",
        "docs" => "Obsidian vault and engineering documentation.",
        "e2e" => "End-to-end fixture workspace.",
        "examples" => "Language and pipeline example programs.",
        "sandbox-e2e" => "Isolated end-to-end sandbox project.",
        "tool" => "Editor integrations and Tree-sitter grammar.",
        "xtask" => "Automation crate.",
        _ => "Repository directory.",
    }
}

fn display_rel(root: &Path, path: &Path) -> String {
    relative_path(root, path).unwrap_or_else(|_| path.display().to_string())
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::TempDir;

    #[test]
    fn parse_workspace_members_reads_explicit_members() {
        let manifest = r#"
[workspace]
members = ["crates/aura-cli", "crates/aura-frontend", "xtask"]
"#;

        let members = parse_workspace_members(manifest).expect("manifest parses");

        assert_eq!(
            members,
            vec![
                "crates/aura-cli".to_string(),
                "crates/aura-frontend".to_string(),
                "xtask".to_string()
            ]
        );
    }

    #[test]
    fn skip_rules_ignore_generated_noise() {
        assert!(should_skip_relative_path("target/debug/build.txt"));
        assert!(should_skip_relative_path("toolchains/cache/archive.tar.xz"));
        assert!(should_skip_relative_path("docs/.obsidian/workspace.json"));
        assert!(should_skip_relative_path(
            "tool/tree-sitter-aura/node_modules/pkg/index.js"
        ));
        assert!(should_skip_relative_path(".opencode"));
        assert!(should_skip_relative_path(
            ".opencode/node_modules/pkg/index.js"
        ));
        assert!(!should_skip_relative_path(
            "crates/aura-frontend/src/lib.rs"
        ));
    }

    #[test]
    fn workspace_inventory_lists_members() {
        let markdown = render_workspace_inventory(&[
            "crates/aura-cli".to_string(),
            "crates/aura-frontend".to_string(),
        ]);

        assert!(markdown.contains("crates/aura-cli"));
        assert!(markdown.contains("crates/aura-frontend"));
        assert!(markdown.contains("| Path |"));
    }

    #[test]
    fn language_scaffold_does_not_point_to_root_design_doc() {
        let inventory = RepoInventory {
            workspace_members: Vec::new(),
            top_level_directories: Vec::new(),
            example_files: Vec::new(),
            test_files: Vec::new(),
        };

        for spec in curated_note_specs()
            .into_iter()
            .filter(|spec| spec.path.starts_with("docs/Language/"))
        {
            let rendered = (spec.render)(&inventory);
            assert!(
                !rendered.contains("DESIGN.md"),
                "{} still references DESIGN.md",
                spec.path
            );
        }
    }

    #[test]
    fn strip_generated_at_line_ignores_timestamp_diffs() {
        let input = r#"---
title: Workspace Inventory
generated_at: 2026-04-18T12:30:00Z
kind: generated
---

Body
"#;

        let stripped = strip_generated_at_line(input);
        assert!(!stripped.contains("generated_at:"));
        assert!(stripped.contains("kind: generated"));
        assert!(stripped.contains("Body"));
    }

    #[test]
    fn check_requires_curated_subsystem_notes() {
        let temp = TempDir::new().expect("tempdir");
        let root = temp.path();
        fs::create_dir_all(root.join("docs/Generated")).expect("generated dir");
        fs::write(
            root.join("Cargo.toml"),
            "[workspace]\nmembers = [\"crates/aura-frontend\", \"xtask\"]\n",
        )
        .expect("manifest");
        fs::create_dir_all(root.join("crates/aura-frontend/src")).expect("crate dir");
        fs::create_dir_all(root.join("xtask/src")).expect("xtask dir");
        fs::create_dir_all(root.join("examples")).expect("examples dir");
        for (path, contents) in expected_generated_files(
            &discover_repo_inventory(root).expect("inventory"),
            "2026-04-18T00:00:00Z",
        ) {
            write_string(root.join(path), &contents).expect("write generated");
        }

        let err = check(root).expect_err("check should fail without curated notes");
        assert!(err.to_string().contains("missing curated note"));
    }

    #[test]
    fn sync_creates_docs_and_check_passes() {
        let temp = TempDir::new().expect("tempdir");
        let root = temp.path();
        fs::write(
            root.join("Cargo.toml"),
            "[workspace]\nmembers = [\"crates/aura-cli\", \"crates/aura-frontend\", \"xtask\"]\n",
        )
        .expect("manifest");
        fs::create_dir_all(root.join("crates/aura-cli/src")).expect("cli dir");
        fs::create_dir_all(root.join("crates/aura-frontend/src")).expect("frontend dir");
        fs::create_dir_all(root.join("xtask/src")).expect("xtask dir");
        fs::create_dir_all(root.join("examples")).expect("examples dir");
        fs::write(
            root.join("examples/hello_world.aura"),
            "def main() -> Void { () }\n",
        )
        .expect("example");

        sync(root).expect("sync succeeds");
        check(root).expect("check succeeds after sync");
    }
}
