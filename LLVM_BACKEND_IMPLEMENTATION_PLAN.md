# LLVM Backend Implementation Plan

This plan is executed in strict order: each step is completed in full before moving to the next step.

## Phase 1 - Project Infrastructure

- [x] 1.1 Define `build.aura` manifest schema in `DESIGN.md` using Aura syntax
- [x] 1.2 Create new `crates/aura-codegen` crate and add it to workspace
- [x] 1.3 Implement project discovery (`build.aura` root, `src/`, `vendor/`, `target/`)
- [x] 1.4 Implement manifest parsing and validation in code
- [x] 1.5 Extend CLI with project-aware `build` flow (no codegen yet)
- [x] 1.6 Add `aura init` to scaffold project layout and vendor STL

## Phase 2 - STL Strategy and Packaging

- [ ] 2.1 Replace current STL surface with a minimal, coherent STL design
- [ ] 2.2 Define minimal runtime boundary (syscalls + core memory helpers only)
- [ ] 2.3 Vendor STL during `aura init`
- [ ] 2.4 Compile vendored STL per project and cache build artifacts in `target/`

## Phase 3 - LLVM Backend Foundation

- [ ] 3.1 Initialize LLVM backend infrastructure with `inkwell` (latest stable LLVM)
- [ ] 3.2 Implement type lowering from Aura checked types to LLVM types
- [ ] 3.3 Implement declaration and function lowering skeleton
- [ ] 3.4 Implement expression lowering for core literals, identifiers, calls, binary ops

## Phase 4 - Runtime and Builtins

- [ ] 4.1 Implement minimal syscall wrapper layer in Rust (host target first)
- [ ] 4.2 Expose only minimal builtins needed for STL implementation
- [ ] 4.3 Implement UTF-8 `String` representation from day one
- [ ] 4.4 Move `io_write` and similar high-level behavior into Aura STL on top of minimal builtins

## Phase 5 - Emission Pipeline

- [ ] 5.1 Emit LLVM textual IR (`.ll`)
- [ ] 5.2 Emit object files (`.o`)
- [ ] 5.3 Link native executable
- [ ] 5.4 Wire full CLI pipeline: `.ll` -> `.o` -> native

## Phase 6 - Test System

- [ ] 6.1 Add Aura `test` macro surface (Aura syntax, not Rust attributes)
- [ ] 6.2 Support paired module test files (`x.aura` + `x.test.aura`) in same module namespace
- [ ] 6.3 Exclude `.test.aura` from production builds
- [ ] 6.4 Add builtin testing macros (`assert`, `assert_eq`, `panic`) for test mode
- [ ] 6.5 Implement `aura test` discovery, compile, and execution pipeline

## Phase 7 - TDD and Deep Validation

- [ ] 7.1 Add unit tests per lowering component (types, exprs, functions)
- [ ] 7.2 Add integration tests for project builds and dependency resolution
- [ ] 7.3 Add LLVM IR snapshot tests
- [ ] 7.4 Add end-to-end executable tests
- [ ] 7.5 Add regression fixtures for STL and test-macro behavior
