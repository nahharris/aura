# Aura Native Pipeline - Done Checklist

This checklist defines what "done" means for the end-to-end path from `main.aura` to `main.exe`, including architecture expectations and verification criteria.

## 0) Build Entrypoint and Toolchain

- [ ] `cargo xtask llvm run -- -p aura-cli -- build <project> --format native` is the canonical native build path.
- [ ] `xtask llvm` is the only required path for LLVM-sensitive tasks (no hidden global env dependency).
- [ ] Windows LLVM compatibility handling (including `libxml2s.lib` stub) is deterministic and documented.
- [ ] Toolchain/version mismatch errors are actionable and point to `cargo xtask llvm doctor`.
- [ ] CI covers native build invocation via xtask on supported platforms.

Verification:

- [ ] `cargo xtask llvm doctor` passes on a clean machine.
- [ ] Native build succeeds without manual environment exports.

## 1) Project Discovery and Manifest Layer

- [ ] `aura-cli build` consistently discovers `build.aura` and resolves project root.
- [ ] Binary/library project modes are correctly distinguished.
- [ ] Entrypoint resolution (`src/main.aura`) is explicit, validated, and error messages are clear.
- [ ] Manifest diagnostics include source location and remediation hints.

Verification:

- [ ] Broken/invalid manifest tests assert expected diagnostics.
- [ ] Valid binary and library fixtures build with expected behavior.

## 2) Module System and Imports

Target architecture:

- Real module resolution for `use` declarations (not ad-hoc symbol remapping).
- Namespace/member lookup driven by resolved module graph.
- Stable import semantics across project modules and vendored STL.

Checklist:

- [ ] `use` supports required syntax/features from `DESIGN.md` (including any aliasing rules once finalized).
- [ ] Resolver/typechecker consume module graph, not string-based hacks.
- [ ] `runtime.fd_write` resolves through module namespace naturally.
- [ ] Import cycles/duplicates produce deterministic diagnostics.
- [ ] Cross-module symbol visibility rules are implemented and tested.

Verification:

- [ ] Module resolution contract tests for success/failure paths.
- [ ] No special-case mapping in checker for `runtime.*` calls.

## 3) Frontend and Checked IR Contract

Target architecture:

- Parsed AST aligns with `DESIGN.md`.
- Checked IR carries enough type and symbol information for backend lowering without semantic guesswork.

Checklist:

- [ ] Function declarations in checked IR always store function type (`Ty::Func`) and never only return type.
- [ ] Main symbol normalization (`main` / lowered name) is explicit and centralized.
- [ ] Checked IR shape is versioned/contract-tested to avoid backend breakage.
- [ ] Parser tests exist for every syntax feature used in runtime/STL surface.

Verification:

- [ ] Snapshot tests for checked IR of representative programs.
- [ ] Backend smoke test fails fast if IR invariants regress.

## 4) Type System and Builtins Semantics

Target architecture:

- Builtins are typed from a single source of truth.
- No per-symbol inference hacks.
- Nominal aliases and primitive ABI types interoperate predictably.

Checklist:

- [ ] Builtin registry signatures match runtime host ABI exactly.
- [ ] `Ptr[T]` and `Slice[T]` typing rules are complete and tested.
- [ ] Result main contract is stable: `main -> Void` or `main -> Result[Void, UInt8]`.
- [ ] No ad-hoc `InferVar` hacks for specific builtins.
- [ ] Nominal/primitive compatibility rules are defined and consistently applied.

Verification:

- [ ] Unit tests for each runtime builtin signature.
- [ ] Typecheck tests for nominal `UInt8` vs primitive `UInt8` interactions.

## 5) LLVM Lowering Coverage

Target architecture:

- Lowering is expression-complete for supported language subset.
- ABI mapping is explicit and centralized.

Checklist:

- [ ] All expressions needed by STL + hello-world + control-flow samples lower without fallback hacks.
- [ ] String literal lowering produces correct memory layout and lifetime.
- [ ] Integer width/sign conversions at call boundaries are explicit and correct.
- [ ] Function declaration/call lowering agrees on parameter and return ABI.
- [ ] Unsupported forms fail with precise diagnostics (not generic "unsupported ident").

Verification:

- [ ] LLVM module verification passes for representative fixtures.
- [ ] `.ll` golden tests include call signatures for runtime/builtin calls.

## 6) Runtime ABI and Host Integration

Target architecture:

- Aura builtins call runtime host symbols directly with a stable C ABI contract.
- No temporary substitution path (`puts`/`printf`) for `rt_fd_write`.

Checklist:

- [ ] Runtime host exports all required `rt_*` symbols with stable ABI.
- [ ] Codegen emits direct calls to `rt_*` symbols for runtime builtins.
- [ ] `rt_fd_write` consumes ABI-correct parameters (fd + byte buffer contract) end-to-end.
- [ ] `rt_fd_read`, `rt_fd_open`, `rt_fd_close`, `rt_fd_seek`, memory/time/random symbols are wired.
- [ ] Error/result conventions are documented and enforced.

Verification:

- [ ] E2E tests for each wired syscall-like function.
- [ ] Platform parity checks (Windows + non-Windows where supported).

## 7) Native Entrypoint and Exit Semantics

Target architecture:

- C/OS entrypoint calls Aura user main through generated wrapper.
- Exit code follows language contract.

Checklist:

- [ ] `main` wrapper generation always targets actual lowered user function.
- [ ] `main -> Void` returns exit code `0`.
- [ ] `main -> Result[Void, UInt8]` returns `ok => 0`, `err(code) => code`.
- [ ] Wrapper behavior is tested for both accepted signatures and rejection diagnostics.

Verification:

- [ ] Integration tests assert process exit codes.
- [ ] Invalid main signatures emit `E_MAIN_SIGNATURE` reliably.

## 8) Object Emission and Link Layer

Target architecture:

- Linker invocation is platform-correct, minimal, and reproducible.
- Runtime/static libs are linked with required CRT/system dependencies.

Checklist:

- [ ] `--format obj` emits valid object files for supported targets.
- [ ] `--format native` links successfully without manual flag edits.
- [ ] Windows link flags/libraries are centralized and documented.
- [ ] Intermediate artifact policy is explicit (keep/remove, debug vs release).

Verification:

- [ ] Link step tested in CI for `native` on Windows.
- [ ] No unresolved externals for runtime host path.

## 9) STL Build Strategy

Target architecture:

- Vendored STL compilation is first-class and uses the same backend path as user modules.

Checklist:

- [ ] STL modules emit true LLVM IR/object output when required (not checked-IR text placeholders).
- [ ] STL cache invalidation is deterministic.
- [ ] STL/runtime API surface is parser-valid, typed, and documented.
- [ ] Source-of-truth between `aura-stl` and vendored copies is clearly defined.

Verification:

- [ ] Build uses cached STL outputs when valid and rebuilds when stale.
- [ ] Tests confirm no drift between canonical STL and vendored snapshot workflow.

## 10) CLI Format Contract

Checklist:

- [ ] Supported formats are exactly: `native` (default), `auir`, `ll`, `obj`.
- [ ] Behavior for each format is documented and stable.
- [ ] `ll` always means LLVM IR (no fallback to checked IR text).
- [ ] Error messaging distinguishes parse/typecheck/codegen/link failures.

Verification:

- [ ] CLI integration tests per format.
- [ ] README examples stay in sync with actual behavior.

## 11) Diagnostics, Docs, and Developer Experience

Checklist:

- [ ] Diagnostics include code, stage, span, and fix hint where possible.
- [ ] `README.md` and `AGENTS.md` reflect canonical workflow and caveats.
- [ ] Known limitations and temporary shims are documented and tracked.
- [ ] Generated artifacts are ignored or managed to keep workspace clean.

Verification:

- [ ] `cargo xtask dev qa` passes.
- [ ] Fresh contributor can build/run sandbox e2e from docs alone.

## 12) Required E2E Gate (Definition of Done)

The pipeline is considered done only when all checks below are true:

- [ ] `sandbox-e2e/src/main.aura` using `runtime.fd_write` builds via `--format native`.
- [ ] Running `sandbox-e2e/src/main.exe` prints `hello world`.
- [ ] Output path uses real `rt_fd_write` ABI, not temporary CRT fallback.
- [ ] Additional runtime functions (read/open/close/seek/mem/time/random) are callable and tested.
- [ ] No temporary checker/codegen hacks remain for this path.
- [ ] CI enforces the above as non-optional regression gates.

## Current Status Snapshot (Apr 2026)

- [x] Native `sandbox-e2e` executable can be produced and run.
- [x] `runtime.fd_write` source path can print `hello world` in e2e flow.
- [ ] Runtime ABI is fully clean and direct (current implementation still uses temporary lowering fallback for write path).
- [ ] Full runtime syscall surface is wired and verified end-to-end.
- [ ] STL LLVM emission path is fully canonical for native/ll output.
