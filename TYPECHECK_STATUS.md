# Aura Typechecker Status

This report tracks current implementation status against the 4 remaining phases before LLVM backend handoff.

Last updated: 2026-04-03 (build mode, latest: parser/call-shape hardening, static-only top-level enforcement, macro finality checks)

## 1) Deep inference + unification

Status: ✅ Phase 1 complete (baseline scope)

### Partially done
- ✅ Infer vars, substitutions, unifier, occurs-check
- ✅ Call-shape inference scaffold
- ✅ Basic env tracking for identifiers/functions
- ✅ Function/macro return compatibility checks against declared type expressions
- ✅ Multi-arm result join checks for body compatibility
- ✅ Identifier resolution in type inference now emits explicit unresolved diagnostics
- ✅ Closure typing/lowering baseline added (typed function shape)
- ✅ Builtin macro typing now returns concrete function types from registry
- ✅ Dot-ident no-payload typing now defaults to `Void` (instead of broad `Any`)
- ✅ Nested value-scope environment baseline added for function/macro parameter visibility and non-leaking locals
- ✅ Error/fallback paths now prefer fresh inference variables over immediate `Any` in core checker flows
- ✅ Generic container type-expression argument resolution tightened (missing/wrong-kind args now emit explicit diagnostics instead of defaulting silently)
- ✅ Type constructor static arguments now enforce exact arity (no extra/no missing args)
- ✅ Multi-arm parser/checker now supports optional pattern side (`->`) and optional guards (`~ expr`) with guard bool-check typing
- ✅ Generic declarations now resolve static params as dedicated generic type params (`Ty::GenericParam`) within function scope
- ✅ Generic call static-arg arity now enforces exact match (missing or extra both diagnosed)
- ✅ Baseline constraint collection/solve pass added (equality + assignability constraints solved per declaration boundary)
- ✅ Function generic parameters now use constrained static-param metadata (same shape as macro static params)
- ✅ Constraint solver path now includes baseline generic interface/static bound constraints

### Left
- ✅ Full bidirectional inference baseline for current frontend expression set (returns/call args, branch arms/joins, labels, dot payloads, expected-container propagation)
- ✅ Proper scoped env baseline for current frontend forms (function/macro params + per-arm binders + guard typing)
- ✅ Generic type variable instantiation + unification baseline end-to-end for named generic functions
- ✅ Generic call static-arg policy supports all-or-none explicit args with omitted-args inference
- ✅ `_` infer-hole support added in type expressions and explicit static call arguments
- ✅ Constraint solving beyond equality/assignability basics (baseline interface/static bound integration complete in solver path with diagnostics and tests)

### Remaining beyond Phase 1
- 🔶 Richer constraint graph/entailment for advanced generic/interface reasoning (higher-order or transitive bound logic)
- 🔶 Stronger bound entailment + cross-constraint propagation for deep generic ecosystems

---

## 2) Widening enforcement everywhere

### Partially done
- ✅ Widening matrix exists and is used in key assignability paths
- ✅ Some IR-level coercion/cast decisions are emitted
- ✅ Operator macro typing path exists for `add/sub/mul/div`
- ✅ Branch-join and function/macro return compatibility checks are present
- ✅ `cast` macro lowers to explicit typed `Cast` IR node
- ✅ `if/cases/return/break/continue` macro surfaces typecheck and lower to dedicated IR nodes
- ✅ Reduced core-path `Any` fallthrough by adding typed closure lowering and unresolved identifier diagnostics
- ✅ Untyped macro usage now hard-fails (`E_MACRO_UNTYPED`) instead of warning-only fallback
- ✅ Central conversion decision engine now drives assignability checks, branch joins, and IR coercion decisions on core paths
- ✅ Reassignment compatibility now uses the same conversion pipeline as call/return/joins
- ✅ Explicit `cast` macro typing now routes through the same centralized conversion decision engine (explicit-cast mode)

### Left
- ✅ Uniform coercion API applied to all current core contexts:
  - ✅ operators (macro operator family now covers arithmetic/comparison/equality/logical through unified conversion path)
  - ✅ call arguments (all core checked paths)
  - ✅ branch joins (all current `if`/`cases`/`multi-arm` paths)
  - ✅ return-flow joins (function/macro returns + reassignment surfaces)
- ✅ Explicit parsed cast expression lowering into typed cast IR consistently across non-macro surfaces
- ✅ Eliminate ad-hoc type compatibility checks in core checker conversion paths (residual non-core fallthrough cleanup tracked as post-phase hardening)

Status: ✅ Phase 2 complete (baseline scope)

---

## 3) Obligation tracing + elite diagnostics

Status: ✅ Phase 3 complete (baseline scope)

### Partially done
- ✅ Related labels + obligation stack plumbing
- ✅ Obligation context appears on some mismatch/unify diagnostics
- ✅ Shared diagnostics crate introduced (`crates/aura-diagnostics`) and adopted by lexer/parser/typecheck stages
- ✅ Frontend lex/parse now emit shared diagnostics model with stage tagging
- ✅ Typechecker/resolver now emit shared diagnostics model (local diagnostics module removed)
- ✅ Constraint-solver-originated diagnostics now preserve deep obligation chains captured at emit-site context

### Left
- ✅ Full obligation chains for interface/generic/static failures (deep traces preserved through solver constraints and covered by snapshot tests)
- ✅ Consistent primary/secondary diagnostic context strategy across checker errors (stage tagging + related labels baseline standardized)
- ✅ Snapshot/golden diagnostics suite baseline for major failure classes (cross-stage harness added with frontend lexer/parser and typecheck mismatch/operator/cast/generic-bound snapshots)

### Remaining beyond Phase 3
- 🔶 Precise source-span propagation for checker diagnostics (typed AST currently lacks full expression-level span carriage; current baseline uses standardized related-label fallback context)

---

## 4) Checked IR contract freeze (LLVM handoff)

Status: ✅ Phase 4 complete (frozen v1 baseline)

### Partially done
- ✅ Checked IR exists and now includes more expression forms
- ✅ Coerce/Cast nodes introduced
- ✅ Control-flow nodes added (`If`, `Cases`, `Return`, `Break`, `Continue`)
- ✅ Draft checked-IR contract doc added: `docs/typecheck-ir.md`
- ✅ Macro static args are preserved in IR macro-apply nodes

### Left
- ✅ Freeze schema with backend-oriented invariants and compatibility policy (`docs/typecheck-ir.md` frozen v1)
- ✅ Typed operator nodes added and operator macro family lowers to typed IR (`BinaryOp` + `BinaryOpKind`)
- ✅ Ensure semantically-checked core operator/control-flow forms lower without `Any` fallback (contract tests added)
- ✅ Final contract validation pass for LLVM consumer assumptions (workspace + IR contract snapshots)

### Remaining beyond Phase 4
- ✅ Structural typed static-arg IR (`CheckedStaticArg` now uses typed structural forms)

### Remaining beyond current hardening pass
- 🔶 Precise expression-level source-span carriage through typed AST for checker diagnostics (current baseline uses standardized related-context fallback where spans are unavailable)
- 🔶 Richer advanced constraint entailment/propagation beyond current baseline multi-pass solver model

---

## Update Log

- `c31991d` unification core + call inference scaffold.
- `013e0fe` obligation traces + occurs-check + coercion/cast IR contract extension.
- `936154f` broader IR lowering and coercion/cast decision coverage.
- `48b7589` function/macro return checking + multi-arm result checks.
- `5c31cc9` numeric operator macro typing + richer IR macro static args.
- `8e2b9db` `if/cases` typing + control-flow IR nodes.
- `8f77fbb` `return/break/continue` control-flow IR lowering.
- `00c1338` explicit `cast` macro IR lowering + jump macro typing paths.
- `8e2b9db` + `8f77fbb` + `00c1338` + `5c31cc9` together expanded control-flow/operator/cast IR semantics.
- `docs/typecheck-ir.md` added as backend-facing IR contract draft.
- `8f77fbb` + `00c1338` + follow-ups: jump macros + explicit cast IR + control-flow normalization expanded.
- Current pass: unresolved identifier diagnostics + closure typed lowering baseline added.
- Current pass: unresolved identifiers downgraded to warnings for build continuity while still reducing silent `Any` fallthrough.
- Current pass: additional `Any` reduction via typed builtin macro resolution and dot-ident default typing.
- Current pass: introduced stacked value environment scopes and tests for function parameter visibility + no scope leakage.
- Current pass: multi-arm/cases pattern identifiers now bind within arm-local scopes with no outward leakage.
- Current pass: unifier now structurally handles `Func`, `Tuple`, `Struct`, `Set`, and `Array` (with arity/shape checks).
- Current pass: call-site static argument instantiation baseline added for named generic functions, with diagnostics for unsupported/unexpected static call args.
- Current pass: added expected-type-driven inference entrypoint for key contexts (returns/call args), reducing `Any` fallback in empty collection and closure return inference paths.
- Current pass: expected container typing now applies to non-empty list/dict literals under expected types, catching element/entry mismatches earlier.
- Current pass: expected-type propagation widened to calls/labels/dot-payload paths to reduce latent fallback and improve nested inference stability.
- Current pass: removed residual `CheckedExpr::Any` fallback in malformed `if/cases` lowering by preserving macro-apply fallback IR shape.
- Current pass: replaced major `Ty::Any` error fallback sites with fresh infer vars (`unknown_ty`) to reduce eager top-typing and keep constraints informative.
- Current pass: `List/Dict/Set/Array/Func` type-expression arg parsing now reports explicit missing/kind errors (`E_TYPE_ARG_MISSING`, `E_TYPE_ARG_KIND`, `E_ARRAY_SIZE_*`) with strict argument expectations.
- Current pass: added exact static-arg arity diagnostics (`E_TYPE_ARG_ARITY`) across primitive and container type constructors.
- Current pass: generic call arity now allows omitted static args (full inference) while rejecting partial explicit lists; explicit `_` slots participate in inference.
- Current pass: parser now enforces static-only top-level declarations (`def`/`defmacro`/`use`) to align with compiled-module semantics.
- Current pass: call parser supports labeled trailing closure forms across function and method calls; unlabeled trailing closure stays macro-application surface.
- Current pass: binary operator AST parsing now includes `:` as expression/type binary operator with precedence handling.
- Current pass: `if`/`cases` moved to inline-function call typing path; macro-form usage is now diagnosed as invalid form.
- Current pass: macro symbols treated as final/non-shadowable during parse; function/static declarations cannot reuse macro symbol names.
