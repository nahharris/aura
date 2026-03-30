# Aura Typechecker Status

This report tracks current implementation status against the 4 remaining phases before LLVM backend handoff.

Last updated: 2026-03-30 (build mode, latest: cast/jump/control-flow normalization)

## 1) Deep inference + unification

### Partially done
- ✅ Infer vars, substitutions, unifier, occurs-check
- ✅ Call-shape inference scaffold
- ✅ Basic env tracking for identifiers/functions
- ✅ Function/macro return compatibility checks against declared type expressions
- ✅ Multi-arm result join checks for body compatibility

### Left
- ❌ Full bidirectional inference across all expression forms (not just current subset)
- ❌ Proper local scope/type env for nested blocks/closures/arms
- ❌ Generic type variable instantiation + unification flow end-to-end
- ❌ Constraint solving beyond equality/assignability basics (e.g., richer constraint graph)

---

## 2) Widening enforcement everywhere

### Partially done
- ✅ Widening matrix exists and is used in key assignability paths
- ✅ Some IR-level coercion/cast decisions are emitted
- ✅ Operator macro typing path exists for `add/sub/mul/div`
- ✅ Branch-join and function/macro return compatibility checks are present
- ✅ `cast` macro lowers to explicit typed `Cast` IR node
- ✅ `if/cases/return/break/continue` macro surfaces typecheck and lower to dedicated IR nodes

### Left
- ❌ Uniform coercion API applied to all contexts:
  - operators (currently partial, macro-path only)
  - call arguments (all paths)
  - branch joins (all paths)
  - return-flow joins (all paths)
- ❌ Explicit parsed cast expression lowering into typed cast IR consistently (currently `cast` macro path)
- ❌ Eliminate remaining ad-hoc type compatibility checks

---

## 3) Obligation tracing + elite diagnostics

### Partially done
- ✅ Related labels + obligation stack plumbing
- ✅ Obligation context appears on some mismatch/unify diagnostics

### Left
- ❌ Full obligation chains for interface/generic/static failures (deep traces)
- ❌ Consistent primary/secondary span strategy across all checker errors
- ❌ Snapshot/golden diagnostics suite for all major failure classes

---

## 4) Checked IR contract freeze (LLVM handoff)

### Partially done
- ✅ Checked IR exists and now includes more expression forms
- ✅ Coerce/Cast nodes introduced
- ✅ Control-flow nodes added (`If`, `Cases`, `Return`, `Break`, `Continue`)
- ✅ Draft checked-IR contract doc added: `docs/typecheck-ir.md`
- ✅ Macro static args are preserved in IR macro-apply nodes

### Left
- ❌ Freeze schema with backend-oriented invariants (draft exists; formal freeze + compatibility policy pending)
- ❌ Add remaining typed operator/control-flow nodes needed by backend (beyond current macro-surface coverage)
- ❌ Ensure all semantically-checked forms lower to IR (no `Any` fallthrough in core paths)
- ❌ Final contract validation pass for LLVM consumer assumptions

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
