# Type System / Compiler Gap Report (Issue Drafts)

Date: 2026-04-24
Repo: `nahharris/aura`
Scope reviewed: parser + typechecker + LLVM codegen + open issues `#24`-`#29`

## Quick Status Matrix

| Feature | Spec Status (`DESIGN.md`) | Impl Status | Gap Level | Blocker for #24-#29 |
|---|---|---|---|---|
| Tuples | Specified | Mostly implemented (frontend/typecheck), limited runtime lowering | Medium | No |
| Structs | Specified | Mostly implemented (frontend/typecheck), limited runtime lowering | Medium | No |
| Enums | Specified | Implemented end-to-end baseline (typecheck + enum lowering) | Low | No |
| Unions | Specified | Parsed + type-level support only, no dedicated runtime representation/dispatch | High | No |
| Interfaces | Specified | Mostly not implemented as first-class types | Critical | No (for #24-#29), Yes (for requested interface roadmap) |
| Runtime interface objects (dyn-like) | Specified direction | Not implemented | Critical | No (for #24-#29), Yes |
| Implicit Go-style method pickup | Specified | Not implemented structurally | Critical | No (for #24-#29), Yes |
| Interface bounds in static args | Specified | Partial (single named bounds only; hardcoded registry) | High | No |
| Parameterized method receivers | Requested + issue #3 | Partial (parses/checks, but no robust overload model) | High | Partial for #24 tests |
| Generic+specialized receiver overloads | Requested | Not implemented | High | No |
| Multi-overload by signature/return | Requested | Not implemented (name collision in resolver) | Critical | No |
| `Self` type in methods/interfaces | Specified examples | Not implemented as special type | High | No |
| Kotlin-like extension methods | Requested | Partial (global type-prefixed methods) | Medium | No |
| Operator interfaces (`Add`, `Index`, etc.) | Requested | Not implemented (hardcoded operator typing path) | High | No |

---

## Evidence Highlights

- Interface is heavily specified in `DESIGN.md` (`interface(...)`, implicit implementation, `Self`, default methods): `DESIGN.md:355`, `DESIGN.md:367`, `DESIGN.md:390`.
- AST has no dedicated interface type node (`TypeExpr` only `Named/Tuple/Struct/Static/InferHole`): `crates/aura-frontend/src/ast.rs:95`.
- Type interner has no `Ty::Interface` variant: `crates/aura-typecheck/src/types.rs:36`.
- Typechecker special-cases `union` and `enum`, but not `interface`: `crates/aura-typecheck/src/checker.rs:2747`, `crates/aura-typecheck/src/checker.rs:2761`.
- Interface constraints are validated against a hardcoded name registry: `crates/aura-typecheck/src/interfaces.rs:9`, `crates/aura-typecheck/src/checker.rs:3783`.
- Method table is keyed by `(receiver_ty, method_name)` with single binding (no overload set): `crates/aura-typecheck/src/checker.rs:46`, `crates/aura-typecheck/src/checker.rs:790`, `crates/aura-typecheck/src/checker.rs:794`.
- Resolver treats function names as globally unique regardless of receiver type: `crates/aura-typecheck/src/resolver.rs:46`, `crates/aura-typecheck/src/resolver.rs:67`.
- Parameterized generic receivers are expected syntactically for known generic types (`Seq[T].method` hint): `crates/aura-frontend/src/parser.rs:371`, `crates/aura-typecheck/src/checker.rs:2956`.
- LLVM lowering has dedicated enum lowering, but tuple/struct/union/interface are pointer-shaped fallback types: `crates/aura-codegen/src/llvm/types.rs:41`, `crates/aura-codegen/src/llvm/types.rs:51`.

---

## Draft Issue 1: Implement First-Class Interface Types

**Title**
`feat(types): first-class interface type representation and checking`

## Goal

Implement `interface(...)` as a first-class type in frontend/typecheck/IR, not just as a nominal string or bound name.

## Current Behavior

- `interface(...)` parses as `TypeExpr::Named { name: "interface", ... }`.
- Typechecker does not lower this into a dedicated interface type.
- No structural method-set contract is stored for user-defined interfaces.

## Scope

- Add explicit interface type nodes in type IR (`Ty::Interface` with method signatures).
- Lower `interface(...)` and aliases to that representation.
- Preserve `Any == interface()` behavior.
- Emit diagnostics for malformed/duplicate interface method signatures.

## Acceptance Criteria

- [ ] `def ToStr = interface(to_string: Func[(), String])` lowers to a first-class interface type.
- [ ] Interface method signatures are preserved in checked module metadata.
- [ ] `Any` and `interface()` are equivalent.
- [ ] Tests cover parser + typechecker + IR snapshots.

## Depends on

- None

## Blocker Analysis (#24-#29)

Not required by memory roadmap issues (`#24`-`#29`).

---

## Draft Issue 2: Structural Interface Satisfaction (Go-Style Implicit Pickup)

**Title**
`feat(typecheck): structural interface satisfaction via method sets`

## Goal

Make interface satisfaction derive from actual method availability/signatures, including implicit implementation.

## Current Behavior

- Interface bound checks use `satisfies_interface` with hardcoded type-class-like heuristics (`Eq`, `Show`, `Iterable`, etc.).
- User-defined interface aliases are not structurally checked.

## Scope

- Build method-set extraction for concrete and generic receiver types.
- Check assignability `T -> interface(...)` by method-set inclusion.
- Replace/phase out hardcoded heuristic satisfaction for user-level interfaces.

## Acceptance Criteria

- [ ] User-defined interface constraints are validated structurally.
- [ ] `implements[...]`-style guarantees can be validated against actual methods.
- [ ] Diagnostics show missing methods/signature mismatches.

## Depends on

- Draft Issue 1

## Blocker Analysis (#24-#29)

Not required for `Ref[T]/Slice[T]` or GC roadmap issues.

---

## Draft Issue 3: Runtime Interface Objects (dyn-like)

**Title**
`feat(runtime+codegen): runtime interface object representation`

## Goal

Support interface-typed runtime values (Java interface refs / Rust `dyn`-like object model).

## Current Behavior

- No interface runtime representation (`Ty::Interface` absent).
- No vtable/witness-table lowering in codegen.

## Scope

- Define ABI for interface objects (data pointer + witness/vtable pointer, or equivalent).
- Lower interface method calls through runtime-dispatch path.
- Enable interface-typed locals/params/returns safely.

## Acceptance Criteria

- [ ] `let x: ToStr = some_value` works at runtime when structurally valid.
- [ ] Interface method calls dispatch correctly.
- [ ] IR/codegen tests cover object construction and invocation.

## Depends on

- Draft Issue 1
- Draft Issue 2

## Blocker Analysis (#24-#29)

Not required for memory roadmap issues.

---

## Draft Issue 4: Interface Bounds in Static Params (Complete)

**Title**
`fix(generics): robust interface/static bound model for static params`

## Goal

Complete static-parameter bound semantics to match design:

- single interface bound (`T: Show`)
- multiple bounds (`T: (Show, Eq)`)
- static value bounds (`n: static Int`)

## Current Behavior

- Single named bounds are partially supported.
- Multiple bounds are not modeled correctly.
- Constraint interpretation currently collapses non-named bound expressions into debug-string pseudo interfaces.

## Scope

- Add explicit bound AST/model for multiple interface bounds.
- Preserve constraints in typed metadata cleanly.
- Ensure solver handles multiple interface bounds deterministically.

## Acceptance Criteria

- [ ] `def[T: (Show, Eq)] ...` parses and checks correctly.
- [ ] Multiple interface constraints all enforced.
- [ ] Solver diagnostics identify which bound failed.

## Depends on

- Draft Issue 1
- Draft Issue 2

## Blocker Analysis (#24-#29)

No direct blocker.

---

## Draft Issue 5: Method Receiver and Overload Model

**Title**
`feat(methods): receiver-aware overload sets with generic specialization`

## Goal

Support parameterized receiver methods and specialization patterns, including:

- `def[T] Foo[T].bar(...)`
- `def Foo[Int].bar(...)`

with deterministic dispatch and diagnostics.

## Current Behavior

- Receiver type expression syntax is accepted.
- Methods stored as single map entry per `(receiver_ty, method_name)`.
- No overload-set abstraction or ambiguity checks.
- Function name resolution is global and conflicts on duplicate names, even for different receivers.

## Scope

- Introduce overload sets keyed by method symbol + receiver compatibility.
- Resolve most-specific match (`Foo[Int]` before `Foo[T]` when both apply).
- Make resolver/typechecker method identity receiver-aware to avoid false duplicate-name failures.

## Acceptance Criteria

- [ ] Generic and specialized receiver overloads can coexist.
- [ ] Overload resolution is deterministic and documented.
- [ ] Ambiguous calls emit explicit diagnostics.

## Depends on

- None (can start independently)

## Blocker Analysis (#24-#29)

Partial risk for `#24`: `Ref[T]`/`Slice[T]` method surfaces need stable generic receiver behavior, but full overload specialization is not required by current acceptance criteria.

---

## Draft Issue 6: Multiple Overloads with Same Name (Function/Method)

**Title**
`feat(overload): multi-signature overloads for same symbol`

## Goal

Allow multiple callable definitions with same name and different signatures (including receiver + args + static params).

## Current Behavior

- Resolver reports duplicate symbol for repeated `def` names.
- Example like two `Int32.into` definitions with different returns cannot coexist.

## Scope

- Redesign resolver symbol table for overload groups.
- Include return type only as tie-breaker policy if explicitly desired; otherwise reject ambiguous return-only overloads.

## Acceptance Criteria

- [ ] Same-name overload groups are represented and resolved.
- [ ] Return-type-only ambiguity policy is documented and enforced.
- [ ] Existing non-overload behavior remains backward-compatible.

## Depends on

- Draft Issue 5

## Blocker Analysis (#24-#29)

No blocker.

---

## Draft Issue 7: `Self` Type Support in Method/Interface Context

**Title**
`feat(types): contextual Self type in methods and interfaces`

## Goal

Support `Self` as contextual receiver/interface type variable in declarations and signatures.

## Current Behavior

- `Self` is treated like an ordinary nominal identifier unless explicitly bound.

## Scope

- Add contextual `Self` resolution in method declarations and interface method signatures.
- Forbid invalid out-of-context `Self` usage with targeted diagnostics.

## Acceptance Criteria

- [ ] `Self` resolves to receiver type in method declarations.
- [ ] `Self` works in interface signatures and default methods.
- [ ] Out-of-context uses produce clear diagnostics.

## Depends on

- Draft Issue 1

## Blocker Analysis (#24-#29)

No blocker.

---

## Draft Issue 8: Extension Method Semantics and Namespacing

**Title**
`feat(methods): extension method coherence and namespacing`

## Goal

Formalize Kotlin-like extension method semantics over the current global type-prefixed method mechanism.

## Current Behavior

- Type-prefixed methods behave like global extensions but with limited conflict/coherence rules.

## Scope

- Define import/module coherence for extension methods.
- Define conflict resolution priority vs inherent methods.
- Add diagnostics for extension collisions.

## Acceptance Criteria

- [ ] Extension methods are resolved predictably across modules.
- [ ] Conflicts are diagnosed with actionable errors.
- [ ] Semantics documented in `DESIGN.md`.

## Depends on

- Draft Issue 5

## Blocker Analysis (#24-#29)

No blocker.

---

## Draft Issue 9: Operator Traits/Interfaces (`Add`, `Index`, ...)

**Title**
`feat(operators): interface-driven operator resolution`

## Goal

Use interfaces (e.g., `Add`, `Index`) as operator contracts instead of hardcoded operator typing rules.

## Current Behavior

- Operators are typed/lowered through dedicated builtin paths and conversion rules.
- No interface-based operator dispatch.

## Scope

- Introduce operator interfaces and mapping from syntax to method contracts.
- Keep numeric fast-paths as optimization, not language-level typing source of truth.

## Acceptance Criteria

- [ ] `+`, indexing, comparisons can be expressed via interface contracts.
- [ ] User-defined types can implement operator behavior through interfaces.
- [ ] Existing numeric behavior remains compatible.

## Depends on

- Draft Issue 1
- Draft Issue 2
- Draft Issue 5

## Blocker Analysis (#24-#29)

No blocker.

---

## 24+ Roadmap Compatibility Summary

Reviewed issues: `#24`, `#25`, `#26`, `#27`, `#28`, `#29`.

- `#24` (`Ref[T]`/`Slice[T]`) mainly needs stable generic alias + receiver method support. Current implementation is likely sufficient for baseline methods but not for advanced overload/specialization patterns.
- `#25`-`#29` (GC roadmap) are runtime/codegen memory-model phases and do not depend on interface runtime objects, operator interfaces, or advanced overload features.
- Therefore: missing features from this report are **not blockers** for completing `#24`-`#29` as currently written, with one caveat: if `#24` implementation chooses advanced method specialization/overloading patterns, receiver+overload gaps become immediate blockers.
