# Panic System Gap Report

Date: 2026-04-24
Repo: `nahharris/aura`

## Quick Status Matrix

| Feature | Spec Status (`DESIGN.md`) | Impl Status | Gap Level |
|---|---|---|---|
| User-accessible `panic` builtin | Specified (`!!` operator) | Not implemented | Critical |
| `catch`/`recover` syntax | Not specified | Not implemented | Critical |
| Panic unwinding (LLVM personality) | Not implemented | Not implemented | Critical |
| Custom panic handlers (`set_hook`) | Not specified | Not implemented | High |
| `Bytes` bounds check panic | Specified (DESIGN.md:1412) | UB until handlers exist | High |
| Panic payload type (`.Str`, `.Custom`) | Not specified | Not implemented | High |

---

## Current State

The compiler currently uses `panic!` internally for invariant violations in parser and typechecker, but **there is no user-accessible panic mechanism**:

### What Exists
- `!!` operator - documented in DESIGN.md as panicking unwrap for Option/Result (line 812)
- Fallible destructuring patterns (`.ok(v)`, `Coord(x, y)`) - panics at runtime on mismatch (lines 437-441)
- `Bytes.get`/`set` - documented as **undefined behavior** until panic handlers exist (`docs/Subsystems/Runtime Host.md:54`)

### What's Missing
- No user-callable `panic` function/macro
- No `catch`/`except` mechanism to recover from panics
- No panic handler registration (`std::panic::set_hook`)
- No panic payload/message support
- No unwinding infrastructure across FFI boundaries

---

## Draft Issue 1: Core Panic Infrastructure

**Title**
`feat(runtime): user-accessible panic mechanism`

## Goal

Implement a Rust-like panic system that allows users to trigger panics, catch/recover from them, and register custom panic handlers.

## Scope

### Phase 1: Core Panic Infrastructure

1. **Panic builtin** - Add a `panic[message]` builtin or macro:
   ```aura
   panic "something went wrong"
   ```

2. **Panic payload** - Define panic payload as an enum:
   ```aura
   enum Panic = .Str(String) | .Custom(Dict)
   ```

3. **Panic unwinding** - Implement stack unwinding with LLVM personality functions:
   - Use `llvm.eh.something` intrinsics
   - Handle unwinding across Aura code boundaries

### Phase 2: Recovery Mechanism

4. **Catch/Recover** - Add `catch` expression syntax:
   ```aura
   let result = catch some_fallible_operation() {
       "fallback on panic"
   }
   
   let val = catch do_something() else { "default" }
   ```

5. **Result integration** - `Result` should have `.unwrap()` that panics with the error:
   ```aura
   maybe_err.unwrap()
   maybe_err.unwrap_or(42)
   maybe_err.expect("msg")
   ```

### Phase 3: Custom Handlers

6. **Panic hook** - Implement `std::panic::set_hook`:
   ```aura
   std::panic::set_hook({ msg =>
       io::eprintln("PANIC: {}", msg)
       sys::exit(1)
   })
   ```

7. **CatchUnwind** trait - Allow capturing panic payloads:
   ```aura
   enum CatchResult<T> = .Ok(T) | .Panic(Panic)

   std::panic::catch({ => do_something() })
   ```

### Phase 4: STL Integration

8. **std::panic module** - Expose in Aura STL:
   - `pub def panic: Func[(msg: String), Never]`
   - `pub def catch: Func[f: Func[] -> T, ] -> CatchResult<T>`
   - `pub def set_hook: Func[hook: Func[Panic], Void]`

9. **Update Bytes bounds checking** - Once handlers exist:
   - `Bytes.get(index)` should panic on OOB
   - `Bytes.set(index, val)` should panic on OOB

## Acceptance Criteria

- [ ] User can call `panic "message"` from Aura source
- [ ] `catch` expression recovers from panics
- [ ] `std::panic::set_hook` registers custom handlers
- [ ] `Bytes.get`/`set` panics on OOB (defined behavior)
- [ ] Tests cover panic triggering and recovery
- [ ] LLVM unwinding integration works

## Implementation Hints

- LLVM personality functions: Use `llvm.eh.something` intrinsics
- Test mode: The LLVM backend plan already mentions `panic` builtin for test mode (item 6.4 in `LLVM_BACKEND_IMPLEMENTATION_PLAN.md`)
- Consider Rust interop: If Aura embeds Rust code later, need `resume_unwind` across FFI

## References

- DESIGN.md: Lines 288, 318, 437-441, 812, 1209, 1412
- `docs/Subsystems/Runtime Host.md:54`
- LLVM Backend Implementation Plan: item 6.4
- Rust's `std::panic` module for comparison