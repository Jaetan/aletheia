# Atomic stepEval Bug Fix - Decision Record

**Date**: 2025-12-22
**Status**: APPROVED - To be implemented next session
**Impact**: Critical - blocks Group D equivalence proofs

---

## Problem Statement

`stepEval` for Atomic predicates returns `Continue AtomicState` on success instead of `Satisfied`. This causes semantic mismatch with `checkIncremental`:

**Current behavior:**
- `runStepEval (Atomic p) [f1, f2]` checks p on ALL frames (p f1 ∧ p f2)
- `checkIncremental [f1, f2] (Atomic p)` checks p on FIRST frame only (p f1)

**Impact:** Property-specific equivalence proofs cannot be completed.

---

## Root Cause

**File**: `src/Aletheia/LTL/Incremental.agda`
**Line**: 123

```agda
stepEval (Atomic p) eval AtomicState prev curr =
  if eval prev curr p
  then Continue AtomicState  -- ❌ BUG: Should be Satisfied
  else Violated (mkCounterexample curr "atomic predicate failed")
```

---

## Solution

Change line 123 to return `Satisfied` instead of `Continue`:

```agda
stepEval (Atomic p) eval AtomicState prev curr =
  if eval prev curr p
  then Satisfied  -- ✅ CORRECT: Atomic evaluated, done
  else Violated (mkCounterexample curr "atomic predicate failed")
```

---

## Rationale

**LTL Semantics:**
- Atomic propositions evaluate at a single time point (frame 0)
- Once checked, there's nothing more to evaluate
- This is standard LTL semantics for atomic formulas

**Impact on runStepEval:**
- When `stepEval` returns `Satisfied`, `runStepEval` stops immediately and returns `true`
- This matches `checkIncremental` behavior (checks only first frame)

**Impact on Temporal Operators:**

All temporal operators correctly handle `Satisfied` from inner formulas:

1. **Always (Atomic p)**:
   ```agda
   stepEval (Always φ) eval (AlwaysState st) prev curr
     with stepEval φ eval st prev curr
   ... | Satisfied = Continue (AlwaysState st)  -- ✓ Keeps checking next frame
   ```

2. **Eventually (Atomic p)**:
   ```agda
   stepEval (Eventually φ) eval (EventuallyState st) prev curr
     with stepEval φ eval st prev curr
   ... | Satisfied = Satisfied  -- ✓ Property satisfied, done
   ```

3. **Not (Atomic p)**:
   ```agda
   stepEval (Not φ) eval (NotState st) prev curr
     with stepEval φ eval st prev curr
   ... | Satisfied = Violated (...)  -- ✓ Negation fails when inner succeeds
   ```

**Conclusion:** Fix is safe and correct for all use cases.

---

## Validation Plan

1. **Apply fix** to `Incremental.agda` line 123
2. **Type-check** Incremental.agda: `agda +RTS -N32 -RTS Aletheia/LTL/Incremental.agda`
3. **Type-check** dependent modules (StreamState, Main, etc.)
4. **Run tests** (if any Agda tests exist)
5. **Remove postulate** from Properties.agda
6. **Complete proof** for Atomic multi-frame case (should now be trivial)
7. **Type-check** Properties.agda
8. **Commit** with message: `fix(LTL): Atomic stepEval should return Satisfied not Continue`

---

## Next Session Checklist

- [ ] Apply one-line fix to Incremental.agda:123
- [ ] Type-check Incremental.agda (verify no breakage)
- [ ] Type-check StreamState.agda (uses stepEval)
- [ ] Type-check Main.agda (uses streaming protocol)
- [ ] Remove postulate from Properties.agda:983-992
- [ ] Complete Atomic proof for multi-frame case
- [ ] Type-check Properties.agda
- [ ] Commit fix
- [ ] Continue with Phase 2 (Not, And, Or, Next)

---

## References

- **Session state**: `.session-state.md`
- **Plan**: `~/.claude/plans/stateless-napping-narwhal.md`
- **Properties file**: `src/Aletheia/LTL/Properties.agda` (lines 977-992)
- **Incremental file**: `src/Aletheia/LTL/Incremental.agda` (line 123)
