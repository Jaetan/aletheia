# Bug Fix: Not Operator in Incremental Checker

**Date**: 2025-12-25
**Discovered by**: Coinductive proof attempt for Phase 3.2 (Propositional Operators)
**Status**: FIXED and PROVEN

## The Bug

In `src/Aletheia/LTL/Incremental.agda` line 131, the `Not` operator incorrectly returned `Continue` when the inner formula returned `Violated`:

```agda
-- BEFORE (incorrect):
... | Violated _ = Continue (NotState st)  -- Inner violated = outer continues (¬false = true)

-- AFTER (correct):
... | Violated _ = Satisfied  -- Inner violated = outer satisfied (¬false = true)
```

## Why It Was Wrong

**Semantic Mismatch**:
- Comment correctly stated: "¬false = true"
- But code returned `Continue` (meaning "not decided yet")
- Should return `Satisfied` (meaning "decided true")

**Behavioral Impact**:
- For `Not (Atomic p)` where `p f = false`:
  - Incremental checker with bug: returned `Continue`, kept processing subsequent frames
  - Coinductive checker: returned `now true` immediately
  - **Mismatch**: Incremental checker continued unnecessarily when it should have terminated

**Concrete Example**:
```agda
-- Input: Not (Atomic (λ _ → false)) on trace [f1, f2]
-- Coinductive: later (λ .force → now true)          -- one delay layer
-- Incremental:  later (λ .force → later (...))      -- two delay layers (BUG!)
-- These are NOT bisimilar!
```

## How the Proof Exposed It

When proving:
```agda
not-atomic-fold-equiv : ∀ (p : TimedFrame → Bool) (trace : Colist TimedFrame ∞)
  → ∞ ⊢ foldStepEval (Not (Atomic p)) trace ≈ checkColist (Not (Atomic p)) trace
```

The proof helper function attempted to show:
```agda
not-atomic-go-equiv p f rest with p f
... | false = {!!}  -- Goal: prove both sides bisimilar
```

When tracing through the false case:
- `checkColist` evaluation: `Delay.map not (now (p f))` = `now (not (p f))` = `now true`
- `foldStepEval-go` with buggy stepEval:
  1. stepEval (Atomic p) returns Violated (p f = false)
  2. stepEval (Not ...) returns Continue (BUG!)
  3. foldStepEval-go with Continue and non-empty rest: later (recurse)
  4. Result has extra delay layer!

Attempted proof of bisimilarity failed because the structures were fundamentally different.

## Investigation Process

1. **Attempted proof** - pattern matched on `p f`, tried `DB.now refl` for false case
2. **Type error** - Agda couldn't unify the two delay structures
3. **Traced both implementations** - found extra `later` in foldStepEval
4. **Identified root cause** - Continue when should be Satisfied
5. **Checked comment** - comment said "¬false = true" confirming the bug
6. **Applied fix** - changed Continue to Satisfied
7. **Proof succeeded** - `DB.now refl` now works!

## The Fix

Changed line 131 in `src/Aletheia/LTL/Incremental.agda`:

```diff
 stepEval (Not φ) eval (NotState st) prev curr
   with stepEval φ eval st prev curr
 ... | Continue st' = Continue (NotState st')
-... | Violated _ = Continue (NotState st)  -- Inner violated = outer continues (¬false = true)
+... | Violated _ = Satisfied  -- Inner violated = outer satisfied (¬false = true)
 ... | Satisfied = Violated (mkCounterexample curr "negation failed (inner satisfied)")
```

## Correctness Verification

**Temporal Operator Compatibility**:

1. **Always (Not (Atomic p))**:
   - When Not returns Satisfied: Always sees success on this frame
   - Always line 176: `... | Satisfied = Continue (AlwaysState st)`
   - Continues checking next frame ✓ CORRECT

2. **Eventually (Not (Atomic p))**:
   - When Not returns Satisfied: Eventually succeeds
   - Eventually line 185: `... | Satisfied = Satisfied`
   - Returns satisfied ✓ CORRECT

3. **And/Or with Not**:
   - And/Or handle Satisfied correctly (short-circuit logic)
   - No issues ✓ CORRECT

**Proof Success**:

With the fix applied, the proof completed without postulates:

```agda
not-atomic-go-equiv : ∀ (p : TimedFrame → Bool) (f : TimedFrame) (rest : Colist TimedFrame ∞)
  → ∞ ⊢ foldStepEval-go (Not (Atomic p)) (NotState AtomicState) nothing f rest ≈ now (not (p f))
not-atomic-go-equiv p f rest with p f
... | true = DB.now refl  -- Both sides reduce to 'now false'
... | false = DB.now refl  -- Both sides reduce to 'now true' (NOW WORKS!)

not-atomic-fold-equiv : ∀ (p : TimedFrame → Bool) (trace : Colist TimedFrame ∞)
  → ∞ ⊢ foldStepEval (Not (Atomic p)) trace ≈ checkColist (Not (Atomic p)) trace
not-atomic-fold-equiv p [] = DB.now refl
not-atomic-fold-equiv p (f ∷ rest) = DB.later λ where .force → not-atomic-go-equiv p f (rest .force)
```

**Type-checking**: Both fixes and proofs verified successfully with `agda +RTS -N32 -RTS`.

## Lesson Learned

**Value of Formal Verification**:
- The proof process exposed a subtle semantic bug
- Comment indicated the developer knew the correct semantics ("¬false = true")
- But implementation had wrong return value (Continue vs Satisfied)
- Testing might have missed this (tests might only check final result, not intermediate states)
- **Formal proof made the bug impossible to ignore**

This validates the Phase 3 approach: proving properties discovers bugs and ensures correctness.

## Impact Assessment

**Severity**: Medium
- Bug only affected `Not` operator when inner formula was Violated
- Most commonly occurs with `Not (Atomic p)` when predicate is false
- Would cause unnecessary continuation instead of immediate termination
- Could affect performance (extra frame processing) and semantics (wrong delay structure)

**Scope**: Limited
- Only affects `Not` operator behavior
- `And`, `Or`, temporal operators were already correct
- Coinductive checker (`checkColist`) had correct semantics all along
- Bug was isolated to incremental checker's `stepEval`

**Risk of Fix**: Low
- One-line change
- All temporal operators handle Satisfied correctly
- Type-checking verified fix doesn't break anything
- Proof now succeeds, confirming correctness

## Files Modified

1. **src/Aletheia/LTL/Incremental.agda** (line 131)
   - Changed: `Continue (NotState st)` → `Satisfied`

2. **src/Aletheia/LTL/Properties.agda** (lines 155-175)
   - Added: `not-atomic-go-equiv` proof
   - Added: `not-atomic-fold-equiv` proof
   - Result: NO POSTULATES, fully proven!

## Next Steps

**Immediate** (Phase 3.2 continuation):
- ✅ Not (Atomic p) - PROVEN
- ⏸️ And (Atomic p) (Atomic q) - TODO
- ⏸️ Or (Atomic p) (Atomic q) - TODO

**Future** (Phase 3.3):
- Temporal operators (Next, Always, Eventually, Until, EventuallyWithin, AlwaysWithin)
- Will require more sophisticated coinductive techniques
- Deferred as planned

**Integration**:
- Run Python tests to verify no regression
- Update PROJECT_STATUS.md with Phase 3.2 progress
- Commit with descriptive message documenting both bug fix and proof

## References

- **Session state**: `.session-state.md`
- **Detailed plan**: `~/.claude/plans/coinductive-proof-strategy.md`
- **Current position**: `~/.claude/plans/CURRENT_POSITION.md`
- **Properties file**: `src/Aletheia/LTL/Properties.agda`
- **Incremental file**: `src/Aletheia/LTL/Incremental.agda`
- **Coinductive file**: `src/Aletheia/LTL/Coinductive.agda`
