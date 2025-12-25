# Or Operator Bug Fix

**Date**: 2025-12-26
**Type**: Semantic Bug (Incorrect Temporal Behavior)
**Severity**: Medium
**Status**: ✅ FIXED

## Bug Description

The Or operator in `Aletheia.LTL.Coinductive` exhibited incorrect temporal behavior instead of standard propositional logic semantics.

**Buggy code** (Coinductive.agda lines 126-131):
```agda
go (Or ψ₁ ψ₂) frame [] = now (evalAtFrame frame ψ₁ ∨ evalAtFrame frame ψ₂)
go (Or ψ₁ ψ₂) frame (next ∷ rest') =
  if evalAtFrame frame ψ₁ ∨ evalAtFrame frame ψ₂
    then now true
    else (later λ where .force → go (Or ψ₁ ψ₂) next (rest' .force))  -- BUG!
```

**Problem**: When the disjunction was false at the current frame, the checker would **continue to the next frame** and check again. This is temporal behavior (like Eventually), not propositional Or.

## Expected Behavior

Propositional Or should evaluate **only at the current frame**:
- `Or ψ₁ ψ₂` holds at frame `f` ⟺ `ψ₁` holds at `f` OR `ψ₂` holds at `f`
- Should NOT check future frames

For temporal disjunction, use: `Eventually (Or ψ₁ ψ₂)` or `Or (Eventually ψ₁) (Eventually ψ₂)`

## Impact

**Affected formulas**:
- `Or (Atomic p) (Atomic q)` where both predicates are false at frame 1
- Previously: Would continue checking frame 2, frame 3, ...
- Now: Returns false immediately if both are false at frame 1

**Severity**: Medium
- Incorrect semantics for propositional Or
- Could cause tests to pass when they should fail (false negatives)
- No production impact yet (proofs blocked on this bug being fixed)

## How Discovered

Discovered during formal verification (Phase 3.2 - proving And/Or operators):
- Attempted to prove `or-atomic-fold-equiv` for `Or (Atomic p) (Atomic q)`
- Proof failed because `checkColist` had extra delay layer
- RHS: `go (Or ...) f rest` pattern-matched on `rest` and recursed
- LHS: `foldStepEval-go` returned immediately
- Bisimilarity proof revealed semantic mismatch

**Root cause**: Pattern matching on colist in `go` prevented reduction in proofs and revealed the temporal behavior.

## Fix

**Fixed code** (Coinductive.agda line 126-128):
```agda
-- Or: check either on current frame (non-temporal semantics)
-- Temporal operators like Eventually wrap Or to check multiple frames
go (Or ψ₁ ψ₂) frame rest = now (evalAtFrame frame ψ₁ ∨ evalAtFrame frame ψ₂)
```

**Changes**:
1. Removed pattern matching on `rest` (both cases were semantically incorrect)
2. Return result immediately based on current frame only
3. Added comment explaining non-temporal semantics

## Locations Fixed

**Three independent implementations**:

1. **checkColist** (lines 126-128):
   Main infinite-trace LTL checker

2. **checkColistCE** (lines 233-237):
   Checker with counterexample generation

3. **goDelayed** (lines 345-348):
   Checker for DelayedColist (with explicit delays)

All three had identical bugs and were fixed consistently.

## Validation

**Proof succeeds after fix**:
```agda
or-atomic-go-equiv : ∀ (p q : TimedFrame → Bool) (f : TimedFrame) (rest : Colist TimedFrame ∞)
  → ∞ ⊢ foldStepEval-go (Or (Atomic p) (Atomic q)) (OrState AtomicState AtomicState) nothing f rest
      ≈ now (p f ∨ q f)

or-atomic-go-equiv p q f rest with p f in eq-p | q f in eq-q
... | true  | true  = DB.now refl  -- Left or right satisfied
... | true  | false = DB.now refl  -- Left satisfied
... | false | true  = DB.now refl  -- Right satisfied
... | false | false = DB.now refl  -- Both violated: returns now false
```

Proof type-checks successfully after fix, confirming:
- Both sides reduce to the same value
- No temporal recursion occurs
- Standard propositional Or semantics restored

## Related Bugs

This bug is similar to the And operator bug fixed earlier:
- **AND_OPERATOR_BUG_FIX.md**: And continued to next frame when both held (should stop)
- **OR_OPERATOR_BUG_FIX.md**: Or continued to next frame when both failed (should stop)

Both bugs stem from confusion between propositional and temporal operators.

## Lessons Learned

1. **Formal verification finds semantic bugs**: Proof attempts revealed incorrect temporal behavior
2. **Propositional operators are non-temporal**: And, Or, Not should only check current frame
3. **Temporal behavior belongs in temporal operators**: Always, Eventually, Until check multiple frames
4. **Pattern matching reveals hidden semantics**: Unnecessary case-splits often indicate semantic issues

## Prevention

**Design principle**:
- Propositional operators (And, Or, Not): Non-temporal, single-frame evaluation
- Temporal operators (Always, Eventually, Next, Until): Multi-frame evaluation
- Never mix the two semantics

**Code review checklist**:
- [ ] Does the operator pattern-match on the colist/trace?
- [ ] If yes, is it a temporal operator? (Next, Always, Eventually, Until, *Within)
- [ ] If no (propositional), remove pattern matching and use current frame only

## Files Modified

1. **src/Aletheia/LTL/Coinductive.agda** (3 locations):
   - Line 126-128: `go` for Or (checkColist)
   - Line 233-237: `go` for Or (checkColistCE)
   - Line 345-348: `goDelayed` for Or

2. **src/Aletheia/LTL/Properties.agda**:
   - Lines 214-233: `or-atomic-go-equiv` and `or-atomic-fold-equiv` (proofs now succeed)

## Verification Status

✅ **Verified**: Or operator proof complete without postulates
✅ **Builds**: Full type-check and build successful
✅ **Semantics**: Standard propositional Or restored

**Phase 3.2 Progress**: 4/4 propositional operators proven (Atomic, Not, And, Or)
