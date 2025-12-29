# Always Proof Progress (Session 6)

**Date**: 2025-12-27
**Status**: Partial implementation, hit reduction issue

## What Was Implemented

### ✅ Empty Case (lines 574-599)
Pattern matches on `stepEval φ` result and handles all three cases:
- **Violated**: Uses correspondence lemma to show `evalAtInfiniteExtension f φ ≡ false`
- **Satisfied**: Both sides match directly (`DB.now refl`)
- **Continue**: Both sides match directly (`DB.now refl`)

### ⏸️ Non-empty Violated Case (lines 608-660)
Attempted to use bind-cong with prf.force, but hit an issue:

**Problem**: Agda can't automatically see that:
```agda
foldStepEval-go (Always φ) (AlwaysState (initState φ)) nothing f (next ∷ rest')
```

reduces to `now false` when `stepEval φ` returns `Violated ce`.

**Why**: The definition of `foldStepEval-go` has complex nested pattern matching:
1. It pattern matches on `stepEval φ` (the outer call, Always φ)
2. Which internally calls `stepEval φ` (the inner formula)
3. Agda can't see through this indirection automatically

**Current error**:
```
bind (evaluateLTLOnTrace φ f ...) (λ r → if r then ... else now false)
!= now false
```

Even though we know from the pattern match that `stepEval φ` returned `Violated`, Agda doesn't propagate this through to show that `foldStepEval-go (Always φ)` reduces to `now false`.

## Attempted Solutions

1. **Using `bind-cong` with `prf .force`**: Gets us `bind (now false) (...) ≈ bind (evaluateLTLOnTrace φ ...) (...)`, but Agda doesn't reduce `bind (now false) (...)` to `now false` automatically

2. **Using `DB.sym`**: Flips the direction, but doesn't help with the reduction issue

3. **Using `DelayBisim.trans` with `DB.refl`**: Expects both sides to be syntactically equal after the first transformation, but they're not

## What's Needed

Need to explicitly show that when `stepEval φ` returns `Violated`, the LHS reduces to `now false`. Possible approaches:

### Option 1: Auxiliary Lemma
Create a lemma that states:
```agda
stepEval-always-violated-gives-now-false :
  ∀ φ f rest →
  stepEval φ evalAtomicPred (initState φ) nothing f ≡ Violated ce →
  foldStepEval-go (Always φ) (AlwaysState (initState φ)) nothing f rest
    ≈ now false
```

This would explicitly capture the reduction behavior.

### Option 2: Compute LHS Explicitly
Instead of relying on automatic reduction, manually expand what `foldStepEval-go (Always φ)` does when `stepEval (Always φ)` returns `Violated`:

```agda
-- Show: foldStepEval-go (Always φ) ... reduces to now false
-- by explicit computation using the definition of foldStepEval-go
```

### Option 3: Refactor Proof Structure
Don't pattern match on `stepEval φ` before calling `foldStepEval-go`. Instead, let `foldStepEval-go` do its own pattern matching, and then relate the result to the RHS.

### Option 4: Use Inspect Pattern More Cleverly
The `in eq-step` gives us an equality `stepEval φ ... ≡ Violated ce`. Maybe we can use this equality to rewrite the LHS explicitly before applying bisimilarity.

## Files Modified

- **src/Aletheia/LTL/Properties.agda**:
  - Lines 574-599: Empty case implementation ✅
  - Lines 604-660: Violated case attempt (incomplete)
  - Lines 662-670: Satisfied case (still has {!!})
  - Lines 672-680: Continue case (still has {!!})

## Next Steps

1. Try Option 4 first: Use `eq-step` to rewrite the LHS
2. If that fails, implement Option 1: Create auxiliary lemma
3. As last resort, try Option 3: Refactor proof structure

## Time Spent

~2 hours on implementation + debugging
Estimated remaining for Always: 2-3 hours
