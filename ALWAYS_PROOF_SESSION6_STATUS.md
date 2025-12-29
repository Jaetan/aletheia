# Always Operator Proof - Session 6 Status

**Date**: 2025-12-27
**Status**: Significant progress, blocked on with-pattern reduction issue

## Summary

Made substantial progress on the Always operator proof, implementing several helper lemmas and proof infrastructure. Currently blocked on a fundamental Agda limitation with nested with-pattern reduction.

## Accomplishments

### 1. Helper Lemmas Created

**`bind-now-reduces`** (Properties.agda:362-368):
```agda
bind-now-reduces : ∀ {A B} {i} {d} {x} (f : A → Delay B ∞)
  → i ⊢ d ≈ now x
  → i ⊢ bind d f ≈ f x
```
- **Purpose**: Shows that when `d ≈ now x`, then `bind d f ≈ f x`
- **Key insight**: Avoids needing to know what `f` is syntactically
- **Usage**: Essential for proving temporal operators that use `bind`

**`foldStepEval-go-violated`** (Properties.agda:504-509):
```agda
foldStepEval-go-violated : ∀ {i} φ st prev curr rest ce
  → stepEval φ evalAtomicPred st prev curr ≡ Violated ce
  → i ⊢ foldStepEval-go φ st prev curr rest ≈ now false
```
- **Purpose**: Captures reduction behavior when `stepEval` returns `Violated`
- **Implementation**: Uses `rewrite` to substitute the equality
- **Issue**: Doesn't fully reduce nested with-patterns

**`always-stepEval-violated`** (Properties.agda:521-527):
```agda
always-stepEval-violated : ∀ φ st prev curr ce
  → stepEval φ evalAtomicPred st prev curr ≡ Violated ce
  → stepEval (Always φ) evalAtomicPred (AlwaysState st) prev curr ≡ Violated ce
```
- **Purpose**: Shows that Violated propagates from inner `φ` to outer `Always φ`
- **Corresponds to**: Incremental.agda:183

### 2. Proof Structure

**Empty case** (Properties.agda:574-599): ✅ **COMPLETE**
- Pattern matches on `stepEval φ` result
- Handles Violated, Satisfied, Continue cases correctly
- Uses correspondence lemma for Violated case

**Non-empty Violated case** (Properties.agda:645-664): ⏸️ **BLOCKED**
```agda
-- Proof strategy:
-- 1. Show LHS ≈ now false using foldStepEval-go-violated
-- 2. Show RHS ≈ now false using bind-now-reduces
-- 3. Use transitivity: LHS ≈ now false ≈ RHS
let inner-eq = ...
    lhs-eq = foldStepEval-go-violated (Always φ) ...  -- ≈ now false
    rhs-eq = bind-now-reduces _ inner-eq               -- bind (...) ≈ now false
in DelayBisim.trans lhs-eq (DB.sym rhs-eq)
```

## Current Blocker

### The With-Pattern Reduction Issue

**Problem**: Even after using `rewrite` in `foldStepEval-go-violated`, Agda shows:
```
foldStepEval-go (Always φ) (AlwaysState (initState φ)) nothing f (next ∷ rest')
  | (stepEval (Always φ) evalAtomicPred (AlwaysState (initState φ)) nothing f
     | stepEval φ evalAtomicPred (initState φ) nothing f)
!= now false
```

**Root cause**: Nested with-patterns in:
1. `foldStepEval-go` (line 125): `with stepEval φ ...`
2. `stepEval (Always φ)` (Incremental.agda:180-181): `with stepEval φ ...`

**Why it matters**: When we pattern match on `Violated ce` at the proof site, we KNOW that:
- `stepEval φ ... = Violated ce` (from `eq-step`)
- Therefore `stepEval (Always φ) ... = Violated ce` (line 183)
- Therefore `foldStepEval-go (Always φ) ... = now false` (line 137)

But Agda doesn't automatically propagate this knowledge through the with-patterns.

### Lambda Nominal Equality Issue (Resolved)

**Previous blocker**: Couldn't use `bind-cong` because locally-defined lambdas are syntactically different from those in `Coinductive.agda` (Agda treats lambdas nominally by source location).

**Solution**: Created `bind-now-reduces` which doesn't require knowing the function syntactically. This resolves the lambda issue.

## What Was Tried

1. ✅ **Using `bind-cong` with local lambda**: Failed due to nominal lambda equality
2. ✅ **Helper lemma `always-coinductive-violated`**: Failed due to same lambda issue
3. ✅ **`bind-now-reduces` with underscore for function**: Agda can infer the function from context
4. ✅ **`rewrite` in `foldStepEval-go-violated`**: Partially works but doesn't fully reduce nested with-patterns
5. ⏸️ **Transitivity with both sides ≈ now false**: Current approach, blocked on with-pattern reduction

## Possible Solutions

### Option 1: Modify foldStepEval-go to avoid with-patterns
**Complexity**: High (major refactor)
**Risk**: Might break existing proofs (Next operator)
**Benefit**: Would resolve with-pattern issues permanently

### Option 2: Use `subst` with explicit pattern matching
**Complexity**: Medium
**Approach**: Extract the with-pattern match result and use `subst` to rewrite goal
**Status**: Not yet attempted

### Option 3: Auxiliary function without with-patterns
**Complexity**: Medium
**Approach**: Define helper function that explicitly matches on `StepResult`:
```agda
foldStepEval-go-explicit : StepResult → ...
foldStepEval-go-explicit (Violated _) = now false
foldStepEval-go-explicit Satisfied = now true
foldStepEval-go-explicit (Continue st') = later (...)
```

### Option 4: Accept postulate for Violated case
**Complexity**: Low (pragmatic but not ideal)
**Risk**: Undermines proof goals
**When to consider**: If other approaches take >8 hours

## Estimated Time Remaining

- **Option 2 (subst)**: 2-3 hours
- **Option 3 (auxiliary function)**: 3-4 hours
- **Option 1 (refactor foldStepEval-go)**: 6-8 hours
- **Option 4 (postulate)**: 30 minutes

## Recommendation

Try **Option 2** next (use `subst` to explicitly rewrite goal using `eq-step`). If that doesn't work within 2-3 hours, consider **Option 3** (auxiliary function without with-patterns).

## Files Modified

- `src/Aletheia/LTL/Properties.agda`:
  - Lines 362-368: `bind-now-reduces` helper
  - Lines 504-509: `foldStepEval-go-violated` helper
  - Lines 521-527: `always-stepEval-violated` helper
  - Lines 574-599: Empty case (complete)
  - Lines 645-664: Non-empty Violated case (blocked)

## Key Insights

1. **Bisimilarity with `now`**: When `d ≈ now x`, then `d` must be `now x` (bisimilarity preserves constructors). This enables `bind-now-reduces`.

2. **Nominal lambda equality**: Agda treats lambda expressions by their source location, not their content. Can't match locally-defined lambdas with those in definitions.

3. **With-pattern abstraction**: `rewrite` doesn't fully reduce through nested with-patterns in the proof context.

4. **Proof strategy for temporal operators**:
   - Show both LHS and RHS bisimilar to a common intermediate value
   - Use transitivity to connect them
   - Requires helper lemmas to handle reduction explicitly

## Time Spent

**Total**: ~4-5 hours
- Helper lemma development: 2 hours
- Proof attempts and debugging: 2 hours
- Lambda equality investigation: 1 hour
