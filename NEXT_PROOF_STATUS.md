# Next Operator Proof Status

**Date**: 2025-12-26
**Status**: In progress - infrastructure complete, final connection needed

## ✅ Achievements

1. **Bug Fixed**: Critical Next operator bug discovered and fixed (commit d256423)
   - Added `NextActive` state to properly skip first frame
   - Now correctly evaluates φ at next frame, not current frame

2. **Auxiliary Lemmas Added**:
   - `nextactive-unwrap`: Proves NextActive state evaluates same as regular φ ✅
   - `prev-irrelevant`: Postulated (evalAtomicPred ignores prev parameter)

3. **Understanding Gained**:
   - `prev` parameter only affects `changedBy` operator (not in current proofs)
   - For Next proof, prev values don't matter - can use transitivity to bridge

## 🔄 Current Challenge

**Issue**: Mismatch between helper proof and what's needed.

**Helper proves** (next-go-equiv-mut):
```agda
foldStepEval-go (Next φ) (NextState (initState φ)) nothing f rest
≈ checkColist φ rest
```

**Top-level needs**:
```agda
foldStepEval-go (Next φ) (NextState (initState φ)) nothing f rest
≈ go (Next φ) f rest  -- Internal coinductive function
```

**The problem**: `go (Next φ) f rest` ≠ `checkColist φ rest`!

### Semantic Difference

For `rest = []` (empty):
- `go (Next φ) f []` = `now (evalAtFrame f φ)`  ← Evaluates φ at last frame
- `checkColist φ []` = `now true`  ← Vacuously true

For `rest = (next ∷ rest')` (non-empty):
- `go (Next φ) f (next ∷ rest')` = `later λ .force → go φ next (rest' .force)`
- `checkColist φ (next ∷ rest')` = `later λ .force → go φ next (rest' .force)`
- These ARE the same! ✅

## 💡 Solution Approaches

### Option A: Inline coinductive definition
Since `go` is private, manually inline what `go (Next φ) f rest` reduces to:
- Empty case: Prove `≈ now (evalAtFrame f φ)`
- Non-empty case: Prove `≈ later λ .force → go φ next (rest' .force)`
- Use `fold-equiv φ` to connect to coinductive side

### Option B: Restructure helper lemma
Change helper to prove exactly what's needed by pattern matching on rest:
```agda
next-go-equiv-mut φ f [] :
  foldStepEval-go (Next φ) (NextState (initState φ)) nothing f []
  ≈ now (evalAtFrame f φ)  -- Match coinductive semantics!

next-go-equiv-mut φ f (next ∷ rest') :
  foldStepEval-go (Next φ) (NextState (initState φ)) nothing f (next ∷ rest')
  ≈ later λ .force → [something that reduces to go φ next (rest' .force)]
```

### Option C: Use symmetry + fold-equiv
- Prove `checkColist (Next φ) (f ∷ rest) ≈ checkColist φ rest` directly
- Use this to bridge the gap

## 📝 Key Insights for Next Session

1. **prev parameter**: Can be ignored for all non-changedBy operators
   - Postulate prev-irrelevant is reasonable
   - Can prove rigorously later if needed

2. **Coinductive go function**: Can't reference directly (private)
   - Must inline its definition or work around it
   - Pattern match on rest structure to handle empty/non-empty cases

3. **Empty trace semantics**:
   - Next φ on empty trace uses "infinite extension": last frame persists forever
   - So `Next φ` evaluated at last frame `f` with `rest = []` checks φ at f

4. **Proof strategy**: Use fold-equiv from mutual block to bridge to coinductive side
   - Extract forced thunks with pattern matching
   - Use transitivity to chain multiple bisimilarity steps

## 🎯 Recommended Next Steps

1. **Fix helper lemma**: Pattern match on rest to handle empty/non-empty separately
2. **Empty case**: Show incremental returns `now true`, coinductive returns `now (evalAtFrame f φ)`
   - These might not match! Need to check if incremental semantics are correct
3. **Non-empty case**: Current approach with transitivity should work
4. **If stuck**: Consider posting to Agda mailing list or looking for similar proofs in stdlib

## Files Modified

- `src/Aletheia/LTL/Incremental.agda`: Next operator bug fix (lines 57-58, 169-177)
- `src/Aletheia/LTL/Properties.agda`: Proof infrastructure (lines 285-447)
- Commits: d256423 (bug fix), others for proof attempts

## Time Investment

- Bug discovery + fix: ~2 hours
- Proof attempts: ~3 hours
- Total: ~5 hours on Next operator

**Value**: Bug discovery alone justified the effort! Proof completion will follow.
