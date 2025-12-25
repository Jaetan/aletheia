# Next Operator Semantics Analysis

**Date**: 2025-12-26
**Issue**: Potential semantic mismatch between incremental and coinductive Next

## Coinductive Version Trace

For `checkColist (Next (Atomic p)) (f1 ∷ (f2 ∷ rest))`:

1. `checkColist (Next (Atomic p)) (f1 ∷ ...)`  
   = `later λ .force → go (Next (Atomic p)) f1 (f2 ∷ rest)`

2. `go (Next (Atomic p)) f1 (f2 ∷ rest)`  
   = `later λ .force → go (Atomic p) f2 rest`  (by Next definition)

3. `go (Atomic p) f2 rest`  
   = `now (p f2)`  (by Atomic definition)

**Result**: `later (later (now (p f2)))`  
**Evaluates predicate at**: Frame f2 (second frame) ✅

## Incremental Version Trace

For `foldStepEval (Next (Atomic p)) (f1 ∷ (f2 ∷ rest))`:

1. `foldStepEval (Next (Atomic p)) (f1 ∷ ...)`  
   = `later λ .force → foldStepEval-go (Next (Atomic p)) (NextState AtomicState) nothing f1 (f2 ∷ rest)`

2. `foldStepEval-go` calls `stepEval (Next (Atomic p)) ... nothing f1`

3. `stepEval (Next (Atomic p))` calls `stepEval (Atomic p) ... nothing f1`

4. `stepEval (Atomic p) ... f1` evaluates `p f1` and returns Satisfied or Violated

5. `stepEval (Next (Atomic p))` returns Satisfied or Violated (no NextState wrap!)

6. `foldStepEval-go` returns `now true` or `now false`

**Result**: `later (now (p f1))`  
**Evaluates predicate at**: Frame f1 (first frame) ❌

## The Problem

- **Coinductive**: Two `later` wrappers, evaluates at f2
- **Incremental**: One `later` wrapper, evaluates at f1
- **Mismatch**: Different number of delays AND different frames!

## Possible Explanations

1. **Bug in incremental**: Should not call `stepEval φ` at current frame for Next
2. **Bug in trace analysis**: Maybe the evaluation happens differently than traced
3. **Different semantics**: Maybe they're supposed to be different (but why?)

## Next Steps

- Check if there are tests for Next operator behavior
- Verify understanding by looking at how Next is used in practice
- Consider if the incremental version needs to be fixed before proving equivalence

