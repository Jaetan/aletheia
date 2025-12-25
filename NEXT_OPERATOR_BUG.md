# Next Operator Bug - Incremental Evaluator

**Date**: 2025-12-26
**Severity**: HIGH - Incorrect semantics for Next operator
**Status**: CONFIRMED

## The Bug

The incremental evaluator's `stepEval` for Next operator evaluates the inner formula at the **current frame** instead of **skipping to the next frame**.

### Current Implementation (WRONG)

```agda
-- Incremental.agda:166-171
stepEval (Next φ) eval (NextState st) prev curr
  with stepEval φ eval st prev curr  -- ❌ Evaluates φ at curr (current frame)
... | Continue st' = Continue (NextState st')
... | Violated ce = Violated ce
... | Satisfied = Satisfied
```

### Expected Behavior (Coinductive - CORRECT)

```agda
-- Coinductive.agda:130-133
go (Next ψ) frame [] = now (evalAtFrame frame ψ)
go (Next ψ) frame (next ∷ rest') =
  later λ where .force → go ψ next (rest' .force)  -- ✅ Evaluates ψ at next frame
```

### Concrete Example

For `Next (Atomic (id == 2))` on trace `[frame1(id=1), frame2(id=2), frame3(id=3)]`:

**Coinductive (correct)**:
- Evaluates `id == 2` at frame2 → TRUE

**Incremental (buggy)**:
- Evaluates `id == 2` at frame1 → FALSE

## Root Cause

The state machine approach for Next is incorrect. The current implementation:
1. Stores `NextState st` where `st` is the state of the inner formula φ
2. On each frame, evaluates `stepEval φ ... st ... curr` at the current frame
3. Wraps result in `NextState` if it continues

This is wrong because Next should:
1. **Skip the first frame** without evaluating φ
2. On the **second frame**, start evaluating φ

## Fix Strategy

Add a new state constructor to track whether we've skipped the frame yet:

```agda
data LTLEvalState where
  ...
  NextState : LTLEvalState → LTLEvalState       -- Waiting to skip first frame
  NextActive : LTLEvalState → LTLEvalState      -- Skipped first frame, now evaluating inner
  ...
```

Update stepEval:

```agda
-- First frame: skip it, transition to NextActive
stepEval (Next φ) eval (NextState st) prev curr
  = Continue (NextActive st)  -- Skip this frame

-- Subsequent frames: evaluate φ
stepEval (Next φ) eval (NextActive st) prev curr
  with stepEval φ eval st prev curr
... | Continue st' = Continue (NextActive st')
... | Violated ce = Violated ce
... | Satisfied = Satisfied
```

## Impact

**High impact**:
- All Next operator evaluations are incorrect in the streaming evaluator
- This affects ANY property using Next in production
- Legacy list-based evaluators (checkFormula, checkFormulaCE) are CORRECT - they properly skip the first frame

**Where Next is used**:
- Check if Next appears in production DBC files or test cases
- Verify whether Always/Until might have similar state machine bugs

## Testing

Need to add tests for Next operator to catch this:
```python
# Test: Next (id == 2) on [id=1, id=2, id=3] should be TRUE
trace = [frame(id=1), frame(id=2), frame(id=3)]
result = check(Next(Atomic(lambda f: f.id == 2)), trace)
assert result == True  # Currently would be False!
```

## Related

- NEXT_SEMANTICS_ISSUE.md: Initial analysis that discovered this bug
- Properties.agda: Proof attempt revealed the semantic mismatch
- Phase 4 proofs blocked until this is fixed

## Next Steps

1. Fix bug in Incremental.agda by adding NextActive state
2. Verify fix with manual trace
3. Update initState for Next to return NextState (not NextActive)
4. Re-run type-checking to ensure no regressions
5. Resume Phase 4 proofs with corrected implementation
