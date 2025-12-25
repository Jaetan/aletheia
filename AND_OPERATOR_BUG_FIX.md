# Bug Fix: And Operator in Coinductive Checker

**Date**: 2025-12-25
**Discovered by**: Proof attempt for Phase 3.2 (And/Or operators)
**Status**: FIXED (proof blocked on separate issue)

## The Bug

In `src/Aletheia/LTL/Coinductive.agda`, the `And` operator incorrectly continued to the next frame when both operands held on the current frame:

**Affected functions**: `go` (line 126), `go` in `checkColistCE` (line 236), `goDelayed` (line 355)

```agda
-- BEFORE (incorrect):
go (And ψ₁ ψ₂) frame (next ∷ rest') =
  if evalAtFrame frame ψ₁ ∧ evalAtFrame frame ψ₂
    then (later λ where .force → go (And ψ₁ ψ₂) next (rest' .force))  -- BUG!
    else now false

-- AFTER (correct):
go (And ψ₁ ψ₂) frame (next ∷ rest') =
  -- Evaluate both on current frame only (non-temporal semantics)
  -- Temporal operators like Always wrap And to check multiple frames
  now (evalAtFrame frame ψ₁ ∧ evalAtFrame frame ψ₂)
```

## Why It Was Wrong

**Semantic Mismatch**:
- `And (Atomic p) (Atomic q)` should evaluate on the first frame only (non-temporal)
- Temporal checking is the responsibility of `Always`, `Eventually`, etc.
- The bug caused `And` to behave like `Always (And ...)` even without the `Always` wrapper

**Behavioral Impact**:
- For `And (Atomic p) (Atomic q)` on trace `[f1, f2]` where both p and q hold:
  - Buggy version: `later (later (...))` - continued checking f2
  - Correct version: `later (now true)` - stopped after f1
  - **Mismatch**: Extra delay layer, wrong semantics

**Concrete Example**:
```agda
-- Input: And (Atomic p) (Atomic q) on trace [f1, f2]
-- Assume: p f1 = true, q f1 = true

-- Coinductive (BUGGY): later (λ .force → later (λ .force → ...))   -- checks f2!
-- Coinductive (FIXED):  later (λ .force → now true)                -- stops at f1
-- Incremental:          later (λ .force → now true)                -- stops at f1
```

## Comparison with Not Operator Bug

| Aspect | Not Bug | And Bug |
|--------|---------|---------|
| **File** | Incremental.agda | Coinductive.agda |
| **Line** | 131 | 126, 236, 355 |
| **Symptom** | Returned Continue instead of Satisfied | Continued to next frame instead of stopping |
| **Impact** | Extra recursion when inner Violated | Extra delay layer when both hold |
| **Severity** | Medium | Medium |

Both bugs caused semantic mismatches that prevented bisimilarity proofs from succeeding!

## How the Bug Was Discovered

While attempting to prove:
```agda
and-atomic-fold-equiv : ∀ (p q : TimedFrame → Bool) (trace : Colist TimedFrame ∞)
  → ∞ ⊢ foldStepEval (And (Atomic p) (Atomic q)) trace ≈ checkColist (And (Atomic p) (Atomic q)) trace
```

**Discovery process**:
1. Attempted proof with pattern matching on `p f` and `q f`
2. Type error: couldn't unify delay structures
3. Traced both implementations manually
4. Found extra `later` wrapper in `checkColist` when both operands hold
5. Identified root cause: unnecessary recursion to next frame

**Key insight**: The bug was hidden until we tried to prove equivalence formally!

## The Fix

Changed three locations in `src/Aletheia/LTL/Coinductive.agda`:

**1. checkColist's `go` function (lines 124-127)**:
```diff
 go (And ψ₁ ψ₂) frame (next ∷ rest') =
-  if evalAtFrame frame ψ₁ ∧ evalAtFrame frame ψ₂
-    then (later λ where .force → go (And ψ₁ ψ₂) next (rest' .force))
-    else now false
+  -- Evaluate both on current frame only (non-temporal semantics)
+  -- Temporal operators like Always wrap And to check multiple frames
+  now (evalAtFrame frame ψ₁ ∧ evalAtFrame frame ψ₂)
```

**2. checkColistCE's `go` function (lines 234-237)**:
```diff
 go (And ψ₁ ψ₂) frame (next ∷ rest') =
-  if evalAtFrame frame ψ₁ ∧ evalAtFrame frame ψ₂
-    then (later λ where .force → go (And ψ₁ ψ₂) next (rest' .force))
-    else now (Fail (mkCounterexample frame "And: conjunct failed"))
+  -- Evaluate both on current frame only (non-temporal semantics)
+  if evalAtFrame frame ψ₁ ∧ evalAtFrame frame ψ₂ then now Pass
+  else now (Fail (mkCounterexample frame "And: conjunct failed"))
```

**3. checkDelayedColist's `goDelayed` function (lines 351-356)**:
```diff
 goDelayed (And ψ₁ ψ₂) frame [] = now (evalAtFrame frame ψ₁ ∧ evalAtFrame frame ψ₂)
-goDelayed (And ψ₁ ψ₂) frame (wait rest) = later λ where .force → goDelayed (And ψ₁ ψ₂) frame (rest .force)
-goDelayed (And ψ₁ ψ₂) frame (next ∷ rest') =
-  if evalAtFrame frame ψ₁ ∧ evalAtFrame frame ψ₂
-    then (later λ where .force → goDelayed (And ψ₁ ψ₂) next (rest' .force))
-    else now false
+goDelayed (And ψ₁ ψ₂) frame (wait rest) = now (evalAtFrame frame ψ₁ ∧ evalAtFrame frame ψ₂)
+goDelayed (And ψ₁ ψ₂) frame (next ∷ rest') = now (evalAtFrame frame ψ₁ ∧ evalAtFrame frame ψ₂)
```

## Verification

**Type-checking**: Module compiles successfully with `agda +RTS -N32 -RTS Aletheia/LTL/Coinductive.agda`

**Correctness**:
- Now matches `Atomic` and `Not` semantics (evaluate once, return immediately)
- Matches `Or` semantics (which was already correct!)
- Temporal checking delegated to `Always`, `Eventually`, etc. where it belongs

## Related Issue: And/Or Proof Blocked

**Problem**: Even with the And bug fixed, the And/Or proofs still fail due to a different issue.

**Root cause**: `stepEval` for And/Or uses nested with-clauses, which generate auxiliary functions (e.g., `with-164`) that Agda cannot reduce during proofs.

**Example error**:
```
Aletheia.LTL.Incremental.with-164 (Atomic p) ... != Satisfied
```

**Solution required**: Refactor `stepEval` in `Incremental.agda` to extract And/Or logic into top-level helper functions (similar to `foldStepEval-go`).

**Status**: Deferred to future session - requires careful refactoring of Incremental.agda

## Impact Assessment

**Severity**: Medium
- Bug affected all And operator evaluations in coinductive checker
- Would cause incorrect behavior for formulas like `And (Atomic p) (Atomic q)`
- Could cause performance issues (unnecessary frame processing)
- Semantic mismatch with incremental checker

**Scope**: Limited to coinductive checker
- Incremental checker (`stepEval`) was already correct
- Only `checkColist`, `checkColistCE`, and `checkDelayedColist` affected
- Or operator was already correct (good comparison!)

**Risk of Fix**: Low
- Straightforward change (remove unnecessary recursion)
- Matches semantics of Atomic, Not, and Or
- Module type-checks successfully
- Aligns with LTL semantics (non-temporal operators evaluate once)

## Files Modified

1. **src/Aletheia/LTL/Coinductive.agda** (3 locations)
   - Line 126-127: `go` for And in `checkColist`
   - Line 235-237: `go` for And in `checkColistCE`
   - Line 352-353: `goDelayed` for And in `checkDelayedColist`

## Next Steps

**Immediate** (blocked):
- ⏸️ Complete And/Or proofs - BLOCKED on stepEval refactoring

**Required refactoring**:
- Extract And/Or logic from `stepEval` into helper functions
- Avoid nested with-clauses to enable proof reduction
- Follow pattern used for `foldStepEval-go`

**Future** (after refactoring):
- ✅ Prove And operator equivalence
- ✅ Prove Or operator equivalence
- ✅ Complete Phase 3.2 (all propositional operators)

**Integration**:
- Run comprehensive tests after refactoring
- Verify no regression in existing functionality
- Update PROJECT_STATUS.md with progress

## Lesson Learned

**Value of Formal Verification** (again!):
- Second bug discovered through proof attempts in this session
- Both bugs (Not and And) had semantic mismatches hidden from testing
- Formal proofs expose subtle implementation errors
- Incremental checker was correct; coinductive checker had bugs

**Pattern emerging**: The proof process is finding real bugs, not just theoretical issues!

## References

- **Session state**: `.session-state.md`
- **Not bug fix**: `NOT_OPERATOR_BUG_FIX.md`
- **Properties file**: `src/Aletheia/LTL/Properties.agda`
- **Incremental file**: `src/Aletheia/LTL/Incremental.agda`
- **Coinductive file**: `src/Aletheia/LTL/Coinductive.agda`
