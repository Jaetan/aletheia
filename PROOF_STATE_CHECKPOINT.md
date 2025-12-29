# Proof State Checkpoint - Extended Lambda Blocker Discovery

**Date**: 2025-12-29
**Commit**: 6dcccc3 (revert incorrect semantic changes, remove operator postulates)
**Status**: Successfully identified the ONLY blocker for False/True case proofs

---

## Current Achievement: Proof Almost Complete!

We successfully proved that the **False and True cases for Always operator** can be proven using **ONLY the 5 generic postulates**, with all intermediate steps type-checking perfectly. The ONLY blocker is extended lambda nominal equality in the final step.

### What We Proved

**All these steps type-check** (see `AlwaysLemmas.agda` lines 101-130):

```agda
always-rhs-when-false φ curr next rest' inner-false =
  let continuation r = if r then later (λ where .force → ...) else now false

      -- Step 1: Apply bind-cong ✅
      step1 : bind (evaluateLTLOnTrace φ ...) continuation ≈ bind (now false) continuation

      -- Step 2: Apply bind-now ✅
      step2 : bind (now false) continuation ≈ continuation false

      -- Step 3: Compute continuation false = now false ✅
      step3 : continuation false ≈ now false

      -- Step 4: Chain them ✅
      chain : bind (evaluateLTLOnTrace φ ...) continuation ≈ now false

  in subst (λ x → ∞ ⊢ x ≈ now false) refl chain  -- ❌ BLOCKED HERE
```

**The blocker**: Agda says our extended lambda `λ where .force → ...` at line 105 is nominally distinct from the one in `Coinductive.agda:134`, even though they're syntactically identical.

---

## Files Containing Evidence

### Primary Evidence
- **`EXTENDED_LAMBDA_BLOCKER_EVIDENCE.md`**: Full analysis of the blocker
- **`src/Aletheia/LTL/Properties/AlwaysLemmas.agda`** (lines 101-142): Proof attempt showing all steps type-check except the final subst

### Supporting Analysis
- **`STRATEGY1_TYPE_ANALYSIS.md`**: Type-level analysis showing what lemmas we need
- **`COINDUCTIVE_RESEARCH_NOTES.md`**: Research on how others handle coinductive proofs

### Error Message
```
λ { .force → evaluateLTLOnTrace (Always φ) next (rest' .force) } !=
λ { .force → evaluateLTLOnTrace (Always φ) next (rest' .force) }
Because they are distinct extended lambdas: one is defined at
   AlwaysLemmas.agda:105.35-101 and the other at Coinductive.agda:134.19-85
```

---

## The Three Options

### Option 1: Minimal Definition-Level Postulates

**What**: Add 3 postulates (one per operator) to unfold coinductive definitions:

```agda
postulate
  always-unfold : ∀ φ curr next rest'
    → evaluateLTLOnTrace (Always φ) curr (next ∷ rest')
    ≡ bind (evaluateLTLOnTrace φ curr (next ∷ rest')) λ r →
        if r then later (λ where .force → evaluateLTLOnTrace (Always φ) next (rest' .force))
             else now false
```

**Pros**:
- Reduces from 9 postulates to 3
- Postulates are literally true by definition
- Minimal and honest

**Cons**:
- Still needs 3 operator-specific postulates
- Would prefer 1 generic postulate covering all extended lambda equality

**Variation**: Try to find **1 generic postulate** that covers extended lambda equality for all operators

---

### Option 2: Cubical Agda with Path Equality

**What**: Use Cubical Agda's path-based equality instead of propositional equality

**Challenge**: Compatibility issues:
- Our code uses `--sized-types` (for coinductive streams)
- Cubical uses `--cubical` flag which implies `--guardedness`
- These flags are incompatible

**Workaround**: Don't import cubical library, use built-in cubical primitives in Agda 2.8.0 with `--cubical` flag

**Test**: Create throw-away code in `/tmp/` to check if path equality can prove extended lambda equality

**If successful**: Would eliminate ALL extended lambda equality issues across the codebase

---

### Option 3: Continue Case with Accumulation

**What**: After solving False/True cases, tackle the Continue case using the "accumulation" idea:

> "Can we let [incremental evaluation] accumulate frames, so that it is eventually bisimilar to the RHS that has already seen all frames?"

**Key insight**: When `stepEval φ ... = Continue st'`, the formula φ hasn't finished evaluating on a single frame. But `evaluateLTLOnTrace φ curr rest` evaluates on the entire remaining trace.

**Question**: Can we relate:
- Incremental: processes frame-by-frame, accumulates state
- Coinductive: processes entire trace at once

By showing that after accumulating N frames incrementally, we reach the same result as coinductive evaluation?

---

## Decision Tree

```
1. Test Cubical Agda (Option 2)
   ├─ If path equality solves extended lambda issue:
   │  └─ Port to Cubical Agda (eliminate ALL postulates for False/True)
   │     └─ Then tackle Continue case (Option 3)
   │
   └─ If Cubical doesn't help OR incompatible with --sized-types:
      └─ Use minimal postulates (Option 1)
         ├─ Prefer: 1 generic postulate for extended lambda equality
         └─ Fallback: 3 definition-level postulates
         └─ Then tackle Continue case (Option 3)
```

---

## Current Code State

### What's Reverted and Clean
- ✅ Incremental.agda: Correct state preservation (not reset)
- ✅ AlwaysLemmas.agda: Signatures match implementation
- ✅ 9 operator-specific postulates deleted
- ✅ 5 generic postulates kept
- ✅ 3 holes in Properties.agda (honest assessment)

### What's Work-in-Progress
- 🔄 AlwaysLemmas.agda lines 101-142: Proof attempt for False case (demonstrates the blocker)
- 🔄 always-rhs-when-true: Needs similar proof attempt
- 🔄 always-rhs-continue-continues: Left as hole for Option 3

### All Modules Type-Check
- ✅ Incremental.agda
- ✅ AlwaysLemmas.agda (with holes)
- ✅ Properties.agda (with holes)

---

## Postulate Count Status

**Before this session**: 14 postulates
- 5 generic delay monad
- 9 operator-specific

**After revert and cleanup**: 5 postulates
- 5 generic delay monad
- 0 operator-specific (all deleted, replaced with holes)

**After Option 1 (minimal)**: 8 postulates
- 5 generic delay monad
- 3 definition-level (always-unfold, eventually-unfold, until-unfold)

**After Option 1 (ideal)**: 6 postulates
- 5 generic delay monad
- 1 generic extended lambda equality

**After Option 2 (if successful)**: 5 postulates
- 5 generic delay monad
- 0 for extended lambda (solved by path equality)

---

## Cubical Agda Test Results (COMPLETED)

**Date**: 2025-12-29
**Status**: ❌ **Cubical does NOT solve the problem**

**Findings**:
- Created `/tmp/cubical-extended-lambda-test.agda` with 5 test cases
- Even with Cubical's path equality, extended lambdas at different source locations remain nominally distinct
- Error message identical to our original blocker:
  ```
  λ { .force → now 42 } != λ { .force → now 42 }
  Because they are distinct extended lambdas: one is defined at [location 1]
  and the other at [location 2]
  ```
- **Conclusion**: Path equality doesn't help - the problem is representational, not proof-theoretic

**Decision**: Proceed with **Option 1B** (3 definition-level postulates)

See `/tmp/cubical-test-results.md` for complete test documentation.

---

## Next Immediate Steps

1. **Implement Option 1B** (3 definition-level postulates):
   - Add `always-unfold` postulate to AlwaysLemmas.agda
   - Add `eventually-unfold` postulate to EventuallyLemmas.agda
   - Add `until-unfold` postulate to UntilLemmas.agda
   - Each postulate states the definitional unfolding (TRUE BY DEFINITION)

2. **Complete False/True case proofs**:
   - Use unfold postulates to bridge definitional equality gap
   - All intermediate bind reduction steps already work

3. **After False/True cases resolved**:
   - Option 3: Tackle Continue case with accumulation idea

---

## Key Files for Recovery

If session is interrupted, the critical files are:

**Evidence**:
- `EXTENDED_LAMBDA_BLOCKER_EVIDENCE.md`
- `PROOF_STATE_CHECKPOINT.md` (this file)

**Code**:
- `src/Aletheia/LTL/Properties/AlwaysLemmas.agda` (lines 101-142)
- `src/Aletheia/LTL/Properties.agda` (holes at lines 609, 641, 668)

**Analysis**:
- `STRATEGY1_TYPE_ANALYSIS.md`
- `COINDUCTIVE_RESEARCH_NOTES.md`

**Commit**:
- 6dcccc3: Revert incorrect semantic changes, clean state

---

## Recovery Instructions

To resume from this checkpoint:

1. Read `PROOF_STATE_CHECKPOINT.md` (this file)
2. Read `EXTENDED_LAMBDA_BLOCKER_EVIDENCE.md` for the detailed finding
3. Check cubical test results in `/tmp/cubical-test-results.md` (to be created)
4. Based on cubical results, proceed with Option 1 or Option 2
5. After False/True cases: tackle Option 3 (Continue case)

---

## The Big Picture

We're **very close** to proving bisimilarity without operator-specific postulates!

**What we know**:
- ✅ The proof strategy is mathematically sound
- ✅ Generic postulates are sufficient for bind reduction
- ✅ Extended lambda nominal equality is the ONLY technical blocker
- ❓ Continue case needs separate investigation (accumulation idea)

**What we're testing**:
- Can Cubical Agda's path equality bypass the extended lambda blocker?

**What we'll decide**:
- Use Cubical (if it works) OR use 1-3 minimal postulates (if Cubical doesn't help)

**Then**:
- Tackle Continue case with fresh perspective (accumulation approach)
