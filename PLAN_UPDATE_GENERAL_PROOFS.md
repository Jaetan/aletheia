# Plan Update: Extend to General (Non-Atomic) Proofs

**Date**: 2025-12-25
**Reason**: Current proofs only handle atomic base cases; need full compositional proofs

## Current Status

**Proofs Completed**:
- ✅ `atomic-fold-equiv`: for Atomic p
- ✅ `not-atomic-fold-equiv`: for Not (Atomic p)
- ⏸️ `and-atomic-fold-equiv`: for And (Atomic p) (Atomic q) - BLOCKED on stepEval refactoring
- ⏸️ `or-atomic-fold-equiv`: for Or (Atomic p) (Atomic q) - BLOCKED on stepEval refactoring

**Limitation**: These only prove correctness for specific atomic cases, not general formulas.

## New Requirement: General Compositional Proofs

### Goal

Prove equivalence for **arbitrary** subformulas using structural induction:

```agda
-- General Not equivalence (for any φ)
not-fold-equiv : ∀ (φ : LTL (TimedFrame → Bool)) (trace : Colist TimedFrame ∞)
  → ∞ ⊢ foldStepEval (Not φ) trace ≈ checkColist (Not φ) trace

-- General And equivalence (for any φ, ψ)
and-fold-equiv : ∀ (φ ψ : LTL (TimedFrame → Bool)) (trace : Colist TimedFrame ∞)
  → ∞ ⊢ foldStepEval (And φ ψ) trace ≈ checkColist (And φ ψ) trace

-- General Or equivalence (for any φ, ψ)
or-fold-equiv : ∀ (φ ψ : LTL (TimedFrame → Bool)) (trace : Colist TimedFrame ∞)
  → ∞ ⊢ foldStepEval (Or φ ψ) trace ≈ checkColist (Or φ ψ) trace
```

### Why This Matters

**Current proofs** only work for specific shapes:
- ✅ `Not (Atomic p)` - proven
- ❌ `Not (Not (Atomic p))` - NOT proven
- ❌ `Not (And (Atomic p) (Atomic q))` - NOT proven
- ❌ `And (Not (Atomic p)) (Atomic q)` - NOT proven
- ❌ `Not (Always (Atomic p))` - NOT proven

**General proofs** will handle ALL formulas compositionally.

## Implementation Strategy

### Phase 3.3: Extend to Non-Atomic Operands (NEW)

**Approach**: Structural induction on formula structure

#### Step 1: Propositional Compositions (3-5 hours)

Prove for combinations of propositional operators:

**Not cases**:
- `Not (Not φ)` - use `not-fold-equiv` recursively
- `Not (And φ ψ)` - use `and-fold-equiv` recursively
- `Not (Or φ ψ)` - use `or-fold-equiv` recursively

**And cases**:
- `And (Not φ) ψ` - use `not-fold-equiv` + `and-fold-equiv`
- `And φ (Not ψ)` - symmetric
- `And (And φ₁ φ₂) ψ` - nested And
- `And (Or φ₁ φ₂) ψ` - composition
- ... (all combinations)

**Or cases**:
- Similar to And cases

**Proof structure**:
```agda
not-fold-equiv (Atomic p) trace = not-atomic-fold-equiv p trace  -- Base case
not-fold-equiv (Not φ) trace = ...  -- Recursive case using not-fold-equiv φ
not-fold-equiv (And φ ψ) trace = ...  -- Recursive case using and-fold-equiv φ ψ
-- etc.
```

#### Step 2: Temporal Compositions (2-3 hours, after Phase 4)

Prove for combinations with temporal operators:

**Requires Phase 4 first** (temporal operator proofs):
- `Not (Always φ)` - use `always-fold-equiv` recursively
- `Not (Eventually φ)` - use `eventually-fold-equiv` recursively
- `And (Always φ) ψ` - composition
- `Or (Eventually φ) ψ` - composition
- ... (all combinations)

**Proof structure**:
```agda
not-fold-equiv (Always φ) trace = ...  -- Use always-fold-equiv φ
and-fold-equiv (Eventually φ) ψ trace = ...  -- Use eventually-fold-equiv φ
-- etc.
```

## Updated Phase Structure

### Phase 3.1: Atomic Base Cases ✅ COMPLETE
- atomic-fold-equiv: for Atomic p

### Phase 3.2a: Not/And/Or with Atomic Operands 🔄 IN PROGRESS
- not-atomic-fold-equiv: for Not (Atomic p) ✅ COMPLETE
- and-atomic-fold-equiv: for And (Atomic p) (Atomic q) ⏸️ BLOCKED
- or-atomic-fold-equiv: for Or (Atomic p) (Atomic q) ⏸️ BLOCKED

### Phase 3.2b: stepEval Refactoring ⏸️ TODO
- Extract And/Or logic to avoid nested with-clauses
- Required for atomic proofs to work
- Estimated: 2-3 hours

### Phase 3.3: Extend to Non-Atomic Operands ⏸️ TODO (NEW)
- **Step 1**: Propositional compositions (Not (Not φ), And (Not φ) ψ, etc.)
- **Step 2**: Temporal compositions (after Phase 4)
- Estimated: 5-8 hours total (3-5h + 2-3h)

### Phase 4: Temporal Operators ⏸️ TODO
- **4.1**: Research (3-5h)
- **4.2**: Prove Next, Always, Eventually, Until, *Within (5-10h)
- **4.3**: Complete Phase 3.3 Step 2 temporal compositions (2-3h)

## Benefits of General Proofs

1. **Completeness**: Covers ALL possible LTL formulas, not just specific patterns
2. **Compositionality**: Can reason about complex formulas built from simpler ones
3. **Maintainability**: Changes to one operator's proof don't break compositions
4. **Confidence**: Proves the entire LTL system is correct, not just specific cases

## Example: Building Up Complexity

**Current**:
```agda
-- ✅ Can prove:
foldStepEval (Atomic p) ≈ checkColist (Atomic p)
foldStepEval (Not (Atomic p)) ≈ checkColist (Not (Atomic p))

-- ❌ Cannot prove:
foldStepEval (Not (Not (Atomic p))) ≈ checkColist (Not (Not (Atomic p)))
```

**With general proofs**:
```agda
-- ✅ Base case:
not-fold-equiv (Atomic p) = not-atomic-fold-equiv p

-- ✅ Recursive case (builds on base):
not-fold-equiv (Not φ) = ... (uses not-fold-equiv φ recursively)

-- ✅ Therefore proven for ALL formulas:
foldStepEval (Not (Not (Not (Atomic p)))) ≈ checkColist (Not (Not (Not (Atomic p))))
foldStepEval (Not (And φ ψ)) ≈ checkColist (Not (And φ ψ))
-- etc.
```

## Implementation Notes

**Dependencies**:
- Phase 3.3 Step 1 (propositional) can start after Phase 3.2 completes
- Phase 3.3 Step 2 (temporal) requires Phase 4 to complete first
- Total estimated effort: ~15-20 hours (including Phase 4)

**Proof Technique**:
- Use same copattern matching + bisimilarity approach
- Structural induction on LTL formula
- Recursive proofs compose naturally

**Risk**: Medium complexity
- Need to handle many cases (formula constructors × formula constructors)
- But each case should follow mechanical pattern
- Base cases already proven provide template

## Files to Update

1. **src/Aletheia/LTL/Properties.agda**:
   - Add general `not-fold-equiv`, `and-fold-equiv`, `or-fold-equiv`
   - Keep atomic cases as base lemmas
   - Use structural induction for general cases

2. **Documentation**:
   - ✅ Updated: `~/.claude/plans/coinductive-proof-strategy.md`
   - ✅ Updated: `~/.claude/plans/CURRENT_POSITION.md`
   - This file: Plan update rationale

## Success Criteria

**Phase 3.3 Step 1 Complete** when:
- `not-fold-equiv` proven for all propositional combinations
- `and-fold-equiv` proven for all propositional combinations
- `or-fold-equiv` proven for all propositional combinations
- NO POSTULATES

**Phase 3.3 Step 2 Complete** when (after Phase 4):
- All three theorems proven for temporal operator combinations
- Full compositional correctness established
- NO POSTULATES

**Overall Success**: Complete formal verification that foldStepEval ≡ checkColist for ALL LTL formulas! 🎯
