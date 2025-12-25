# Phase 3.3 Research: Compositional Proof Challenges

**Date**: 2025-12-26
**Status**: ⚠️ Research Required
**Complexity**: High - Requires deep understanding of bisimilarity composition

## The Challenge: Double Negation `Not (Not φ)`

### Goal
Prove: `foldStepEval (Not (Not φ)) trace ≈ checkColist (Not (Not φ)) trace`

### What We Know (Inductive Hypothesis)
```agda
fold-equiv φ trace : foldStepEval φ trace ≈ checkColist φ trace
```

### Coinductive Side (checkColist)
```agda
checkColist (Not (Not φ)) (f ∷ rest)
  = later λ where .force → go (Not (Not φ)) f (rest .force)

go (Not ψ) frame colist = Delay.map not (go ψ frame colist)

-- Therefore:
go (Not (Not φ)) frame colist
  = Delay.map not (go (Not φ) frame colist)
  = Delay.map not (Delay.map not (go φ frame colist))
```

### Incremental Side (foldStepEval)
```agda
foldStepEval (Not (Not φ)) (f ∷ rest)
  = later λ where .force →
      foldStepEval-go (Not (Not φ)) (NotState (NotState (initState φ))) nothing f (rest .force)

-- stepEval (Not (Not φ)) with nested NotState:
stepEval (Not (Not φ)) eval (NotState (NotState st)) prev curr
  = stepEval (Not φ) eval (NotState st) prev curr  -- outer Not
  = [match on stepEval φ eval st prev curr]         -- inner Not
```

### The Gap

**Challenge**: Relate these two very different evaluation strategies:

1. **Coinductive**: Double application of `Delay.map not`
   - Composition: `Delay.map not ∘ Delay.map not`
   - Should reduce to identity (since `not ∘ not = id`)
   - But need to prove this preserves bisimilarity!

2. **Incremental**: Nested state transformations `NotState (NotState st)`
   - State-based: track continue/satisfied/violated through nested Not states
   - Need to relate state transitions to Delay.map operations

## Required Helper Lemmas

### 1. Delay.map Composition
```agda
delay-map-comp : ∀ {A B C} (f : B → C) (g : A → B) (d : Delay A ∞)
  → Delay.map f (Delay.map g d) ≈ Delay.map (f ∘ g) d
```

**Status**: May exist in stdlib, need to check
**Location**: Codata.Sized.Delay.Properties

### 2. Not Double Application
```agda
not-not-id : ∀ (b : Bool) → not (not b) ≡ b
```

**Status**: Trivial, but need to lift to Delay
**Consequence**: `Delay.map not (Delay.map not d) ≈ d`

### 3. Bisimilarity Congruence for Not
```agda
not-preserves-bisim : ∀ {d₁ d₂ : Delay Bool ∞}
  → d₁ ≈ d₂
  → Delay.map not d₁ ≈ Delay.map not d₂
```

**Status**: Probably derivable from Delay.map functor properties
**Need**: This is key for compositional reasoning

### 4. State Correspondence Lemma
**Most Complex**: Relate `foldStepEval-go` with `NotState (NotState st)` to `go` with double `Delay.map not`

```agda
not-not-state-equiv : ∀ (φ : LTL ...) (st : LTLEvalState) (prev : Maybe TimedFrame) (f : TimedFrame) (rest : Colist TimedFrame ∞)
  → [some precondition on st and φ]
  → foldStepEval-go (Not (Not φ)) (NotState (NotState st)) prev f rest
    ≈ Delay.map not (Delay.map not (foldStepEval-go φ st prev f rest))
```

**Challenge**: This requires understanding:
- How `stepEval (Not ψ)` transforms states
- How nested `NotState` corresponds to double `Delay.map not`
- The correspondence between state transitions and delay monad operations

## Why This Is Hard

### 1. Semantic Gap
- **Coinductive**: Pure functional, point-free style with `Delay.map`
- **Incremental**: Stateful, step-by-step evaluation with explicit state types

### 2. State Complexity
`NotState (NotState st)` has nested structure:
- Outer Not: tracks whether inner result should be negated
- Inner Not: tracks whether φ result should be negated
- Combined effect: double negation = identity (semantically)
- But proving this requires understanding state transition sequences!

### 3. Bisimilarity Reasoning
- Not propositional equality (`≡`)
- Coinductive weak bisimilarity (`≈`)
- Requires copattern matching and productivity proofs
- Composition lemmas may not be straightforward

## Possible Approaches

### Approach 1: Direct Proof (Hard)
1. Pattern match on trace (empty vs non-empty)
2. For non-empty: use copattern matching
3. Relate `stepEval` behavior for `NotState (NotState st)` to double `Delay.map not`
4. Use inductive hypothesis for inner `φ`

**Estimated effort**: 3-5 hours per case
**Challenge**: Need to understand state correspondence deeply

### Approach 2: General Bisimilarity Lemmas First (Better)
1. Prove `delay-map-comp` (or find in stdlib)
2. Prove `not-preserves-bisim`
3. Prove general lemma: `Not` preserves bisimilarity
4. Use general lemma for all `Not` compositions

**Estimated effort**: 5-8 hours for lemmas, then 1-2 hours per case
**Benefit**: Reusable lemmas for other cases

### Approach 3: Defer to Phase 4 (Pragmatic)
**Rationale**:
- Temporal operators (Phase 4) are higher priority for real-world use
- Most LTL formulas in practice use `Always`, `Eventually`, not deeply nested `Not`
- Propositional compositions are "nice to have" but less critical

**Estimated effort**: 0 hours now, revisit after Phase 4
**Risk**: Postulates remain longer, but framework is solid

## Recommended Next Steps

### Option A: Research Path (If aiming for completeness)
1. Search standard library for Delay.map properties
2. Implement missing bisimilarity lemmas
3. Prove double negation case using lemmas
4. Apply same approach to other propositional compositions

**Time**: ~10-15 hours
**Value**: Complete propositional operator verification

### Option B: Pragmatic Path (If aiming for high-value proofs)
1. Move to Phase 4 (temporal operators)
2. Temporal proofs likely require similar bisimilarity techniques
3. Research done for temporal operators will help propositional cases later
4. Revisit propositional compositions after Phase 4

**Time**: 0 hours now (defer)
**Value**: Focus on higher-impact temporal operators

## Example: What stdlib Might Provide

Searching for `Codata.Sized.Delay.Properties` or `Codata.Sized.Delay.Bisimilarity`:
- Functor laws for `Delay.map`
- Composition lemmas
- Bisimilarity congruence
- Productivity proofs

**Action**: Need to explore stdlib to see what's available

## Conclusion

**Current Status**: Framework is solid, but compositional proofs require:
1. Understanding Delay.map bisimilarity properties
2. Relating state transformations to functor operations
3. Substantial time investment (~10-20 hours for all propositional cases)

**Recommendation**:
- If goal is completeness → Invest in bisimilarity lemmas (Option A)
- If goal is practical verification → Defer to Phase 4 (Option B)
- Framework allows incremental progress either way

**Decision Point**: What provides most value for the project?
- Deeply nested propositional formulas (rare in practice)
- Temporal operators like `Always` and `Eventually` (common in practice)

Phase 4 likely provides higher ROI.
