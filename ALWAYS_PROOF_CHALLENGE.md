# Always Operator Proof Challenge

**Date**: 2025-12-27
**Status**: Implementation started, discovered fundamental complexity

## Problem Statement

Proving `always-fold-equiv` requires relating two fundamentally different evaluation strategies:

1. **LHS (Incremental)**: Pattern matching on `StepResult` (Continue/Violated/Satisfied)
2. **RHS (Coinductive)**: Using `bind` with `Delay Bool` values

## The Mismatch

**Incremental evaluation:**
```agda
foldStepEval-go (Always φ) (AlwaysState st) nothing f (next ∷ rest')
  -- Calls stepEval (Always φ) which calls stepEval φ:
  --   stepEval φ returns: Continue st' | Violated ce | Satisfied
  --   stepEval (Always φ) maps this to:
  --     Continue st' → Continue (AlwaysState st')
  --     Violated ce → Violated ce
  --     Satisfied → Continue (AlwaysState st)
  -- Then foldStepEval-go processes the Always result:
  --   Continue (AlwaysState st') → later (recurse with st')
  --   Violated ce → now false
```

**Coinductive evaluation:**
```agda
evaluateLTLOnTrace (Always ψ) f (next ∷ rest') =
  bind (evaluateLTLOnTrace ψ f (next ∷ rest')) λ r →
    if r
      then (later λ where .force → evaluateLTLOnTrace (Always ψ) next (rest' .force))
      else now false
```

## The Challenge

`bind-cong` expects both sides to use `bind`, but the LHS doesn't literally use `bind` - it pattern matches on `StepResult`.

We have:
- `fold-equiv φ (f ∷ next ∷ rest')` gives us:
  ```agda
  later (foldStepEval-go φ (initState φ) nothing f (next ∷ rest'))
    ≈ evaluateLTLOnTrace φ f (next ∷ rest')
  ```

- But we need to relate:
  - Incremental: Pattern match on `stepEval φ` result → do different things
  - Coinductive: `bind (evaluateLTLOnTrace φ) (λ r → if r then ... else ...)  `

## Missing Lemmas

We need lemmas that connect `StepResult` to `Delay Bool`:

1. **Violated case**:
   ```agda
   stepEval-violated-gives-now-false :
     stepEval φ eval st prev curr ≡ Violated ce
     → foldStepEval-go φ st prev curr rest ≈ now false
   ```

2. **Satisfied case**:
   ```agda
   stepEval-satisfied-gives-now-true :
     stepEval φ eval st prev curr ≡ Satisfied
     → foldStepEval-go φ st prev curr [] ≈ now true
   ```

3. **Continue case** (more complex):
   - Need to relate continuing with state `st'` to the Delay value

## Alternative Approach

Instead of using `bind-cong` directly, we might need to:

1. **Inline the bind definition** and show the reduction steps manually
2. **Pattern match on both sides** - match on `stepEval φ` result AND on the shape of `evaluateLTLOnTrace φ`
3. **Use transitivity** - show LHS ≈ intermediate form ≈ RHS

## Key Insight from fold-equiv

When we pattern match on `stepEval φ (initState φ) nothing f` returning `Violated/Satisfied/Continue st'`, we simultaneously pattern match on `fold-equiv φ (f ∷ next ∷ rest')` which is `DB.later prf`.

The `prf .force` tells us:
```agda
foldStepEval-go φ (initState φ) nothing f (next ∷ rest') ≈ [unwrapped evaluateLTLOnTrace]
```

But `foldStepEval-go` pattern matches on the `stepEval φ` result internally, so:
- If `stepEval φ` returns `Violated`: foldStepEval-go returns `now false`
- If `stepEval φ` returns `Satisfied`: foldStepEval-go returns `now true`
- If `stepEval φ` returns `Continue st'`: foldStepEval-go returns `later (recurse with st')`

So `prf .force` gives us:
- Violated case: `now false ≈ [evaluateLTLOnTrace φ unwrapped]`
- Satisfied case: `now true ≈ [evaluateLTLOnTrace φ unwrapped]`
- Continue case: `later (...) ≈ [evaluateLTLOnTrace φ unwrapped]`

## Next Steps

1. **Try using prf .force directly** in each case to get the bisimilarity
2. **Apply bind definition** manually to reduce the RHS
3. **Use bind-cong only on the simplified form** after we've exposed the structure

## Concrete Plan for Violated Case

```agda
-- Case 1: Violated
... | Violated ce | DB.later prf =
  -- We have: stepEval φ (initState φ) nothing f ≡ Violated ce (from pattern match)
  --
  -- LHS: foldStepEval-go (Always φ) (AlwaysState (initState φ)) nothing f (next ∷ rest')
  --   = [stepEval (Always φ) calls stepEval φ which returns Violated ce]
  --   = [stepEval (Always φ) returns Violated ce]
  --   = [foldStepEval-go processes Violated]
  --   = now false
  --
  -- RHS: evaluateLTLOnTrace (Always φ) f (next ∷ rest')
  --   = bind (evaluateLTLOnTrace φ f (next ∷ rest')) (λ r → if r then ... else now false)
  --
  -- From prf .force, we know:
  --   foldStepEval-go φ (initState φ) nothing f (next ∷ rest') ≈ [unwrapped evaluateLTLOnTrace φ]
  -- And since stepEval φ returned Violated, foldStepEval-go φ reduces to now false
  -- So: now false ≈ [unwrapped evaluateLTLOnTrace φ f (next ∷ rest')]
  --
  -- This means evaluateLTLOnTrace φ must reduce to later (now false) or now false
  -- Then bind (now false) (λ r → ...) = now false (by bind definition)
  -- Or bind (later (... now false)) (...) = later (bind (... now false) (...)) = ... = later (now false)
  --
  -- We need to use prf and bind-cong (or manual bind reduction) to show:
  --   bind (evaluateLTLOnTrace φ ...) (...) ≈ now false

  {!!}
```

## Status

**Current**: Proof skeleton with holes in Properties.agda:617, :621, :632
**Next**: Implement Violated case using prf .force and bind reasoning
**Estimated time**: 2-4 hours (more complex than initially estimated)

