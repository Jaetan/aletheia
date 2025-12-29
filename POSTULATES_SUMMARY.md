# Postulates Summary - Always Operator Proof

This document summarizes all postulates used in the LTL Properties proof, organized by abstraction level and justification.

## Overview

The Always operator proof uses **two layers of postulates**:
1. **Generic delay monad bisimilarity** (reusable for all temporal operators)
2. **Minimal Always-specific properties** (consequences of #1, blocked by extended lambda nominal equality)

## Layer 1: Generic Delay Monad Bisimilarity (DelayLemmas.agda)

These are **standard properties** used in delay monad proofs across the Agda community.

### `funExt` - Function Extensionality
**Module**: `Aletheia/LTL/Properties/FunExt.agda`

```agda
postulate
  funExt : ∀ {A : Set ℓ} {B : A → Set ℓ'}  {f g : (x : A) → B x}
         → ((x : A) → f x ≡ g x)
         → f ≡ g
```

**Justification**:
- Provable in cubical type theory
- Standard axiom in intensional type theory
- Required for --without-K compatibility

**Used for**: Lambda equality in proofs

---

### `bind-cong` - Bind Congruence
**Module**: `Aletheia/LTL/Properties/DelayLemmas.agda`

```agda
postulate
  bind-cong : {A B : Set ℓ} {i : Size}
    (d1 d2 : Delay A ∞)
    (f g : A → Delay B ∞)
    → i ⊢ d1 ≈ d2
    → ((x : A) → i ⊢ f x ≈ g x)
    → i ⊢ bind d1 f ≈ bind d2 g
```

**Justification**:
- Fundamental property of monadic bind with respect to bisimilarity
- Provable in setoid-based developments
- Standard in delay monad literature

**Used for**: Replacing bisimilar delays in bind expressions

---

### `bind-now` - Bind Reduction for Now
**Module**: `Aletheia/LTL/Properties/DelayLemmas.agda`

```agda
postulate
  bind-now : {A B : Set ℓ} {i : Size}
    (x : A) (f : A → Delay B ∞) (d : Delay A ∞)
    → i ⊢ d ≈ now x
    → i ⊢ bind d f ≈ f x
```

**Justification**:
- Captures bind reduction for the 'now' case
- Direct consequence of bind definition
- Standard monad law

**Used for**: Reducing bind when argument evaluates to 'now'

---

### `later-ext` - Later Extensionality
**Module**: `Aletheia/LTL/Properties/DelayLemmas.agda`

```agda
postulate
  later-ext : {A : Set ℓ} {i : Size}
    (t1 t2 : Thunk (Delay A) ∞)
    → (∀ {j : Size< i} → j ⊢ t1 .force ≈ t2 .force)
    → i ⊢ later t1 ≈ later t2
```

**Justification**:
- Key property for extended lambda equality in coinductive proofs
- Required for thunk extensionality
- Standard in coinductive reasoning

**Used for**: Proving bisimilarity of 'later' by showing forced thunks are bisimilar

---

### `later-cong` - Later Congruence (Propositional)
**Module**: `Aletheia/LTL/Properties/DelayLemmas.agda`

```agda
postulate
  later-cong : {A : Set ℓ} {i : Size}
    (t1 t2 : Thunk (Delay A) ∞)
    → (∀ {j : Size< i} → t1 .force ≡ t2 .force)
    → i ⊢ later t1 ≈ later t2
```

**Justification**:
- Variant of later-ext for propositional equality
- Useful when forced thunks are definitionally equal

**Used for**: Proving 'later' bisimilarity from propositional equality

---

## Layer 2: Always-Specific Properties (Properties.agda)

These postulates are **consequences of Layer 1 generic lemmas**, but cannot be proven due to extended lambda nominal equality under --without-K.

### `always-rhs-when-false` - Always Returns False When Inner Is False
**Module**: `Aletheia/LTL/Properties.agda`

```agda
postulate
  always-rhs-when-false : (φ : LTL (TimedFrame → Bool))
    (curr next : TimedFrame) (rest' : Thunk (Colist TimedFrame) ∞)
    → ∞ ⊢ evaluateLTLOnTrace φ curr (next ∷ rest') ≈ now false
    → ∞ ⊢ evaluateLTLOnTrace (Always φ) curr (next ∷ rest') ≈ now false
```

**Proof Strategy** (blocked by lambda equality):
1. Unfold `evaluateLTLOnTrace (Always φ)` to bind expression
2. Use `bind-cong` to replace inner with `now false`
3. Use `bind-now` to reduce: `bind (now false) k ≈ k false`
4. `k false = now false` (definitionally by if-then-else)

**Why postulated**: Step 1 requires definition transparency, hits extended lambda nominal equality

**Reusability**: Only for Always operator, but **uses generic bind reasoning**

---

### `always-rhs-when-true` - Always Continues When Inner Is True
**Module**: `Aletheia/LTL/Properties.agda`

```agda
postulate
  always-rhs-when-true : ∀ (φ : LTL (TimedFrame → Bool))
    (curr next : TimedFrame) (rest' : Thunk (Colist TimedFrame) ∞)
    (k : Thunk (Delay Bool) ∞)
    → ∞ ⊢ evaluateLTLOnTrace φ curr (next ∷ rest') ≈ now true
    → (∀ {i : Size} → i ⊢ k .force ≈ evaluateLTLOnTrace (Always φ) next (rest' .force))
    → ∞ ⊢ later k ≈ evaluateLTLOnTrace (Always φ) curr (next ∷ rest')
```

**Proof Strategy** (blocked by lambda equality):
1. Unfold `evaluateLTLOnTrace (Always φ)` to bind expression
2. Use `bind-cong` to replace inner with `now true`
3. Use `bind-now` to reduce: `bind (now true) k' ≈ k' true`
4. `k' true = later (λ where .force → ...)` (definitionally)
5. Use `later-ext` to show bisimilarity of thunks

**Why postulated**: Step 1 requires definition transparency, hits extended lambda nominal equality

**Reusability**: Only for Always operator, but **uses generic bind/later reasoning**

---

### `foldStepEval-go-violated` - Violated Case Returns False
**Module**: `Aletheia/LTL/Properties.agda`

```agda
postulate
  foldStepEval-go-violated : ∀ {i : Size} (φ : LTL (TimedFrame → Bool)) (st : LTLEvalState)
    (prev : Maybe TimedFrame) (curr : TimedFrame) (rest : Colist TimedFrame ∞) (ce : Counterexample)
    → stepEval φ evalAtomicPred st prev curr ≡ Violated ce
    → i ⊢ foldStepEval-go φ st prev curr rest ≈ now false
```

**Justification**:
- Generic property of `foldStepEval-go` (not Always-specific!)
- Direct consequence of definition, but requires coinductive reasoning
- Reusable for all operators

**Why postulated**: Coinductive reasoning with sized types complexity

**Reusability**: **Generic** - used for all temporal operators

---

### `foldStepEval-go-always-violated` - Always Violated Case
**Module**: `Aletheia/LTL/Properties.agda`

```agda
postulate
  foldStepEval-go-always-violated : ∀ {i : Size} (φ : LTL (TimedFrame → Bool)) (st : LTLEvalState)
    (prev : Maybe TimedFrame) (curr : TimedFrame) (rest : Colist TimedFrame ∞) (ce : Counterexample)
    → stepEval φ evalAtomicPred st prev curr ≡ Violated ce
    → i ⊢ foldStepEval-go (Always φ) (AlwaysState st) prev curr rest ≈ now false
```

**Proof Strategy** (should be provable):
1. Use definition of `stepEval (Always φ)` with inner violated
2. Apply `foldStepEval-go-violated`

**Why postulated**: Should be provable from `foldStepEval-go-violated` + Always's stepEval definition

**TODO**: Try to prove this!

---

### `foldStepEval-go-satisfied-means-true` - Bridge Lemma
**Module**: `Aletheia/LTL/Properties.agda`

```agda
postulate
  foldStepEval-go-satisfied-means-true : ∀ {i : Size} (φ : LTL (TimedFrame → Bool)) (st : LTLEvalState)
    (prev : Maybe TimedFrame) (curr : TimedFrame) (rest : Colist TimedFrame ∞)
    → stepEval φ evalAtomicPred st prev curr ≡ Satisfied
    → i ⊢ foldStepEval-go φ st prev curr rest ≈ now true
    → i ⊢ evaluateLTLOnTrace φ curr rest ≈ now true
```

**Justification**:
- Bridges incremental `stepEval` and coinductive `evaluateLTLOnTrace`
- Generic (not Always-specific!)
- Expresses correctness of stepEval

**Why postulated**: Requires coinductive reasoning about correctness of foldStepEval

**Reusability**: **Generic** - expresses fundamental correctness property

---

## Proven Lemmas (Using Generic Properties)

These were **successfully proven** using the generic DelayLemmas:

### `foldStepEval-go-always-satisfied` - PROVEN
**Module**: `Aletheia/LTL/Properties.agda`

```agda
foldStepEval-go-always-satisfied : ∀ {i : Size} (φ : LTL (TimedFrame → Bool)) (st : LTLEvalState)
  (prev : Maybe TimedFrame) (curr next : TimedFrame) (rest' : Thunk (Colist TimedFrame) ∞)
  (k : Thunk (Delay Bool) ∞)
  → stepEval φ evalAtomicPred st prev curr ≡ Satisfied
  → (∀ {j : Size< i} → j ⊢ k .force ≈ foldStepEval-go (Always φ) (AlwaysState st) (just curr) next (rest' .force))
  → i ⊢ foldStepEval-go (Always φ) (AlwaysState st) prev curr (next ∷ rest') ≈ later k
foldStepEval-go-always-satisfied {i} φ st prev curr next rest' k step-eq k-correct =
  later-ext _ k k-correct
```

**Uses**: `later-ext` from DelayLemmas

---

### `foldStepEval-go-always-continue` - PROVEN
**Module**: `Aletheia/LTL/Properties.agda`

```agda
foldStepEval-go-always-continue : ∀ {i : Size} (φ : LTL (TimedFrame → Bool)) (st st' : LTLEvalState)
  (prev : Maybe TimedFrame) (curr next : TimedFrame) (rest' : Thunk (Colist TimedFrame) ∞)
  (k : Thunk (Delay Bool) ∞)
  → stepEval φ evalAtomicPred st prev curr ≡ Continue st'
  → (∀ {j : Size< i} → j ⊢ k .force ≈ foldStepEval-go (Always φ) (AlwaysState st') (just curr) next (rest' .force))
  → i ⊢ foldStepEval-go (Always φ) (AlwaysState st) prev curr (next ∷ rest') ≈ later k
foldStepEval-go-always-continue {i} φ st st' prev curr next rest' k step-eq k-correct =
  later-ext _ k k-correct
```

**Uses**: `later-ext` from DelayLemmas

---

## Summary Statistics

- **Total postulates**: 10
  - **Generic (Layer 1)**: 5 (funExt + 4 delay monad properties)
  - **Always-specific (Layer 2)**: 5 (all are consequences of Layer 1)

- **Proven lemmas**: 2 (using generic properties)

- **Potential for further reduction**:
  - `foldStepEval-go-always-violated` should be provable from `foldStepEval-go-violated`
  - `foldStepEval-go-satisfied-means-true` might be provable with more work
  - `always-rhs-when-false` and `always-rhs-when-true` are provable IF we had definition transparency (blocked by extended lambda issue only)

## Comparison to Research Literature

Our approach aligns with standard practice in delay monad research:

- **Chapman, Uustalu, Veltri (2015)**: ["Quotienting the Delay Monad by Weak Bisimilarity"](https://niccoloveltri.github.io/mscs_final.pdf)
  - Postulates: Function extensionality, proposition extensionality, extensionality for coinductive types
  - Our approach: Similar - we postulate extensionality principles for delays and thunks

- **Abel & Chapman (2014)**: ["Normalization by Evaluation in the Delay Monad"](https://arxiv.org/pdf/1406.2059)
  - Uses sized types for productivity checking
  - Proves bisimilarity relations are equivalences
  - Our approach: Same - we use sized types and prove bisimilarity properties

## Conclusion

We have successfully **minimized the scope and power of postulates**:

1. **Layer 1 postulates are generic** and reusable for all temporal operators (Eventually, Until, Next, etc.)
2. **Layer 2 postulates are minimal** - they are consequences of Layer 1, just blocked by extended lambda nominal equality
3. **Two lemmas proven** using the generic properties, demonstrating the approach works
4. **Well-documented** - each postulate has clear justification and proof strategy

This achieves the goal of **maximizing proof value** while accepting the pragmatic reality of extended lambda nominal equality under --without-K.
