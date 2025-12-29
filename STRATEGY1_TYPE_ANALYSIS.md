# Strategy 1: State Correspondence - Type-Level Analysis

**Date**: 2025-12-29
**Goal**: Analyze what lemmas we need, what StateCorrespondence can provide, and how to compose them to fill our proof holes

---

## Part 1: Understanding the Holes

### The Coinductive Definition We're Comparing To

```agda
evaluateLTLOnTrace (Always ψ) frame (next ∷ rest') =
  bind (evaluateLTLOnTrace ψ frame (next ∷ rest')) λ r →
    if r
      then (later λ where .force → evaluateLTLOnTrace (Always ψ) next (rest' .force))
      else now false
```

**Key observation**: The continuation `λ r → if r then ... else now false` is where "state" is encoded.

### Hole 1: False Case (Properties.agda:609)

**What we need to prove**:
```agda
rhs-reduces-to-false : ∞ ⊢ now false ≈ evaluateLTLOnTrace (Always φ) f (next ∷ rest')
```

**What we know**:
```agda
inner-eq : ∞ ⊢ evaluateLTLOnTrace φ f (next ∷ rest') ≈ now false
step-eq  : stepEval φ evalAtomicPred (initState φ) nothing f ≡ Violated ce
```

**Coinductive expansion**:
```agda
evaluateLTLOnTrace (Always φ) f (next ∷ rest')
  = bind (evaluateLTLOnTrace φ f (next ∷ rest')) λ r →
      if r then later ... else now false
  ≈ bind (now false) λ r → if r then later ... else now false
  ≈ (λ r → if r then later ... else now false) false   -- by bind-now
  = if false then later ... else now false
  = now false
```

**Type of lemma we need**:
```agda
always-bind-false : ∀ φ f next rest'
  → ∞ ⊢ evaluateLTLOnTrace φ f (next ∷ rest') ≈ now false
  → ∞ ⊢ evaluateLTLOnTrace (Always φ) f (next ∷ rest') ≈ now false
```

**Does this need StateCorrespondence?** NO - this is purely about bind reduction and β-equality of the continuation!

---

### Hole 2: Satisfied Case (Properties.agda:641)

**What we need to prove**:
```agda
rhs-reduces-to-true : ∞ ⊢ later k-satisfied ≈ evaluateLTLOnTrace (Always φ) f (next ∷ rest')
where
  k-satisfied .force = foldStepEval-go (Always φ) (AlwaysState (initState φ)) (just f) next (rest' .force)
```

**What we know**:
```agda
inner-eq : ∞ ⊢ evaluateLTLOnTrace φ f (next ∷ rest') ≈ now true
step-eq  : stepEval φ evalAtomicPred (initState φ) nothing f ≡ Satisfied
helper   : ∀ {i} → i ⊢ k-satisfied .force ≈ evaluateLTLOnTrace (Always φ) next (rest' .force)
```

**Coinductive expansion**:
```agda
evaluateLTLOnTrace (Always φ) f (next ∷ rest')
  = bind (evaluateLTLOnTrace φ f (next ∷ rest')) λ r →
      if r then later (λ where .force → evaluateLTLOnTrace (Always φ) next (rest' .force)) else now false
  ≈ bind (now true) λ r → if r then later ... else now false
  ≈ (λ r → if r then later ... else now false) true   -- by bind-now
  = if true then later (λ where .force → evaluateLTLOnTrace (Always φ) next (rest' .force)) else now false
  = later (λ where .force → evaluateLTLOnTrace (Always φ) next (rest' .force))
```

**Type of lemma we need**:
```agda
always-bind-true : ∀ φ f next rest' k
  → ∞ ⊢ evaluateLTLOnTrace φ f (next ∷ rest') ≈ now true
  → (∀ {i} → i ⊢ k .force ≈ evaluateLTLOnTrace (Always φ) next (rest' .force))
  → ∞ ⊢ later k ≈ evaluateLTLOnTrace (Always φ) f (next ∷ rest')
```

**Does this need StateCorrespondence?** NO for the outer structure - just bind reduction and later-ext!
But the `helper` proof DOES need it (see below).

---

### Hole 3: Continue Case (Properties.agda:668) **THE CHALLENGE**

**What we need to prove**:
```agda
rhs-continues : ∞ ⊢ later k-continue ≈ evaluateLTLOnTrace (Always φ) f (next ∷ rest')
where
  k-continue .force = foldStepEval-go (Always φ) (AlwaysState st') (just f) next (rest' .force)
  step-eq : stepEval φ evalAtomicPred (initState φ) nothing f ≡ Continue st'
```

**What we know**:
```agda
step-eq : stepEval φ evalAtomicPred (initState φ) nothing f ≡ Continue st'
```

**What we DON'T know**:
- What is `evaluateLTLOnTrace φ f (next ∷ rest')` in this case?
- We know `stepEval φ ... ≡ Continue st'`, but what does that tell us about the coinductive evaluation?

**The problem**: When `stepEval φ ... ≡ Continue st'`, the inner formula φ didn't finish evaluating. So what is `evaluateLTLOnTrace φ f (next ∷ rest')`?

**Answer**: It must be `later (λ where .force → ...)` for some delayed computation!

**Critical insight**: We need to know:
```agda
Continue st' corresponds to coinductive: later (λ where .force → <some-computation-encoding-st'>)
```

**Type of lemma we need**:
```agda
-- When stepEval returns Continue st', what does evaluateLTLOnTrace return?
stepEval-continue-correspondence : ∀ φ st f next rest'
  → stepEval φ evalAtomicPred st nothing f ≡ Continue st'
  → ∃[ k ] (  ∞ ⊢ evaluateLTLOnTrace φ f (next ∷ rest') ≈ later k
           ×  (∀ {i} → i ⊢ k .force ≈ <coinductive-computation-representing-st'>)  )
```

**This DOES need StateCorrespondence!** We need to relate `st'` to the delayed computation.

---

## Part 2: What StateCorrespondence Should Provide

### Option A: Direct State-to-Computation Mapping

```agda
StateCorrespondence : (φ : LTL (TimedFrame → Bool))
                    → LTLEvalState
                    → (TimedFrame → Colist TimedFrame ∞ → Delay Bool ∞)
                    → Set

-- Example for Always:
StateCorrespondence (Always ψ) (AlwaysState st) k  =
  ∀ f rest → k f rest ≈ <what should this be?>
```

**Problem**: What is the RHS? We don't have a "coinductive evaluation with state st" - the coinductive side doesn't have states!

### Option B: Relate States to Evaluation Results

Instead of mapping states to computations, relate states to evaluation behavior:

```agda
-- A state 'st' corresponds to a delayed computation 'd' if:
-- evaluating with 'st' incrementally gives the same result as evaluating 'd' coinductively
StateCorrespondence : (φ : LTL (TimedFrame → Bool))
                    → LTLEvalState
                    → (curr : TimedFrame)
                    → (rest : Colist TimedFrame ∞)
                    → (d : Delay Bool ∞)
                    → Set

StateCorrespondence φ st curr rest d =
  ∀ {i} → i ⊢ foldStepEval-go φ st (just prev) curr rest ≈ d
```

**Problem**: This is just the bisimilarity we're trying to prove! Circular.

### Option C: Relate States to Continuation Invariants

The key insight: A state `st` in incremental evaluation represents **how much of the formula has been evaluated**. In coinductive evaluation, this is represented by **which part of the formula we're evaluating**.

For Always specifically:
- `AlwaysState st` means "we're checking Always, and the inner φ is at state st"
- Coinductively, this is: `bind (evaluateLTLOnTrace φ ...) λ r → if r then later ... else now false`
  where the inner `evaluateLTLOnTrace φ ...` is at the "position" corresponding to st

```agda
-- State st corresponds to position in evaluation
-- For Always: the state is just the state of the inner formula
StateCorrespondence : (φ : LTL (TimedFrame → Bool))
                    → LTLEvalState
                    → (curr : TimedFrame)
                    → (rest : Colist TimedFrame ∞)
                    → Set

StateCorrespondence φ (AlwaysState st) curr rest =
  -- The inner formula at state st corresponds to some delayed computation
  ∃[ d ] (  StateCorrespondence φ st curr rest d
         ×  (∀ {i} → i ⊢ evaluateLTLOnTrace (Always φ) curr rest
                       ≈ bind d λ r → if r then later ... else now false)  )
```

**Problem**: Still recursive! And we still don't know how to relate `st` to `d` for the base case φ.

---

## Part 3: The Fundamental Challenge

### Why StateCorrespondence is Hard

The problem is **asymmetry**:

**Incremental side**:
- Has explicit states: `Continue st'`
- State st' is a **data structure** (AlwaysState, UntilState, etc.)
- State encodes "where we are in the evaluation"

**Coinductive side**:
- No explicit states
- "Where we are" is encoded in **which computation we're running**
- State is implicit in the continuation closure

### The Gap

When we have:
```agda
stepEval φ evalAtomicPred (initState φ) nothing f ≡ Continue st'
```

We need to know:
```agda
evaluateLTLOnTrace φ f (next ∷ rest') ≈ <what?>
```

**The issue**: `evaluateLTLOnTrace` doesn't take a state parameter! It ALWAYS starts fresh with the formula φ and the trace.

**Wait, is that the problem?**

Let me check: When `stepEval φ ... ≡ Continue st'`, we're evaluating φ on frame f.

What does `evaluateLTLOnTrace φ f (next ∷ rest')` compute?
- It evaluates φ on the trace starting with f, looking ahead to next

But stepEval is evaluating φ on just the single frame f (with prev context).

**These are different things!**

---

## Part 4: Reconsidering the Problem

### What stepEval Actually Does

```agda
stepEval : LTL Atom → (evaluator) → LTLEvalState → Maybe TimedFrame → TimedFrame → StepResult
```

For `Always φ`:
```agda
stepEval (Always φ) eval (AlwaysState st) prev curr
  with stepEval φ eval st prev curr
... | Continue st' = Continue (AlwaysState st')
... | Violated ce = Violated ce
... | Satisfied = Continue (AlwaysState st)  -- Preserves state
```

**Key point**: `stepEval` evaluates φ on a **single frame** `curr`, producing:
- `Continue st'` if φ needs more frames
- `Satisfied` if φ is satisfied on this frame
- `Violated` if φ is violated

### What evaluateLTLOnTrace Does

```agda
evaluateLTLOnTrace φ frame (next ∷ rest')
```

Evaluates φ on the **entire trace** starting with frame, looking ahead to next and rest'.

### The Correspondence

**Incremental**: processes trace frame by frame, accumulating state
**Coinductive**: processes entire trace at once, recursively

The question is: if we've processed frames 0..i incrementally and are at state `st`, does evaluating coinductively on frames i+1... give the same result?

**This suggests a different formulation!**

---

## Part 5: Alternative Formulation - Trace Splitting

### The Real Correspondence

```agda
-- If incremental evaluation reached state st after processing prefix,
-- then continuing incrementally from st on suffix
-- gives the same result as evaluating coinductively on suffix
TraceCorrespondence : (φ : LTL (TimedFrame → Bool))
                    → (prefix : List TimedFrame)  -- Already processed
                    → (st : LTLEvalState)         -- State after processing prefix
                    → (suffix : Colist TimedFrame ∞)  -- Remaining trace
                    → Set

TraceCorrespondence φ prefix st suffix =
  ∀ {i} → i ⊢ foldStepEval-go φ st (last prefix) (head suffix) (tail suffix)
            ≈ evaluateLTLOnTrace φ (head suffix) (tail suffix)
```

**Wait, this doesn't work either!** The coinductive side always starts fresh from φ, not from "φ at state st".

---

## Part 6: The Core Issue - Coinductive Always Structure

Let me trace through what happens:

**Incremental Always with Continue**:
```
Frame 0: stepEval φ (initState φ) ≡ Continue st₀  →  Continue (AlwaysState st₀)
Frame 1: stepEval φ st₀ ≡ Continue st₁  →  Continue (AlwaysState st₁)
Frame 2: stepEval φ st₁ ≡ Continue st₂  →  Continue (AlwaysState st₂)
...
```

**Coinductive Always**:
```agda
-- Frame 0:
evaluateLTLOnTrace (Always φ) f₀ (f₁ ∷ f₂ ∷ ...)
  = bind (evaluateLTLOnTrace φ f₀ (f₁ ∷ f₂ ∷ ...)) λ r →
      if r then later (λ .force → evaluateLTLOnTrace (Always φ) f₁ (f₂ ∷ ...))
           else now false

-- If evaluateLTLOnTrace φ f₀ ... ≈ later k₀ (because φ continues):
  = bind (later k₀) λ r → if r then later ... else now false
  = later (bind (k₀ .force) λ r → if r then later ... else now false)  -- by bind-later
```

**So when φ continues, the whole Always computation becomes `later (...)`**

**The continuation contains**:
```agda
bind (k₀ .force) λ r → if r then later (evaluateLTLOnTrace (Always φ) f₁ ...) else now false
```

Where `k₀ .force` is the continuation of evaluating φ from frame 0.

**This is the state!** The state is encoded in the continuation `k₀ .force`.

---

## Part 7: Refined Strategy - Focus on Inner Formula State

### Key Insight

For `Always φ`:
- Incremental state is `AlwaysState st` where `st` is φ's state
- Coinductive "state" is the delayed computation of φ

**We need**: A correspondence between φ's state `st` and φ's delayed computation `d`:

```agda
InnerStateCorrespondence : (φ : LTL (TimedFrame → Bool))
                         → LTLEvalState  -- Inner formula state
                         → TimedFrame
                         → Colist TimedFrame ∞
                         → Delay Bool ∞  -- Inner formula's delayed computation
                         → Set

InnerStateCorrespondence φ st curr rest d =
  ∀ {i} → i ⊢ foldStepEval-go φ st (just prev) curr rest ≈ d
```

**Then for Always**:

```agda
-- If inner φ at state st corresponds to delayed computation d
-- Then Always (AlwaysState st) corresponds to:
--   bind d λ r → if r then later (Always φ on next frame) else now false
```

**But wait**, this is STILL circular! We need `InnerStateCorrespondence` for φ, but φ might itself be `Always ψ`, which needs `InnerStateCorrespondence` for ψ, etc.

**Unless...** we prove it by mutual recursion on the formula structure!

---

## Part 8: Mutual Recursion Approach (Promising!)

### The Idea

Prove correspondence for all operators simultaneously by mutual recursion:

```agda
mutual
  -- For atomic formulas: state is trivial, no correspondence needed
  correspondence-atomic : ...

  -- For Always: if we have correspondence for φ, we can prove it for Always φ
  correspondence-always : (φ : LTL (TimedFrame → Bool))
    → (∀ st → InnerStateCorrespondence φ st ...)  -- IH: correspondence for φ
    → (∀ st → InnerStateCorrespondence (Always φ) (AlwaysState st) ...)

  -- For Eventually, Until, etc.
  correspondence-eventually : ...
  correspondence-until : ...
```

### For Always Specifically

Given:
- `stepEval φ evalAtomicPred (initState φ) nothing f ≡ Continue st'`
- IH: `InnerStateCorrespondence φ st' curr rest d` (for some d)

We need to show:
```agda
evaluateLTLOnTrace (Always φ) f (next ∷ rest')
  = bind (evaluateLTLOnTrace φ f (next ∷ rest')) λ r → if r then later ... else now false
  ≈ bind d λ r → if r then later (evaluateLTLOnTrace (Always φ) next ...) else now false
  = <what the LHS should reduce to>
```

**Wait, the LHS is**:
```agda
foldStepEval-go (Always φ) (AlwaysState st') (just f) next (rest' .force)
```

**The RHS is**:
```agda
evaluateLTLOnTrace (Always φ) f (next ∷ rest')
  = bind (evaluateLTLOnTrace φ f (next ∷ rest')) λ r → ...
```

**The bridge**: We need to know that `evaluateLTLOnTrace φ f (next ∷ rest') ≈ d` where `d` corresponds to state `st'`.

**But how do we get that?** We know:
- `stepEval φ (initState φ) nothing f ≡ Continue st'`

We need:
- `evaluateLTLOnTrace φ f (next ∷ rest') ≈ <delayed computation corresponding to st'>`

**This requires knowing the connection between stepEval and evaluateLTLOnTrace!**

---

## Part 9: The Missing Link

### What We're Missing

We have two evaluation functions:
1. `stepEval` : processes one frame, returns StepResult
2. `evaluateLTLOnTrace` : processes entire trace, returns Delay Bool

**We're trying to prove they're equivalent**, but to do so, we need to understand how stepEval results relate to evaluateLTLOnTrace results.

Specifically:
```agda
-- If stepEval on frame f returns Continue st', what can we say about evaluateLTLOnTrace on f?
stepEval-to-trace : (φ : LTL (TimedFrame → Bool))
  → (st : LTLEvalState)
  → (prev : Maybe TimedFrame)
  → (curr : TimedFrame)
  → (next : TimedFrame)
  → (rest' : Thunk (Colist TimedFrame) ∞)
  → stepEval φ evalAtomicPred st prev curr ≡ Continue st'
  → ∃[ k ] (  ∞ ⊢ evaluateLTLOnTrace φ curr (next ∷ rest') ≈ later k
           ×  InnerStateCorrespondence φ st' next (rest' .force) (k .force)  )
```

**But this is what we're trying to prove!** It's circular.

---

## Part 10: Stepping Back - What CAN We Prove Without Postulates?

### Observation 1: Bind Structure

We CAN prove that `evaluateLTLOnTrace (Always φ)` has the bind structure:

```agda
always-bind-structure : ∀ φ f next rest'
  → ∃[ k ] (  ∞ ⊢ evaluateLTLOnTrace (Always φ) f (next ∷ rest')
                ≈ bind (evaluateLTLOnTrace φ f (next ∷ rest')) (λ r → if r then later k else now false)
           ×  (∀ {i} → i ⊢ k .force ≈ evaluateLTLOnTrace (Always φ) next (rest' .force))  )
```

**Proof**: By definition! It's literally what evaluateLTLOnTrace (Always φ) computes.

**Problem**: This involves extended lambda equality in the continuation, which we can't prove.

### Observation 2: Cases We CAN Handle

**False case**: If `evaluateLTLOnTrace φ ... ≈ now false`, then:
```agda
bind (now false) (λ r → if r then later k else now false)
  = (λ r → if r then later k else now false) false   -- bind-now
  = if false then later k else now false
  = now false
```

**This works!** We can prove the false case using just `bind-now` and β-reduction.

**True case**: If `evaluateLTLOnTrace φ ... ≈ now true`, then:
```agda
bind (now true) (λ r → if r then later k else now false)
  = (λ r → if r then later k else now false) true   -- bind-now
  = if true then later k else now false
  = later k
```

**This works too!** We can prove the true case using `bind-now`, β-reduction, and `later-ext` to relate k to the desired thunk.

### Observation 3: The ONLY Problem is Continue

When φ continues (doesn't finish on this frame), we have:
```agda
evaluateLTLOnTrace φ f (next ∷ rest') ≈ later k'  -- for some k'
```

Then:
```agda
bind (later k') (λ r → if r then later k else now false)
  = later (bind (k' .force) (λ r → if r then later k else now false))  -- bind-later
```

**Problem**: We need to relate this delayed bind to the LHS, which is:
```agda
foldStepEval-go (Always φ) (AlwaysState st') (just f) next (rest' .force)
```

Where `st'` is the state from `stepEval φ ... ≡ Continue st'`.

---

## Part 11: Conclusion - What We Actually Need

### Summary of Findings

1. **False and True cases DON'T need StateCorrespondence** - just bind reduction lemmas!

2. **Continue case DOES need something**, but it's not clear what.

3. **The fundamental issue**: We're relating two different evaluation models:
   - Incremental: stateful, processes frame-by-frame
   - Coinductive: stateless, processes entire trace

4. **StateCorrespondence as originally conceived is too strong/circular**

### Minimal Lemmas Needed (Type Signatures)

**Lemma 1: Always with False Inner** (fills Hole 1)
```agda
always-bind-false : (φ : LTL (TimedFrame → Bool))
  → (f next : TimedFrame) (rest' : Thunk (Colist TimedFrame) ∞)
  → ∞ ⊢ evaluateLTLOnTrace φ f (next ∷ rest') ≈ now false
  → ∞ ⊢ evaluateLTLOnTrace (Always φ) f (next ∷ rest') ≈ now false
```

**Proof sketch**: Expand Always definition, use bind-now, β-reduce continuation.
**Needs**: `bind-now` postulate + β-equality for continuation
**Status**: Should be provable with bind-now, but blocked by extended lambda equality

**Lemma 2: Always with True Inner** (fills Hole 2)
```agda
always-bind-true : (φ : LTL (TimedFrame → Bool))
  → (f next : TimedFrame) (rest' : Thunk (Colist TimedFrame) ∞)
  → (k : Thunk (Delay Bool) ∞)
  → ∞ ⊢ evaluateLTLOnTrace φ f (next ∷ rest') ≈ now true
  → (∀ {i} → i ⊢ k .force ≈ evaluateLTLOnTrace (Always φ) next (rest' .force))
  → ∞ ⊢ later k ≈ evaluateLTLOnTrace (Always φ) f (next ∷ rest')
```

**Proof sketch**: Expand Always definition, use bind-now, β-reduce, use later-ext for thunk.
**Needs**: `bind-now`, `later-ext`, β-equality for continuation
**Status**: Should be provable with existing postulates, but blocked by extended lambda equality

**Lemma 3: Always with Continue Inner** (fills Hole 3) **THE HARD ONE**
```agda
always-bind-continue : (φ : LTL (TimedFrame → Bool))
  → (st' : LTLEvalState)
  → (f next : TimedFrame) (rest' : Thunk (Colist TimedFrame) ∞)
  → (k-inner k-outer : Thunk (Delay Bool) ∞)
  → stepEval φ evalAtomicPred (initState φ) nothing f ≡ Continue st'
  → (∀ {i} → i ⊢ k-inner .force ≈ evaluateLTLOnTrace φ ??? ???)  -- What goes here???
  → (∀ {i} → i ⊢ k-outer .force ≈ foldStepEval-go (Always φ) (AlwaysState st') (just f) next (rest' .force))
  → ∞ ⊢ later k-outer ≈ evaluateLTLOnTrace (Always φ) f (next ∷ rest')
```

**The problem**: When stepEval returns Continue st', what is `evaluateLTLOnTrace φ f (next ∷ rest')`?

**Critical question**: Is there even a relation between stepEval result and evaluateLTLOnTrace result for the SAME frame?

---

## Part 12: Next Steps - Research Questions

Before implementing, we need to answer:

1. **When `stepEval φ st prev curr ≡ Continue st'`, what can we say about `evaluateLTLOnTrace φ curr rest`?**
   - Are they even comparable?
   - stepEval looks at one frame; evaluateLTLOnTrace looks at entire trace

2. **Should we reformulate the coinductive semantics?**
   - Maybe make it more explicit about state?
   - Or make incremental more explicit about traces?

3. **Is there existing work on relating stateful and stateless semantics?**
   - Back to Chapman et al. - do they address this?
   - Interaction Trees - how do they relate stateful/stateless?

4. **Can we prove just False and True cases without postulates?**
   - This would reduce from 9 postulates to ~3 (just for Continue cases)
   - Still progress!

### Immediate Action Items

1. **Try to prove `always-bind-false` and `always-bind-true`**
   - See if extended lambda equality blocks us
   - If yes, understand exactly where and why

2. **Analyze the Continue case more carefully**
   - What SHOULD `evaluateLTLOnTrace φ f (next ∷ rest')` be when stepEval continues?
   - Maybe look at specific examples (Always (Next p), Always (Always p), etc.)

3. **Check if existing literature addresses this**
   - Chapman et al. - does delay monad help with state correspondence?
   - Interaction Trees - do they have a similar problem?

### Hypothesis

**Maybe the Continue case IS genuinely harder and requires a postulate**, but if we can prove False and True cases without postulates, we've still made progress by reducing from 9 postulates to ~3.

That would be a win!
