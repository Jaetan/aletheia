# Coinductive Semantics Research Notes

**Date**: 2025-12-29
**Context**: After reverting incorrect "semantic bug fix" and removing 9 operator-specific postulates

## Summary

This document compiles research findings on how to properly prove bisimilarity between incremental (state machine) and coinductive LTL semantics. The challenge is relating explicit state parameters (incremental) to implicit state in delayed computations (coinductive).

---

## Current Status: Honest Assessment

### What We Have

**✅ Reverted to correct implementation**:
- Incremental.agda preserves states correctly (not resetting)
- AlwaysLemmas.agda signature matches implementation
- All modules type-check successfully

**✅ Reduced postulates to 5 generic ones**:
- `funExt` (functional extensionality)
- `bind-cong` (bind congruence for delay monad)
- `bind-now` (bind reduction for now case)
- `later-ext` (thunk extensionality - KEY workaround)
- `later-cong` (variant using propositional equality)

**❌ Deleted 9 operator-specific postulates**:
- AlwaysLemmas: 4 postulates (always-rhs-when-false, always-rhs-when-true, always-rhs-satisfied-continues, always-rhs-continue-continues)
- EventuallyLemmas: 2 postulates (eventually-rhs-when-true, eventually-rhs-when-false)
- UntilLemmas: 3 postulates (until-rhs-when-psi2-true, until-rhs-when-both-false, until-rhs-when-psi2-false-psi1-true)

**🔍 Current proof gaps (marked with holes)**:
- Properties.agda line 609: Always false case RHS extraction
- Properties.agda line 641: Always true case RHS extraction
- Properties.agda line 668: Always Continue case RHS extraction (state correspondence challenge)
- Properties.agda line 674: Helper for state correspondence

---

## The Core Problem

### Two Representations of State

**Incremental (explicit state)**:
```agda
stepEval (Always φ) eval (AlwaysState st) prev curr
  with stepEval φ eval st prev curr
... | Continue st' = Continue (AlwaysState st')  -- State st' is explicit
```

**Coinductive (implicit state in closure)**:
```agda
evaluateLTLOnTrace (Always ψ) frame (next ∷ rest') =
  bind (evaluateLTLOnTrace ψ frame (next ∷ rest')) λ r →
    if r
      then (later λ where .force → evaluateLTLOnTrace (Always ψ) next (rest' .force))
      else now false
```

The coinductive version doesn't have an explicit `st` parameter, but state IS threaded through the computation via the continuation closure. The challenge is proving these are equivalent representations.

---

## Research Findings

### 1. Weak vs Strong Bisimilarity

**Source**: Chapman, Uustalu, Veltri (2015) - "Quotienting the Delay Monad by Weak Bisimilarity"
**Link**: [ICTAC 2015 Paper](https://cs.ioc.ee/~niccolo/ictac15.pdf) | [MSCS Final Version](https://niccoloveltri.github.io/mscs_final.pdf)
**Agda Formalization**: http://cs.ioc.ee/∼niccolo/delay/

#### Key Concepts:

- **Strong bisimilarity** (`~R`): Exact step-by-step correspondence
- **Weak bisimilarity** (`≈`): Allows internal/silent steps, quotients by them
- **Delay monad**: Constructive alternative for modeling partial computations

#### Relevance to Our Problem:

The delay monad formalization uses weak bisimilarity to quotient computations, which may be the right notion for relating incremental and coinductive semantics.

**Our case**:
- Incremental evaluation: explicit state transitions (visible steps)
- Coinductive evaluation: implicit state in closures (internal steps?)
- These might be weakly bisimilar even if not strongly bisimilar

**Key Challenge Identified**:
> "With inductive-like quotient types, one meets a difficulty when attempting to reproduce the monad structure on the quotiented datatype. Specifically, one cannot define the multiplication. The difficulty has to do with the interplay of the coinductive nature of the delay datatype, or more precisely the infinity involved, and quotient types."

This suggests proving the bisimilarity directly (not via quotients) is the right approach, which is what we're already doing.

#### GitHub Resources:

- [nad/delay-monad](https://github.com/nad/delay-monad): Agda formalization by Nils Anders Danielsson
- Includes combined definitions of strong and weak bisimilarity and expansion

---

### 2. Coinductive Semantics for State Machines

**Sources Found**:

1. **"A coinductive semantics of the Unlimited Register Machine"**
   - Link: [arXiv:1111.3109](https://arxiv.org/abs/1111.3109)
   - Explores (co)inductive specifications for low-level programs in Coq
   - Formalizes both converging and diverging computations

2. **"Interaction Trees: Representing Recursive and Impure Programs in Coq"**
   - Link: [arXiv:1906.00046](https://arxiv.org/pdf/1906.00046)
   - ITrees are coinductive variant of free monads
   - Built from "uninterpreted events and their continuations"
   - **KEY INSIGHT**: State is encoded in continuations, similar to our coinductive LTL

3. **"Coinductive Natural Semantics for Compiler Verification in Coq"**
   - Link: [MDPI Mathematics](https://www.mdpi.com/2227-7390/8/9/1573)
   - Uses coinductive natural semantics for total correctness
   - First to define non-terminating computations in abstract machines using coinduction

4. **"Alternating-Time Temporal Logic in the Calculus of (Co)Inductive Constructions"**
   - Link: [Springer](https://link.springer.com/chapter/10.1007/978-3-642-33296-8_16) | [PDF](https://fceia.unr.edu.ar/~dante/archivos/sbmf12.pdf)
   - Formalizes ATL and Concurrent Game Structures in Coq
   - Temporal operators using inductive/coinductive types with fixpoint characterization
   - Models concurrent systems with unbounded numbers of players and **states**

---

### 3. State Representation Techniques

From the research, several approaches for handling state in coinductive proofs emerged:

#### Approach 1: Continuation-Based State (Interaction Trees)

ITrees represent stateful computations as:
```coq
Inductive itree : Type → Type :=
  | Ret (r : R) : itree R
  | Tau (t : itree R) : itree R  (* Internal step *)
  | Vis (e : E) (k : response e → itree R) : itree R  (* Event + continuation *)
```

**Relevance**: The continuation `k` captures state implicitly, similar to our coinductive LTL.

**Key Insight**: Proving equivalence requires showing:
1. State transitions in incremental ≡ continuation applications in coinductive
2. Observable behavior is the same (weak bisimilarity)

#### Approach 2: Fixpoint Characterization (ATL in Coq)

Temporal operators characterized as fixpoints:
- Inductive for finite behavior
- Coinductive for infinite behavior

**Relevance**: Our LTL operators could be characterized similarly, with explicit fixpoint equations relating incremental and coinductive versions.

#### Approach 3: Logical Relations

Not explicitly mentioned in the papers, but a potential technique:
- Define a logical relation between incremental states and coinductive closures
- Prove that the relation is preserved by evaluation steps

---

## Potential Proof Strategies

### Strategy 1: Direct State Correspondence Lemma

Define an explicit relation between incremental states and coinductive evaluations:

```agda
StateCorrespondence : LTLEvalState → (Colist TimedFrame ∞ → Delay Bool ∞) → Set
StateCorrespondence st k = ∀ (trace : Colist TimedFrame ∞)
  → foldStepEval-go φ st prev curr trace ≈ k trace
```

**Pros**: Makes state relationship explicit
**Cons**: May be difficult to define correctly, especially for complex operators like Until

### Strategy 2: Weak Bisimilarity Proof

Use weak bisimilarity (`≈`) from Chapman et al. to abstract over internal steps:

```agda
-- Incremental may take explicit state transition steps
-- Coinductive may have internal continuation applications
-- But both should be weakly bisimilar
∞ ⊢ foldStepEval φ trace ≈_weak checkColist φ trace
```

**Pros**: More flexible than strong bisimilarity
**Cons**: Need to identify what counts as "internal" vs "observable" steps

### Strategy 3: Simulation Relation

Prove a simulation between incremental and coinductive:
- Incremental step with state st → st' simulates coinductive bind application
- Use coinduction principle to complete the proof

**Pros**: Well-established technique for state machines
**Cons**: May still require relating states to closures explicitly

### Strategy 4: Quotient by State Equivalence

Define when two states are "equivalent" (produce same future behavior):

```agda
st₁ ≈ₛₜ st₂  iff  ∀ trace → eval with st₁ ≈ eval with st₂
```

Then prove incremental with any equivalent state ≈ coinductive.

**Pros**: Abstracts over internal state representation
**Cons**: Circular definition risk; may need well-founded induction

---

## Next Steps (Prioritized)

### Phase 1: Understand State Encoding (Research)

1. **Read Chapman et al. (2015) in detail**
   - Focus on Section 3: "Weak Bisimilarity and the Delay Monad"
   - Understand how they handle continuation equivalence
   - Check if they address state representation

2. **Study Interaction Trees paper**
   - Section on continuations and state
   - How they prove equivalence between ITree programs

3. **Look for existing LTL coinductive proofs**
   - Search Coq stdlib or verified libraries
   - Check if anyone has proven incremental ≈ coinductive for LTL

### Phase 2: Formalize State Correspondence (Proof Attempt)

1. **Define StateCorrespondence relation**
   - Start with simple Always operator
   - Explicitly relate `AlwaysState st` to the continuation closure

2. **Prove correspondence is preserved by evaluation**
   - Show that stepEval with st corresponds to bind application

3. **Use correspondence to fill holes**
   - Apply to Properties.agda line 668 (Continue case)

### Phase 3: Generalize to Other Operators

1. **Apply technique to Eventually**
   - Similar structure to Always but different polarity

2. **Apply to Until**
   - More complex: two states (st1, st2) vs nested bind

3. **Apply to bounded operators**
   - EventuallyWithin, AlwaysWithin

### Phase 4: Alternative If Correspondence Fails

If state correspondence approach doesn't work:

1. **Try weak bisimilarity**
   - Identify internal vs observable steps
   - Use Chapman et al.'s weak bisimilarity definition

2. **Consider Interaction Trees approach**
   - Rewrite coinductive semantics in ITree style?
   - Use existing ITree equivalence proofs

3. **Postulate minimal axioms**
   - If some postulates are truly necessary, identify the minimal set
   - Document why they're needed (fundamental limitation vs proof technique gap)

---

## Open Questions

1. **What exactly is the state in coinductive Always?**
   - Is it the continuation `λ r → if r then later ... else now false`?
   - Or is it the delayed computation `evaluateLTLOnTrace φ ...`?

2. **Are internal state transitions observable?**
   - Does incremental's explicit `Continue st'` count as an observable step?
   - Or should it be considered internal (weak bisimilarity)?

3. **Can we use existing Agda libraries?**
   - Is there a delay monad library we can import?
   - Chapman et al. have a formalization - can we reuse parts?

4. **Is our bisimilarity notion correct?**
   - We're using strong bisimilarity (`_⊢_≈_` from stdlib)
   - Should we switch to weak bisimilarity?

---

## References

### Primary Sources

1. **Chapman, Uustalu, Veltri (2015)**
   *Quotienting the Delay Monad by Weak Bisimilarity*
   [ICTAC 2015](https://cs.ioc.ee/~niccolo/ictac15.pdf) | [MSCS Final](https://niccoloveltri.github.io/mscs_final.pdf)
   Agda code: http://cs.ioc.ee/∼niccolo/delay/

2. **Xia et al. (2019)**
   *Interaction Trees: Representing Recursive and Impure Programs in Coq*
   [arXiv:1906.00046](https://arxiv.org/pdf/1906.00046)

3. **Bonfante et al. (2011)**
   *A coinductive semantics of the Unlimited Register Machine*
   [arXiv:1111.3109](https://arxiv.org/abs/1111.3109)

4. **Ciaffaglione et al. (2020)**
   *Coinductive Natural Semantics for Compiler Verification in Coq*
   [MDPI Mathematics](https://www.mdpi.com/2227-7390/8/9/1573)

5. **Ziliani, Fridlender (2012)**
   *Alternating-Time Temporal Logic in the Calculus of (Co)Inductive Constructions*
   [Springer](https://link.springer.com/chapter/10.1007/978-3-642-33296-8_16) | [PDF](https://fceia.unr.edu.ar/~dante/archivos/sbmf12.pdf)

### Agda/Coq Resources

6. **Nils Anders Danielsson**
   *delay-monad library*
   [GitHub](https://github.com/nad/delay-monad)

7. **Coq Documentation**
   *Coinductive Types*
   [GitHub](https://github.com/coq/coq/blob/master/doc/sphinx/language/core/coinductive.rst)

8. **Agda Documentation**
   *Coinduction*
   [v2.6.2.2](https://agda.readthedocs.io/en/v2.6.2.2/language/coinduction.html)

### Related Work

9. **Veltri (2015)**
   *Guarded Recursion in Agda via Sized Types*
   [PDF](https://cs.ru.nl/~nweide/AgdaSizedTypes.pdf)

10. **Uustalu, Veltri (2017)**
    *The Delay Monad and Restriction Categories*
    [PDF](https://niccoloveltri.github.io/ictac17-revised.pdf)

---

## Conclusion

The incorrect "semantic bug fix" has been reverted, and we now have an honest assessment of the proof state:
- ✅ 5 generic delay monad postulates (reasonable, aligned with research)
- ❌ 9 operator-specific postulates deleted (were masking proof gaps)
- 🔍 3 main holes in Properties.agda showing where RHS extraction is needed

The research shows this is a **well-studied problem** with established techniques:
1. Chapman et al.'s weak bisimilarity for delay monad
2. Interaction Trees' continuation-based state representation
3. ATL in Coq's fixpoint characterization

**Recommended next step**: Study Chapman et al. (2015) in detail and attempt Strategy 1 (Direct State Correspondence) for the Always operator as a proof of concept.
