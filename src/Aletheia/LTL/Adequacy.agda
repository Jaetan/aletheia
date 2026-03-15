{-# OPTIONS --safe --without-K #-}

-- Adequacy of stepL (formula progression) w.r.t. denotational LTLf semantics.
--
-- Purpose: Prove that the coalgebra (stepL + finalizeL) correctly implements
-- the reference denotational semantics ⟦_⟧ from LTL.Semantics.
--
-- Proof architecture (Gap D):
--   stepL ←adequacy→ denotational LTLf
--   Direct adequacy proof (no bisimilarity intermediate layer).
--
-- Theorems:
--   finalize-denot : verdictToSV (finalizeL (initProc φ)) ≡ ⟦ mapLTL table φ ⟧ []
--   Unfolding laws : structural decomposition of ⟦_⟧ (all refl)
--
-- All proofs hold for arbitrary SignalVal atoms (four-valued Kleene logic),
-- not just two-valued predicates. The denotational semantics ⟦_⟧ naturally
-- propagates Unknown/Pending through Kleene connectives (∧TV, ∨TV, notTV).
--
-- Key insight: stepL is essentially Havelund-Rosu formula progression.
-- The one-step unfolding ⟦ φ ⟧ (x ∷ rest) = f(⟦ φ ⟧ x, ⟦ ... ⟧ rest) matches
-- exactly what stepL computes (for the Continue case).
module Aletheia.LTL.Adequacy where

open import Aletheia.Prelude
open import Data.Nat using (_≤ᵇ_; _≡ᵇ_; _∸_)
open import Relation.Binary.PropositionalEquality using (subst)

open import Aletheia.LTL.Syntax as Syntax
open import Aletheia.LTL.SignalPredicate using (SignalVal; True; False; Unknown; Pending;
  notTV; _∧TV_; _∨TV_)
open import Aletheia.LTL.Coalgebra using (LTLProc; PredTable; stepL; finalizeL; initProc; denot)
open import Aletheia.LTL.Coalgebra as Coal
  using (Atomic; Not; And; Or; Next; Always; Eventually; Until; Release;
         MetricEventuallyProc; MetricAlwaysProc; MetricUntilProc; MetricReleaseProc)
open import Aletheia.LTL.Incremental using (StepResult; Continue; Violated; Satisfied;
  FinalVerdict; Holds; Fails)
open import Aletheia.LTL.Semantics using (⟦_⟧; met-ev-go; met-al-go; met-un-go; met-re-go)
open import Aletheia.Trace.CANTrace using (TimedFrame; timestamp)

-- ============================================================================
-- FINAL VERDICT → SIGNAL VALUE CONVERSION
-- ============================================================================

verdictToSV : FinalVerdict → SignalVal
verdictToSV Holds = True
verdictToSV (Fails _) = False

-- ============================================================================
-- COALGEBRA EXECUTION ON FULL TRACE
-- ============================================================================

-- Run the coalgebra on a full trace, producing a SignalVal.
-- Takes a PredTable for evaluating atomic predicates.
-- No prev parameter — delta predicates use SignalCache externally.
--
-- When stepL returns:
--   Satisfied       → True  (property definitely holds)
--   Violated _      → False (property definitely fails)
--   Continue _ proc' → recurse on remaining trace
--   (no Inconclusive — removed, Unknown/Pending signals produce Continue 0)

runL : PredTable → LTLProc → List TimedFrame → SignalVal
runL table proc [] = verdictToSV (finalizeL proc)
runL table proc (x ∷ rest) with stepL table proc x
... | Satisfied        = True
... | Violated _       = False
... | Continue _ proc' = runL table proc' rest

-- ============================================================================
-- ONE-STEP UNFOLDING LEMMAS (all definitional / refl)
-- ============================================================================

-- These show that ⟦_⟧ decomposes exactly according to the recursive structure
-- of each operator. They hold for ALL SignalVal atoms (no two-valued restriction).

-- Temporal operators: non-empty trace
always-unfold : ∀ (φ : LTL (TimedFrame → SignalVal)) (x : TimedFrame) (rest : List TimedFrame)
  → ⟦ Syntax.Always φ ⟧ (x ∷ rest) ≡ ⟦ φ ⟧ (x ∷ rest) ∧TV ⟦ Syntax.Always φ ⟧ rest
always-unfold φ x rest = refl

eventually-unfold : ∀ (φ : LTL (TimedFrame → SignalVal)) (x : TimedFrame) (rest : List TimedFrame)
  → ⟦ Syntax.Eventually φ ⟧ (x ∷ rest) ≡ ⟦ φ ⟧ (x ∷ rest) ∨TV ⟦ Syntax.Eventually φ ⟧ rest
eventually-unfold φ x rest = refl

until-unfold : ∀ (φ ψ : LTL (TimedFrame → SignalVal)) (x : TimedFrame) (rest : List TimedFrame)
  → ⟦ Syntax.Until φ ψ ⟧ (x ∷ rest) ≡ ⟦ ψ ⟧ (x ∷ rest) ∨TV (⟦ φ ⟧ (x ∷ rest) ∧TV ⟦ Syntax.Until φ ψ ⟧ rest)
until-unfold φ ψ x rest = refl

release-unfold : ∀ (φ ψ : LTL (TimedFrame → SignalVal)) (x : TimedFrame) (rest : List TimedFrame)
  → ⟦ Syntax.Release φ ψ ⟧ (x ∷ rest) ≡ ⟦ ψ ⟧ (x ∷ rest) ∧TV (⟦ φ ⟧ (x ∷ rest) ∨TV ⟦ Syntax.Release φ ψ ⟧ rest)
release-unfold φ ψ x rest = refl

next-unfold : ∀ (φ : LTL (TimedFrame → SignalVal)) (x : TimedFrame) (rest : List TimedFrame)
  → ⟦ Syntax.Next φ ⟧ (x ∷ rest) ≡ ⟦ φ ⟧ rest
next-unfold φ x rest = refl

-- Temporal operators: empty trace base cases
always-empty : ∀ (φ : LTL (TimedFrame → SignalVal))
  → ⟦ Syntax.Always φ ⟧ [] ≡ True
always-empty φ = refl

eventually-empty : ∀ (φ : LTL (TimedFrame → SignalVal))
  → ⟦ Syntax.Eventually φ ⟧ [] ≡ False
eventually-empty φ = refl

until-empty : ∀ (φ ψ : LTL (TimedFrame → SignalVal))
  → ⟦ Syntax.Until φ ψ ⟧ [] ≡ False
until-empty φ ψ = refl

release-empty : ∀ (φ ψ : LTL (TimedFrame → SignalVal))
  → ⟦ Syntax.Release φ ψ ⟧ [] ≡ True
release-empty φ ψ = refl

next-empty : ∀ (φ : LTL (TimedFrame → SignalVal))
  → ⟦ Syntax.Next φ ⟧ [] ≡ False
next-empty φ = refl

-- Metric operators: empty trace base cases
metric-always-empty : ∀ (w s : ℕ) (φ : LTL (TimedFrame → SignalVal))
  → ⟦ Syntax.MetricAlways w s φ ⟧ [] ≡ True
metric-always-empty w s φ = refl

metric-eventually-empty : ∀ (w s : ℕ) (φ : LTL (TimedFrame → SignalVal))
  → ⟦ Syntax.MetricEventually w s φ ⟧ [] ≡ False
metric-eventually-empty w s φ = refl

metric-until-empty : ∀ (w s : ℕ) (φ ψ : LTL (TimedFrame → SignalVal))
  → ⟦ Syntax.MetricUntil w s φ ψ ⟧ [] ≡ False
metric-until-empty w s φ ψ = refl

metric-release-empty : ∀ (w s : ℕ) (φ ψ : LTL (TimedFrame → SignalVal))
  → ⟦ Syntax.MetricRelease w s φ ψ ⟧ [] ≡ True
metric-release-empty w s φ ψ = refl

-- ============================================================================
-- FINALIZE-DENOT: finalizeL agrees with empty-trace denotational semantics
-- ============================================================================

-- For an initial process (no accumulated runtime state), finalization agrees
-- with the denotational semantics on the empty trace.
-- Since LTLProc is now ℕ-indexed, we use mapLTL table to convert back.

-- Helper: ⟦ φ ⟧ [] is always True or False (never Unknown/Pending) for any formula.
-- This is because atoms evaluate to False on empty trace, and the only connectives
-- are notTV, ∧TV, ∨TV which preserve the {True, False} subset.
denot-empty-binary : ∀ (φ : LTL (TimedFrame → SignalVal))
  → (⟦ φ ⟧ [] ≡ True) ⊎ (⟦ φ ⟧ [] ≡ False)
denot-empty-binary (Syntax.Atomic _) = inj₂ refl
denot-empty-binary (Syntax.Not φ) with ⟦ φ ⟧ [] | denot-empty-binary φ
... | .True  | inj₁ refl = inj₂ refl
... | .False | inj₂ refl = inj₁ refl
denot-empty-binary (Syntax.And φ ψ) with ⟦ φ ⟧ [] | denot-empty-binary φ
... | .False | inj₂ refl = inj₂ refl
... | .True  | inj₁ refl with ⟦ ψ ⟧ [] | denot-empty-binary ψ
...   | .True  | inj₁ refl = inj₁ refl
...   | .False | inj₂ refl = inj₂ refl
denot-empty-binary (Syntax.Or φ ψ) with ⟦ φ ⟧ [] | denot-empty-binary φ
... | .True  | inj₁ refl = inj₁ refl
... | .False | inj₂ refl with ⟦ ψ ⟧ [] | denot-empty-binary ψ
...   | .True  | inj₁ refl = inj₁ refl
...   | .False | inj₂ refl = inj₂ refl
denot-empty-binary (Syntax.Next _) = inj₂ refl
denot-empty-binary (Syntax.Always _) = inj₁ refl
denot-empty-binary (Syntax.Eventually _) = inj₂ refl
denot-empty-binary (Syntax.Until _ _) = inj₂ refl
denot-empty-binary (Syntax.Release _ _) = inj₁ refl
denot-empty-binary (Syntax.MetricEventually _ _ _) = inj₂ refl
denot-empty-binary (Syntax.MetricAlways _ _ _) = inj₁ refl
denot-empty-binary (Syntax.MetricUntil _ _ _ _) = inj₂ refl
denot-empty-binary (Syntax.MetricRelease _ _ _ _) = inj₁ refl

-- Helper: transport via equality — when we know verdictToSV v ≡ ⟦ φ ⟧ [],
-- we can compute notTV, ∧TV, ∨TV on the denotational side by rewriting.
private
  not-cong : ∀ {a b : SignalVal} → a ≡ b → notTV a ≡ notTV b
  not-cong refl = refl

  and-cong : ∀ {a b c d : SignalVal} → a ≡ c → b ≡ d → (a ∧TV b) ≡ (c ∧TV d)
  and-cong refl refl = refl

  or-cong : ∀ {a b c d : SignalVal} → a ≡ c → b ≡ d → (a ∨TV b) ≡ (c ∨TV d)
  or-cong refl refl = refl

-- finalize-denot now works with ℕ-indexed formulas.
-- Since finalizeL doesn't inspect Atomic content and ⟦ Atomic _ ⟧ [] = False
-- regardless of predicate, the proof is independent of the table.
finalize-denot : ∀ (table : PredTable) (φ : LTL ℕ)
  → verdictToSV (finalizeL (initProc φ)) ≡ ⟦ denot table (initProc φ) ⟧ []
finalize-denot table (Syntax.Atomic n) = refl
finalize-denot table (Syntax.Not φ) with finalizeL (initProc φ) | finalize-denot table φ
... | Holds   | eq rewrite sym eq = refl
... | Fails _ | eq rewrite sym eq = refl
finalize-denot table (Syntax.And φ ψ) with finalizeL (initProc φ) | finalize-denot table φ
... | Fails _ | eq rewrite sym eq = refl
... | Holds   | eq with finalizeL (initProc ψ) | finalize-denot table ψ
...   | Fails _ | eq2 rewrite sym eq | sym eq2 = refl
...   | Holds   | eq2 rewrite sym eq | sym eq2 = refl
finalize-denot table (Syntax.Or φ ψ) with finalizeL (initProc φ) | finalize-denot table φ
... | Holds | eq rewrite sym eq = refl
... | Fails _ | eq with finalizeL (initProc ψ) | finalize-denot table ψ
...   | Holds   | eq2 rewrite sym eq | sym eq2 = refl
...   | Fails _ | eq2 rewrite sym eq | sym eq2 = refl
finalize-denot table (Syntax.Next φ) = refl
finalize-denot table (Syntax.Always φ) = refl
finalize-denot table (Syntax.Eventually φ) = refl
finalize-denot table (Syntax.Until φ ψ) = refl
finalize-denot table (Syntax.Release φ ψ) = refl
finalize-denot table (Syntax.MetricEventually _ _ φ) = refl
finalize-denot table (Syntax.MetricAlways _ _ φ) = refl
finalize-denot table (Syntax.MetricUntil _ _ φ ψ) = refl
finalize-denot table (Syntax.MetricRelease _ _ φ ψ) = refl

-- ============================================================================
-- ADEQUACY: runL table (initProc φ) σ ≡ ⟦ denot table (initProc φ) ⟧ σ
-- ============================================================================

-- The empty-trace case follows directly from finalize-denot.
adequacy-empty : ∀ (table : PredTable) (φ : LTL ℕ)
  → runL table (initProc φ) [] ≡ ⟦ denot table (initProc φ) ⟧ []
adequacy-empty table φ = finalize-denot table φ

-- ============================================================================
-- DENOT-INITPROC: denot table ∘ initProc ≡ mapLTL table
-- ============================================================================

-- The denotational interpretation of an initial process is the formula
-- with table-resolved predicates. This is trivial structural induction.

private
  -- cong for binary constructors (not in stdlib)
  cong-bin : ∀ {A B C : Set} {a₁ a₂ : A} {b₁ b₂ : B}
    → (f : A → B → C) → a₁ ≡ a₂ → b₁ ≡ b₂ → f a₁ b₁ ≡ f a₂ b₂
  cong-bin f refl refl = refl

denot-initProc : ∀ (table : PredTable) (φ : LTL ℕ) → denot table (initProc φ) ≡ mapLTL table φ
denot-initProc table (Syntax.Atomic n)            = refl
denot-initProc table (Syntax.Not φ)               = cong Syntax.Not (denot-initProc table φ)
denot-initProc table (Syntax.And φ ψ)             = cong-bin Syntax.And (denot-initProc table φ) (denot-initProc table ψ)
denot-initProc table (Syntax.Or φ ψ)              = cong-bin Syntax.Or (denot-initProc table φ) (denot-initProc table ψ)
denot-initProc table (Syntax.Next φ)              = cong Syntax.Next (denot-initProc table φ)
denot-initProc table (Syntax.Always φ)            = cong Syntax.Always (denot-initProc table φ)
denot-initProc table (Syntax.Eventually φ)        = cong Syntax.Eventually (denot-initProc table φ)
denot-initProc table (Syntax.Until φ ψ)           = cong-bin Syntax.Until (denot-initProc table φ) (denot-initProc table ψ)
denot-initProc table (Syntax.Release φ ψ)         = cong-bin Syntax.Release (denot-initProc table φ) (denot-initProc table ψ)
denot-initProc table (Syntax.MetricEventually w s φ)    = cong (Syntax.MetricEventually w s) (denot-initProc table φ)
denot-initProc table (Syntax.MetricAlways w s φ)        = cong (Syntax.MetricAlways w s) (denot-initProc table φ)
denot-initProc table (Syntax.MetricUntil w s φ ψ)      = cong-bin (Syntax.MetricUntil w s) (denot-initProc table φ) (denot-initProc table ψ)
denot-initProc table (Syntax.MetricRelease w s φ ψ)    = cong-bin (Syntax.MetricRelease w s) (denot-initProc table φ) (denot-initProc table ψ)

-- ============================================================================
-- INFORMATION ORDERING (_⊑_)
-- ============================================================================

-- x ⊑ y means "x is at least as informative as y."
-- Definite values (True, False) refine uncertain values (Unknown, Pending).
-- This is a preorder (reflexive + transitive).

data _⊑_ : SignalVal → SignalVal → Set where
  ⊑-refl    : ∀ {x}   → x ⊑ x
  ⊑-unknown : ∀ {x}   → x ⊑ Unknown
  ⊑-pending : ∀ {x}   → x ⊑ Pending

-- Equality implies ⊑
≡→⊑ : ∀ {a b} → a ≡ b → a ⊑ b
≡→⊑ refl = ⊑-refl

-- Transitivity of ⊑
⊑-trans : ∀ {a b c} → a ⊑ b → b ⊑ c → a ⊑ c
⊑-trans p ⊑-refl    = p
⊑-trans _ ⊑-unknown = ⊑-unknown
⊑-trans _ ⊑-pending = ⊑-pending

-- ============================================================================
-- MONITORING SOUNDNESS (Sound)
-- ============================================================================

-- Sound m d means "m is a sound monitoring result for denotation d."
--
-- Definite agreement:    Sound True True, Sound False False
-- Denotation uncertain:  Sound m Unknown, Sound m Pending  (any monitor result OK)
-- Monitor uncertain:     Sound Unknown d, Sound Pending d  (admits ignorance)
--
-- Key exclusions: NOT Sound True False, NOT Sound False True
-- (the monitor NEVER gives a wrong definite answer)

data Sound : SignalVal → SignalVal → Set where
  sound-tt    : Sound True True
  sound-ff    : Sound False False
  sound-unk   : ∀ {m} → Sound m Unknown
  sound-pen   : ∀ {m} → Sound m Pending
  sound-m-unk : ∀ {d} → Sound Unknown d
  sound-m-pen : ∀ {d} → Sound Pending d

-- Compose Sound (from IH) with ⊑ (from absorption lemmas).
-- When the target weakens (becomes less informative), soundness is preserved.
sound-weaken : ∀ {m y z} → Sound m y → y ⊑ z → Sound m z
sound-weaken s ⊑-refl    = s
sound-weaken _ ⊑-unknown = sound-unk
sound-weaken _ ⊑-pending = sound-pen

-- ============================================================================
-- MONOTONICITY LEMMAS
-- ============================================================================

-- The monotonicity lemmas are the compositional backbone.
-- They let operator proofs compose refinements structurally.
--
-- Strategy: case split on BOTH SignalVal arguments explicitly,
-- since ⊑ doesn't constrain the LHS enough for the connective
-- to reduce. This is 4×4 = 16 cases per connective, but most are trivial.

-- notTV is monotone
notTV-mono : ∀ {a b} → a ⊑ b → notTV a ⊑ notTV b
notTV-mono {True}    {.True}    ⊑-refl = ⊑-refl        -- False ⊑ False
notTV-mono {False}   {.False}   ⊑-refl = ⊑-refl        -- True ⊑ True
notTV-mono {Unknown} {.Unknown} ⊑-refl = ⊑-refl        -- Unknown ⊑ Unknown
notTV-mono {Pending} {.Pending} ⊑-refl = ⊑-refl        -- Pending ⊑ Pending
notTV-mono {_}       {.Unknown} ⊑-unknown = ⊑-unknown   -- notTV a ⊑ Unknown
notTV-mono {_}       {.Pending} ⊑-pending = ⊑-pending   -- notTV a ⊑ Pending

-- Helper: for any value a, (a ∧TV b) ⊑ Unknown and (a ∧TV b) ⊑ Pending
-- These hold because anything refines Unknown/Pending.
private
  ∧TV-⊑-unknown : ∀ a b → (a ∧TV b) ⊑ Unknown
  ∧TV-⊑-unknown _ _ = ⊑-unknown

  ∧TV-⊑-pending : ∀ a b → (a ∧TV b) ⊑ Pending
  ∧TV-⊑-pending _ _ = ⊑-pending

  ∨TV-⊑-unknown : ∀ a b → (a ∨TV b) ⊑ Unknown
  ∨TV-⊑-unknown _ _ = ⊑-unknown

  ∨TV-⊑-pending : ∀ a b → (a ∨TV b) ⊑ Pending
  ∨TV-⊑-pending _ _ = ⊑-pending

-- ∧TV is monotone in both arguments.
-- When abstract `a` appears in (a ∧TV False), Agda can't reduce it
-- (first clause checks a = False, second checks second arg = False).
-- We need to case split on `a` in these positions.
--
-- Strategy: helper that case-splits on all 4 values to let Agda reduce.

private
  -- Any a: a ∧TV False = False
  ∧TV-false-r : ∀ a → (a ∧TV False) ≡ False
  ∧TV-false-r True    = refl
  ∧TV-false-r False   = refl
  ∧TV-false-r Unknown = refl
  ∧TV-false-r Pending = refl

  -- Any a: a ∨TV True = True
  ∨TV-true-r : ∀ a → (a ∨TV True) ≡ True
  ∨TV-true-r True    = refl
  ∨TV-true-r False   = refl
  ∨TV-true-r Unknown = refl
  ∨TV-true-r Pending = refl

  ∨TV-false-r : ∀ a → (a ∨TV False) ≡ a
  ∨TV-false-r True    = refl
  ∨TV-false-r False   = refl
  ∨TV-false-r Unknown = refl
  ∨TV-false-r Pending = refl

  -- True ∧TV b = b (left identity)
  ∧TV-true-l : ∀ b → (True ∧TV b) ≡ b
  ∧TV-true-l True    = refl
  ∧TV-true-l False   = refl
  ∧TV-true-l Unknown = refl
  ∧TV-true-l Pending = refl

  -- Any a: a ∧TV True = a (right identity for ∧)
  ∧TV-true-r : ∀ a → (a ∧TV True) ≡ a
  ∧TV-true-r True    = refl
  ∧TV-true-r False   = refl
  ∧TV-true-r Unknown = refl
  ∧TV-true-r Pending = refl

  -- False ∨TV b = b (left identity for ∨)
  ∨TV-false-l : ∀ b → (False ∨TV b) ≡ b
  ∨TV-false-l True    = refl
  ∨TV-false-l False   = refl
  ∨TV-false-l Unknown = refl
  ∨TV-false-l Pending = refl

-- Absorption lemmas: when the LHS of ⊑ is a plain value (not a connective),
-- we need direct proofs about the target connective's range.

-- False ⊑ (Unknown ∧TV y) for any y
-- Unknown ∧TV y ∈ {Unknown, False, Pending} — all ⊒ False
⊑-false-unknown-and : ∀ y → False ⊑ (Unknown ∧TV y)
⊑-false-unknown-and True    = ⊑-unknown   -- False ⊑ Unknown
⊑-false-unknown-and False   = ⊑-refl      -- False ⊑ False
⊑-false-unknown-and Unknown = ⊑-unknown   -- False ⊑ Unknown
⊑-false-unknown-and Pending = ⊑-pending   -- False ⊑ Pending

-- y ⊑ (Pending ∧TV y) for any y
⊑-pending-and-absorb : ∀ y → y ⊑ (Pending ∧TV y)
⊑-pending-and-absorb True    = ⊑-pending   -- True ⊑ Pending
⊑-pending-and-absorb False   = ⊑-refl      -- False ⊑ False
⊑-pending-and-absorb Unknown = ⊑-pending   -- Unknown ⊑ Pending
⊑-pending-and-absorb Pending = ⊑-refl      -- Pending ⊑ Pending

-- y ⊑ (Unknown ∧TV y) for any y (similar)
⊑-unknown-and-absorb : ∀ y → y ⊑ (Unknown ∧TV y)
⊑-unknown-and-absorb True    = ⊑-unknown   -- True ⊑ Unknown
⊑-unknown-and-absorb False   = ⊑-refl      -- False ⊑ False
⊑-unknown-and-absorb Unknown = ⊑-refl      -- Unknown ⊑ Unknown
⊑-unknown-and-absorb Pending = ⊑-pending   -- Pending ⊑ Pending

∧TV-mono : ∀ {a b c d} → a ⊑ c → b ⊑ d → (a ∧TV b) ⊑ (c ∧TV d)
-- Both refl
∧TV-mono ⊑-refl ⊑-refl = ⊑-refl
-- Right target Unknown, case split on c (since c ∧TV Unknown depends on c)
∧TV-mono {a} {b} {True}    ⊑-refl    ⊑-unknown = ⊑-unknown
∧TV-mono {a} {b} {False}   ⊑-refl    ⊑-unknown rewrite ∧TV-false-r a = ⊑-refl
∧TV-mono {a} {b} {Unknown} ⊑-refl    ⊑-unknown = ⊑-unknown
∧TV-mono {a} {b} {Pending} ⊑-refl    ⊑-unknown = ⊑-pending
∧TV-mono {a} {b}           ⊑-unknown ⊑-unknown = ⊑-unknown
∧TV-mono {a} {b}           ⊑-pending ⊑-unknown = ⊑-pending
-- Right target Pending
∧TV-mono {a} {b} {True}    ⊑-refl    ⊑-pending = ⊑-pending
∧TV-mono {a} {b} {False}   ⊑-refl    ⊑-pending rewrite ∧TV-false-r a = ⊑-refl
∧TV-mono {a} {b} {Unknown} ⊑-refl    ⊑-pending = ⊑-pending
∧TV-mono {a} {b} {Pending} ⊑-refl    ⊑-pending = ⊑-pending
∧TV-mono {a} {b}           ⊑-unknown ⊑-pending = ⊑-pending
∧TV-mono {a} {b}           ⊑-pending ⊑-pending = ⊑-pending
-- Left Unknown, right refl: b=d, case split on b
∧TV-mono {a} {True}        ⊑-unknown ⊑-refl = ⊑-unknown
∧TV-mono {a} {False}       ⊑-unknown ⊑-refl rewrite ∧TV-false-r a = ⊑-refl
∧TV-mono {a} {Unknown}     ⊑-unknown ⊑-refl = ⊑-unknown
∧TV-mono {a} {Pending}     ⊑-unknown ⊑-refl = ⊑-pending
-- Left Pending, right refl
∧TV-mono {a} {True}        ⊑-pending ⊑-refl = ⊑-pending
∧TV-mono {a} {False}       ⊑-pending ⊑-refl rewrite ∧TV-false-r a = ⊑-refl
∧TV-mono {a} {Unknown}     ⊑-pending ⊑-refl = ⊑-pending
∧TV-mono {a} {Pending}     ⊑-pending ⊑-refl = ⊑-pending

-- ∨TV is monotone (dual of ∧TV, True absorbs)
∨TV-mono : ∀ {a b c d} → a ⊑ c → b ⊑ d → (a ∨TV b) ⊑ (c ∨TV d)
∨TV-mono ⊑-refl ⊑-refl = ⊑-refl
-- Right target Unknown
∨TV-mono {a} {b} {True}    ⊑-refl    ⊑-unknown rewrite ∨TV-true-r a = ⊑-refl
∨TV-mono {a} {b} {False}   ⊑-refl    ⊑-unknown = ⊑-unknown
∨TV-mono {a} {b} {Unknown} ⊑-refl    ⊑-unknown = ⊑-unknown
∨TV-mono {a} {b} {Pending} ⊑-refl    ⊑-unknown = ⊑-pending
∨TV-mono {a} {b}           ⊑-unknown ⊑-unknown = ⊑-unknown
∨TV-mono {a} {b}           ⊑-pending ⊑-unknown = ⊑-pending
-- Right target Pending
∨TV-mono {a} {b} {True}    ⊑-refl    ⊑-pending rewrite ∨TV-true-r a = ⊑-refl
∨TV-mono {a} {b} {False}   ⊑-refl    ⊑-pending = ⊑-pending
∨TV-mono {a} {b} {Unknown} ⊑-refl    ⊑-pending = ⊑-pending
∨TV-mono {a} {b} {Pending} ⊑-refl    ⊑-pending = ⊑-pending
∨TV-mono {a} {b}           ⊑-unknown ⊑-pending = ⊑-pending
∨TV-mono {a} {b}           ⊑-pending ⊑-pending = ⊑-pending
-- Left Unknown, right refl: b=d, case split on b
∨TV-mono {a} {True}        ⊑-unknown ⊑-refl rewrite ∨TV-true-r a = ⊑-refl
∨TV-mono {a} {False}       ⊑-unknown ⊑-refl = ⊑-unknown
∨TV-mono {a} {Unknown}     ⊑-unknown ⊑-refl = ⊑-unknown
∨TV-mono {a} {Pending}     ⊑-unknown ⊑-refl = ⊑-pending
-- Left Pending, right refl
∨TV-mono {a} {True}        ⊑-pending ⊑-refl rewrite ∨TV-true-r a = ⊑-refl
∨TV-mono {a} {False}       ⊑-pending ⊑-refl = ⊑-pending
∨TV-mono {a} {Unknown}     ⊑-pending ⊑-refl = ⊑-pending
∨TV-mono {a} {Pending}     ⊑-pending ⊑-refl = ⊑-pending

-- ============================================================================
-- SOUND COMPOSITIONALITY LEMMAS
-- ============================================================================

-- These let us compose Sound proofs through propositional connectives.

sound-not : ∀ {m d} → Sound m d → Sound (notTV m) (notTV d)
sound-not sound-tt    = sound-ff
sound-not sound-ff    = sound-tt
sound-not sound-unk   = sound-unk
sound-not sound-pen   = sound-pen
sound-not sound-m-unk = sound-m-unk
sound-not sound-m-pen = sound-m-pen

sound-and : ∀ {m₁ d₁ m₂ d₂} → Sound m₁ d₁ → Sound m₂ d₂ → Sound (m₁ ∧TV m₂) (d₁ ∧TV d₂)
sound-and sound-tt sound-tt = sound-tt
sound-and sound-tt sound-ff = sound-ff
sound-and sound-tt sound-unk = sound-unk
sound-and sound-tt sound-pen = sound-pen
sound-and sound-tt sound-m-unk = sound-m-unk
sound-and sound-tt sound-m-pen = sound-m-pen
sound-and sound-ff _ = sound-ff
sound-and sound-unk sound-tt = sound-unk
sound-and {m₁} sound-unk sound-ff rewrite ∧TV-false-r m₁ = sound-ff
sound-and sound-unk sound-unk = sound-unk
sound-and sound-unk sound-pen = sound-pen
sound-and {m₁} {_} {_} {d₂} sound-unk sound-m-unk = unk-and-unk m₁ d₂
  where
    unk-and-unk : ∀ a b → Sound (a ∧TV Unknown) (Unknown ∧TV b)
    unk-and-unk True    True    = sound-unk
    unk-and-unk True    False   = sound-m-unk
    unk-and-unk True    Unknown = sound-unk
    unk-and-unk True    Pending = sound-pen
    unk-and-unk False   True    = sound-unk
    unk-and-unk False   False   = sound-ff
    unk-and-unk False   Unknown = sound-unk
    unk-and-unk False   Pending = sound-pen
    unk-and-unk Unknown True    = sound-unk
    unk-and-unk Unknown False   = sound-m-unk
    unk-and-unk Unknown Unknown = sound-unk
    unk-and-unk Unknown Pending = sound-pen
    unk-and-unk Pending True    = sound-unk
    unk-and-unk Pending False   = sound-m-pen
    unk-and-unk Pending Unknown = sound-unk
    unk-and-unk Pending Pending = sound-pen
sound-and {m₁} {_} {_} {d₂} sound-unk sound-m-pen = unk-and-pen m₁ d₂
  where
    unk-and-pen : ∀ a b → Sound (a ∧TV Pending) (Unknown ∧TV b)
    unk-and-pen True    True    = sound-unk
    unk-and-pen True    False   = sound-m-pen
    unk-and-pen True    Unknown = sound-unk
    unk-and-pen True    Pending = sound-pen
    unk-and-pen False   True    = sound-unk
    unk-and-pen False   False   = sound-ff
    unk-and-pen False   Unknown = sound-unk
    unk-and-pen False   Pending = sound-pen
    unk-and-pen Unknown True    = sound-unk
    unk-and-pen Unknown False   = sound-m-pen
    unk-and-pen Unknown Unknown = sound-unk
    unk-and-pen Unknown Pending = sound-pen
    unk-and-pen Pending True    = sound-unk
    unk-and-pen Pending False   = sound-m-pen
    unk-and-pen Pending Unknown = sound-unk
    unk-and-pen Pending Pending = sound-pen
sound-and sound-pen sound-tt = sound-pen
sound-and {m₁} sound-pen sound-ff rewrite ∧TV-false-r m₁ = sound-ff
sound-and sound-pen sound-unk = sound-pen
sound-and sound-pen sound-pen = sound-pen
sound-and {m₁} {_} {_} {d₂} sound-pen sound-m-unk = pen-and-unk m₁ d₂
  where
    pen-and-unk : ∀ a b → Sound (a ∧TV Unknown) (Pending ∧TV b)
    pen-and-unk True    True    = sound-pen
    pen-and-unk True    False   = sound-m-unk
    pen-and-unk True    Unknown = sound-pen
    pen-and-unk True    Pending = sound-pen
    pen-and-unk False   True    = sound-pen
    pen-and-unk False   False   = sound-ff
    pen-and-unk False   Unknown = sound-pen
    pen-and-unk False   Pending = sound-pen
    pen-and-unk Unknown True    = sound-pen
    pen-and-unk Unknown False   = sound-m-unk
    pen-and-unk Unknown Unknown = sound-pen
    pen-and-unk Unknown Pending = sound-pen
    pen-and-unk Pending True    = sound-pen
    pen-and-unk Pending False   = sound-m-pen
    pen-and-unk Pending Unknown = sound-pen
    pen-and-unk Pending Pending = sound-pen
sound-and {m₁} {_} {_} {d₂} sound-pen sound-m-pen = pen-and-pen m₁ d₂
  where
    pen-and-pen : ∀ a b → Sound (a ∧TV Pending) (Pending ∧TV b)
    pen-and-pen True    True    = sound-pen
    pen-and-pen True    False   = sound-m-pen
    pen-and-pen True    Unknown = sound-pen
    pen-and-pen True    Pending = sound-pen
    pen-and-pen False   True    = sound-pen
    pen-and-pen False   False   = sound-ff
    pen-and-pen False   Unknown = sound-pen
    pen-and-pen False   Pending = sound-pen
    pen-and-pen Unknown True    = sound-pen
    pen-and-pen Unknown False   = sound-m-pen
    pen-and-pen Unknown Unknown = sound-pen
    pen-and-pen Unknown Pending = sound-pen
    pen-and-pen Pending True    = sound-pen
    pen-and-pen Pending False   = sound-m-pen
    pen-and-pen Pending Unknown = sound-pen
    pen-and-pen Pending Pending = sound-pen
sound-and sound-m-unk sound-tt = sound-m-unk
sound-and {_} {d₁} sound-m-unk sound-ff rewrite ∧TV-false-r d₁ = sound-ff
sound-and {_} {d₁} {m₂} {_} sound-m-unk sound-unk = munk-and-unk m₂ d₁
  where
    munk-and-unk : ∀ a b → Sound (Unknown ∧TV a) (b ∧TV Unknown)
    munk-and-unk True    True    = sound-unk
    munk-and-unk True    False   = sound-m-unk
    munk-and-unk True    Unknown = sound-unk
    munk-and-unk True    Pending = sound-pen
    munk-and-unk False   True    = sound-unk
    munk-and-unk False   False   = sound-ff
    munk-and-unk False   Unknown = sound-unk
    munk-and-unk False   Pending = sound-pen
    munk-and-unk Unknown True    = sound-unk
    munk-and-unk Unknown False   = sound-m-unk
    munk-and-unk Unknown Unknown = sound-unk
    munk-and-unk Unknown Pending = sound-pen
    munk-and-unk Pending True    = sound-unk
    munk-and-unk Pending False   = sound-m-pen
    munk-and-unk Pending Unknown = sound-unk
    munk-and-unk Pending Pending = sound-pen
sound-and {_} {d₁} {m₂} {_} sound-m-unk sound-pen = munk-and-pen m₂ d₁
  where
    munk-and-pen : ∀ a b → Sound (Unknown ∧TV a) (b ∧TV Pending)
    munk-and-pen True    True    = sound-pen
    munk-and-pen True    False   = sound-m-unk
    munk-and-pen True    Unknown = sound-pen
    munk-and-pen True    Pending = sound-pen
    munk-and-pen False   True    = sound-pen
    munk-and-pen False   False   = sound-ff
    munk-and-pen False   Unknown = sound-pen
    munk-and-pen False   Pending = sound-pen
    munk-and-pen Unknown True    = sound-pen
    munk-and-pen Unknown False   = sound-m-unk
    munk-and-pen Unknown Unknown = sound-pen
    munk-and-pen Unknown Pending = sound-pen
    munk-and-pen Pending True    = sound-pen
    munk-and-pen Pending False   = sound-m-pen
    munk-and-pen Pending Unknown = sound-pen
    munk-and-pen Pending Pending = sound-pen
sound-and sound-m-unk sound-m-unk = sound-m-unk
sound-and sound-m-unk sound-m-pen = sound-m-pen
sound-and sound-m-pen sound-tt = sound-m-pen
sound-and {_} {d₁} sound-m-pen sound-ff rewrite ∧TV-false-r d₁ = sound-ff
sound-and {_} {d₁} {m₂} {_} sound-m-pen sound-unk = mpen-and-unk m₂ d₁
  where
    mpen-and-unk : ∀ a b → Sound (Pending ∧TV a) (b ∧TV Unknown)
    mpen-and-unk True    True    = sound-unk
    mpen-and-unk True    False   = sound-m-pen
    mpen-and-unk True    Unknown = sound-unk
    mpen-and-unk True    Pending = sound-pen
    mpen-and-unk False   True    = sound-unk
    mpen-and-unk False   False   = sound-ff
    mpen-and-unk False   Unknown = sound-unk
    mpen-and-unk False   Pending = sound-pen
    mpen-and-unk Unknown True    = sound-unk
    mpen-and-unk Unknown False   = sound-m-pen
    mpen-and-unk Unknown Unknown = sound-unk
    mpen-and-unk Unknown Pending = sound-pen
    mpen-and-unk Pending True    = sound-unk
    mpen-and-unk Pending False   = sound-m-pen
    mpen-and-unk Pending Unknown = sound-unk
    mpen-and-unk Pending Pending = sound-pen
sound-and {_} {d₁} {m₂} {_} sound-m-pen sound-pen = mpen-and-pen m₂ d₁
  where
    mpen-and-pen : ∀ a b → Sound (Pending ∧TV a) (b ∧TV Pending)
    mpen-and-pen True    True    = sound-pen
    mpen-and-pen True    False   = sound-m-pen
    mpen-and-pen True    Unknown = sound-pen
    mpen-and-pen True    Pending = sound-pen
    mpen-and-pen False   True    = sound-pen
    mpen-and-pen False   False   = sound-ff
    mpen-and-pen False   Unknown = sound-pen
    mpen-and-pen False   Pending = sound-pen
    mpen-and-pen Unknown True    = sound-pen
    mpen-and-pen Unknown False   = sound-m-pen
    mpen-and-pen Unknown Unknown = sound-pen
    mpen-and-pen Unknown Pending = sound-pen
    mpen-and-pen Pending True    = sound-pen
    mpen-and-pen Pending False   = sound-m-pen
    mpen-and-pen Pending Unknown = sound-pen
    mpen-and-pen Pending Pending = sound-pen
sound-and sound-m-pen sound-m-unk = sound-m-pen
sound-and sound-m-pen sound-m-pen = sound-m-pen

sound-or : ∀ {m₁ d₁ m₂ d₂} → Sound m₁ d₁ → Sound m₂ d₂ → Sound (m₁ ∨TV m₂) (d₁ ∨TV d₂)
sound-or sound-tt _ = sound-tt
sound-or sound-ff sound-tt = sound-tt
sound-or sound-ff sound-ff = sound-ff
sound-or sound-ff sound-unk = sound-unk
sound-or sound-ff sound-pen = sound-pen
sound-or sound-ff sound-m-unk = sound-m-unk
sound-or sound-ff sound-m-pen = sound-m-pen
sound-or {m₁} sound-unk sound-tt rewrite ∨TV-true-r m₁ = sound-tt
sound-or sound-unk sound-ff = sound-unk
sound-or sound-unk sound-unk = sound-unk
sound-or sound-unk sound-pen = sound-pen
sound-or {m₁} {_} {_} {d₂} sound-unk sound-m-unk = unk-or-unk m₁ d₂
  where
    unk-or-unk : ∀ a b → Sound (a ∨TV Unknown) (Unknown ∨TV b)
    unk-or-unk True    True    = sound-tt
    unk-or-unk True    False   = sound-unk
    unk-or-unk True    Unknown = sound-unk
    unk-or-unk True    Pending = sound-pen
    unk-or-unk False   True    = sound-m-unk
    unk-or-unk False   False   = sound-unk
    unk-or-unk False   Unknown = sound-unk
    unk-or-unk False   Pending = sound-pen
    unk-or-unk Unknown True    = sound-m-unk
    unk-or-unk Unknown False   = sound-unk
    unk-or-unk Unknown Unknown = sound-unk
    unk-or-unk Unknown Pending = sound-pen
    unk-or-unk Pending True    = sound-m-pen
    unk-or-unk Pending False   = sound-unk
    unk-or-unk Pending Unknown = sound-unk
    unk-or-unk Pending Pending = sound-pen
sound-or {m₁} {_} {_} {d₂} sound-unk sound-m-pen = unk-or-pen m₁ d₂
  where
    unk-or-pen : ∀ a b → Sound (a ∨TV Pending) (Unknown ∨TV b)
    unk-or-pen True    True    = sound-tt
    unk-or-pen True    False   = sound-unk
    unk-or-pen True    Unknown = sound-unk
    unk-or-pen True    Pending = sound-pen
    unk-or-pen False   True    = sound-m-pen
    unk-or-pen False   False   = sound-unk
    unk-or-pen False   Unknown = sound-unk
    unk-or-pen False   Pending = sound-pen
    unk-or-pen Unknown True    = sound-m-pen
    unk-or-pen Unknown False   = sound-unk
    unk-or-pen Unknown Unknown = sound-unk
    unk-or-pen Unknown Pending = sound-pen
    unk-or-pen Pending True    = sound-m-pen
    unk-or-pen Pending False   = sound-unk
    unk-or-pen Pending Unknown = sound-unk
    unk-or-pen Pending Pending = sound-pen
sound-or {m₁} sound-pen sound-tt rewrite ∨TV-true-r m₁ = sound-tt
sound-or {m₁} sound-pen sound-ff rewrite ∨TV-false-r m₁ = sound-pen
sound-or sound-pen sound-unk = sound-pen
sound-or sound-pen sound-pen = sound-pen
sound-or {m₁} {_} {_} {d₂} sound-pen sound-m-unk = pen-or-unk m₁ d₂
  where
    pen-or-unk : ∀ a b → Sound (a ∨TV Unknown) (Pending ∨TV b)
    pen-or-unk True    True    = sound-tt
    pen-or-unk True    False   = sound-pen
    pen-or-unk True    Unknown = sound-pen
    pen-or-unk True    Pending = sound-pen
    pen-or-unk False   True    = sound-m-unk
    pen-or-unk False   False   = sound-pen
    pen-or-unk False   Unknown = sound-pen
    pen-or-unk False   Pending = sound-pen
    pen-or-unk Unknown True    = sound-m-unk
    pen-or-unk Unknown False   = sound-pen
    pen-or-unk Unknown Unknown = sound-pen
    pen-or-unk Unknown Pending = sound-pen
    pen-or-unk Pending True    = sound-m-pen
    pen-or-unk Pending False   = sound-pen
    pen-or-unk Pending Unknown = sound-pen
    pen-or-unk Pending Pending = sound-pen
sound-or {m₁} {_} {_} {d₂} sound-pen sound-m-pen = pen-or-pen m₁ d₂
  where
    pen-or-pen : ∀ a b → Sound (a ∨TV Pending) (Pending ∨TV b)
    pen-or-pen True    True    = sound-tt
    pen-or-pen True    False   = sound-pen
    pen-or-pen True    Unknown = sound-pen
    pen-or-pen True    Pending = sound-pen
    pen-or-pen False   True    = sound-m-pen
    pen-or-pen False   False   = sound-pen
    pen-or-pen False   Unknown = sound-pen
    pen-or-pen False   Pending = sound-pen
    pen-or-pen Unknown True    = sound-m-pen
    pen-or-pen Unknown False   = sound-pen
    pen-or-pen Unknown Unknown = sound-pen
    pen-or-pen Unknown Pending = sound-pen
    pen-or-pen Pending True    = sound-m-pen
    pen-or-pen Pending False   = sound-pen
    pen-or-pen Pending Unknown = sound-pen
    pen-or-pen Pending Pending = sound-pen
sound-or {_} {d₁} sound-m-unk sound-tt rewrite ∨TV-true-r d₁ = sound-tt
sound-or sound-m-unk sound-ff = sound-m-unk
sound-or {_} {d₁} {m₂} {_} sound-m-unk sound-unk = munk-or-unk m₂ d₁
  where
    munk-or-unk : ∀ a b → Sound (Unknown ∨TV a) (b ∨TV Unknown)
    munk-or-unk True    True    = sound-tt
    munk-or-unk True    False   = sound-unk
    munk-or-unk True    Unknown = sound-unk
    munk-or-unk True    Pending = sound-pen
    munk-or-unk False   True    = sound-m-unk
    munk-or-unk False   False   = sound-unk
    munk-or-unk False   Unknown = sound-unk
    munk-or-unk False   Pending = sound-pen
    munk-or-unk Unknown True    = sound-m-unk
    munk-or-unk Unknown False   = sound-unk
    munk-or-unk Unknown Unknown = sound-unk
    munk-or-unk Unknown Pending = sound-pen
    munk-or-unk Pending True    = sound-m-pen
    munk-or-unk Pending False   = sound-unk
    munk-or-unk Pending Unknown = sound-unk
    munk-or-unk Pending Pending = sound-pen
sound-or {_} {d₁} {m₂} {_} sound-m-unk sound-pen = munk-or-pen m₂ d₁
  where
    munk-or-pen : ∀ a b → Sound (Unknown ∨TV a) (b ∨TV Pending)
    munk-or-pen True    True    = sound-tt
    munk-or-pen True    False   = sound-pen
    munk-or-pen True    Unknown = sound-pen
    munk-or-pen True    Pending = sound-pen
    munk-or-pen False   True    = sound-m-unk
    munk-or-pen False   False   = sound-pen
    munk-or-pen False   Unknown = sound-pen
    munk-or-pen False   Pending = sound-pen
    munk-or-pen Unknown True    = sound-m-unk
    munk-or-pen Unknown False   = sound-pen
    munk-or-pen Unknown Unknown = sound-pen
    munk-or-pen Unknown Pending = sound-pen
    munk-or-pen Pending True    = sound-m-pen
    munk-or-pen Pending False   = sound-pen
    munk-or-pen Pending Unknown = sound-pen
    munk-or-pen Pending Pending = sound-pen
sound-or sound-m-unk sound-m-unk = sound-m-unk
sound-or sound-m-unk sound-m-pen = sound-m-pen
sound-or {_} {d₁} sound-m-pen sound-tt rewrite ∨TV-true-r d₁ = sound-tt
sound-or {_} {d₁} sound-m-pen sound-ff rewrite ∨TV-false-r d₁ = sound-m-pen
sound-or {_} {d₁} {m₂} {_} sound-m-pen sound-unk = mpen-or-unk m₂ d₁
  where
    mpen-or-unk : ∀ a b → Sound (Pending ∨TV a) (b ∨TV Unknown)
    mpen-or-unk True    True    = sound-tt
    mpen-or-unk True    False   = sound-unk
    mpen-or-unk True    Unknown = sound-unk
    mpen-or-unk True    Pending = sound-pen
    mpen-or-unk False   True    = sound-m-pen
    mpen-or-unk False   False   = sound-unk
    mpen-or-unk False   Unknown = sound-unk
    mpen-or-unk False   Pending = sound-pen
    mpen-or-unk Unknown True    = sound-m-pen
    mpen-or-unk Unknown False   = sound-unk
    mpen-or-unk Unknown Unknown = sound-unk
    mpen-or-unk Unknown Pending = sound-pen
    mpen-or-unk Pending True    = sound-m-pen
    mpen-or-unk Pending False   = sound-unk
    mpen-or-unk Pending Unknown = sound-unk
    mpen-or-unk Pending Pending = sound-pen
sound-or {_} {d₁} {m₂} {_} sound-m-pen sound-pen = mpen-or-pen m₂ d₁
  where
    mpen-or-pen : ∀ a b → Sound (Pending ∨TV a) (b ∨TV Pending)
    mpen-or-pen True    True    = sound-tt
    mpen-or-pen True    False   = sound-pen
    mpen-or-pen True    Unknown = sound-pen
    mpen-or-pen True    Pending = sound-pen
    mpen-or-pen False   True    = sound-m-pen
    mpen-or-pen False   False   = sound-pen
    mpen-or-pen False   Unknown = sound-pen
    mpen-or-pen False   Pending = sound-pen
    mpen-or-pen Unknown True    = sound-m-pen
    mpen-or-pen Unknown False   = sound-pen
    mpen-or-pen Unknown Unknown = sound-pen
    mpen-or-pen Unknown Pending = sound-pen
    mpen-or-pen Pending True    = sound-m-pen
    mpen-or-pen Pending False   = sound-pen
    mpen-or-pen Pending Unknown = sound-pen
    mpen-or-pen Pending Pending = sound-pen
sound-or sound-m-pen sound-m-unk = sound-m-pen
sound-or sound-m-pen sound-m-pen = sound-m-pen

-- Derived combinators: sound-or/sound-and with one absorbing argument.
-- These avoid stuck ∨TV/∧TV reductions (False ∨TV abstract, True ∧TV abstract)
-- by pattern matching on Sound constructors so both sides are concrete.
--
-- Why pattern matching (not subst): When the result of sound-or-false-l is passed
-- to sound-and or other combinators, the monitor component must be fully concrete.
-- subst leaves an abstract ∨TV/∧TV expression that blocks downstream unification.
-- Pattern matching computes the result directly — no stuck terms.

sound-or-false-l : ∀ {d₁ d₂ m₂} → Sound False d₁ → Sound m₂ d₂ → Sound m₂ (d₁ ∨TV d₂)
-- m₂ abstract: result independent of ∨TV computation
sound-or-false-l _         sound-m-unk = sound-m-unk
sound-or-false-l _         sound-m-pen = sound-m-pen
-- Both d₁ and d₂ concrete: ∨TV reduces, result mirrors output
sound-or-false-l sound-ff  sound-tt    = sound-tt
sound-or-false-l sound-ff  sound-ff    = sound-ff
sound-or-false-l sound-ff  sound-unk   = sound-unk
sound-or-false-l sound-ff  sound-pen   = sound-pen
sound-or-false-l sound-unk sound-tt    = sound-tt
sound-or-false-l sound-unk sound-ff    = sound-unk
sound-or-false-l sound-unk sound-unk   = sound-unk
sound-or-false-l sound-unk sound-pen   = sound-pen
sound-or-false-l sound-pen sound-tt    = sound-tt
sound-or-false-l sound-pen sound-ff    = sound-pen
sound-or-false-l sound-pen sound-unk   = sound-pen
sound-or-false-l sound-pen sound-pen   = sound-pen

sound-or-false-r : ∀ {d₁ d₂ m₁} → Sound m₁ d₁ → Sound False d₂ → Sound m₁ (d₁ ∨TV d₂)
sound-or-false-r sound-m-unk _         = sound-m-unk
sound-or-false-r sound-m-pen _         = sound-m-pen
sound-or-false-r sound-tt    _         = sound-tt
sound-or-false-r sound-ff  sound-ff    = sound-ff
sound-or-false-r sound-ff  sound-unk   = sound-unk
sound-or-false-r sound-ff  sound-pen   = sound-pen
sound-or-false-r sound-unk sound-ff    = sound-unk
sound-or-false-r sound-unk sound-unk   = sound-unk
sound-or-false-r sound-unk sound-pen   = sound-pen
sound-or-false-r sound-pen sound-ff    = sound-pen
sound-or-false-r sound-pen sound-unk   = sound-pen
sound-or-false-r sound-pen sound-pen   = sound-pen

sound-and-true-l : ∀ {d₁ d₂ m₂} → Sound True d₁ → Sound m₂ d₂ → Sound m₂ (d₁ ∧TV d₂)
sound-and-true-l _         sound-m-unk = sound-m-unk
sound-and-true-l _         sound-m-pen = sound-m-pen
sound-and-true-l sound-tt  sound-tt    = sound-tt
sound-and-true-l sound-tt  sound-ff    = sound-ff
sound-and-true-l sound-tt  sound-unk   = sound-unk
sound-and-true-l sound-tt  sound-pen   = sound-pen
sound-and-true-l sound-unk sound-tt    = sound-unk
sound-and-true-l sound-unk sound-ff    = sound-ff
sound-and-true-l sound-unk sound-unk   = sound-unk
sound-and-true-l sound-unk sound-pen   = sound-pen
sound-and-true-l sound-pen sound-tt    = sound-pen
sound-and-true-l sound-pen sound-ff    = sound-ff
sound-and-true-l sound-pen sound-unk   = sound-pen
sound-and-true-l sound-pen sound-pen   = sound-pen

sound-and-true-r : ∀ {d₁ d₂ m₁} → Sound m₁ d₁ → Sound True d₂ → Sound m₁ (d₁ ∧TV d₂)
sound-and-true-r sound-m-unk _         = sound-m-unk
sound-and-true-r sound-m-pen _         = sound-m-pen
sound-and-true-r sound-ff    _         = sound-ff
sound-and-true-r sound-tt  sound-tt    = sound-tt
sound-and-true-r sound-tt  sound-unk   = sound-unk
sound-and-true-r sound-tt  sound-pen   = sound-pen
sound-and-true-r sound-unk sound-tt    = sound-unk
sound-and-true-r sound-unk sound-unk   = sound-unk
sound-and-true-r sound-unk sound-pen   = sound-pen
sound-and-true-r sound-pen sound-tt    = sound-pen
sound-and-true-r sound-pen sound-unk   = sound-pen
sound-and-true-r sound-pen sound-pen   = sound-pen

-- ============================================================================
-- FINALIZE-SOUND: finalizeL agrees with denotational semantics (general)
-- ============================================================================

-- For ANY LTLProc (not just initProc-constructed ones), finalization is
-- sound with respect to the denotational semantics of denot(proc).
-- Now takes PredTable for denot conversion.

finalize-sound : ∀ (table : PredTable) (proc : LTLProc)
  → Sound (verdictToSV (finalizeL proc)) (⟦ denot table proc ⟧ [])

-- Atomic: finalizeL = Fails → False; ⟦ Atomic _ ⟧ [] = False
finalize-sound table (Atomic _) = sound-ff

-- Not: Case-split on finalizeL φ and ⟦ denot table φ ⟧ [].
finalize-sound table (Not φ)
  with finalizeL φ | ⟦ denot table φ ⟧ [] | denot-empty-binary (denot table φ) | finalize-sound table φ
... | Holds   | .True  | inj₁ refl | _  = sound-ff
... | Holds   | .False | inj₂ refl | ()
... | Fails _ | .True  | inj₁ refl | ()
... | Fails _ | .False | inj₂ refl | _  = sound-tt

-- And: Case-split on both finalizeL results and both denotations.
finalize-sound table (And φ ψ)
  with finalizeL φ | ⟦ denot table φ ⟧ [] | denot-empty-binary (denot table φ) | finalize-sound table φ
... | Fails _ | .True  | inj₁ refl | ()
... | Fails _ | .False | inj₂ refl | _  = sound-ff
... | Holds   | .False | inj₂ refl | ()
... | Holds   | .True  | inj₁ refl | _
  with finalizeL ψ | ⟦ denot table ψ ⟧ [] | denot-empty-binary (denot table ψ) | finalize-sound table ψ
...   | Holds   | .True  | inj₁ refl | _  = sound-tt
...   | Holds   | .False | inj₂ refl | ()
...   | Fails _ | .True  | inj₁ refl | ()
...   | Fails _ | .False | inj₂ refl | _  = sound-ff

-- Or: Dual of And.
finalize-sound table (Or φ ψ)
  with finalizeL φ | ⟦ denot table φ ⟧ [] | denot-empty-binary (denot table φ) | finalize-sound table φ
... | Holds   | .False | inj₂ refl | ()
... | Holds   | .True  | inj₁ refl | _  = sound-tt
... | Fails _ | .True  | inj₁ refl | ()
... | Fails _ | .False | inj₂ refl | _
  with finalizeL ψ | ⟦ denot table ψ ⟧ [] | denot-empty-binary (denot table ψ) | finalize-sound table ψ
...   | Holds   | .True  | inj₁ refl | _  = sound-tt
...   | Holds   | .False | inj₂ refl | ()
...   | Fails _ | .True  | inj₁ refl | ()
...   | Fails _ | .False | inj₂ refl | _  = sound-ff

-- Next: Fails → False; ⟦ Next (denot table _) ⟧ [] = False
finalize-sound table (Next _) = sound-ff

-- Always: Holds → True; ⟦ Always _ ⟧ [] = True
finalize-sound table (Always _) = sound-tt

-- Eventually: Fails → False; ⟦ Eventually _ ⟧ [] = False
finalize-sound table (Eventually _) = sound-ff

-- Until: Fails → False; ⟦ Until _ _ ⟧ [] = False
finalize-sound table (Until _ _) = sound-ff

-- Release: Holds → True; ⟦ Release _ _ ⟧ [] = True
finalize-sound table (Release _ _) = sound-tt

-- MetricEventually: Fails → False; ⟦ MetricEventually _ _ ⟧ [] = False
finalize-sound table (MetricEventuallyProc _ _ _) = sound-ff

-- MetricAlways: Holds → True; ⟦ MetricAlways _ _ ⟧ [] = True
finalize-sound table (MetricAlwaysProc _ _ _) = sound-tt

-- MetricUntil: Fails → False; ⟦ MetricUntil _ _ _ ⟧ [] = False
finalize-sound table (MetricUntilProc _ _ _ _) = sound-ff

-- MetricRelease: Holds → True; ⟦ MetricRelease _ _ _ ⟧ [] = True
finalize-sound table (MetricReleaseProc _ _ _ _) = sound-tt

-- ============================================================================
-- ABSORPTION LEMMAS FOR ∨TV
-- ============================================================================

-- y ⊑ (Unknown ∨TV y) for any y
⊑-unknown-or-absorb : ∀ y → y ⊑ (Unknown ∨TV y)
⊑-unknown-or-absorb True    = ⊑-refl
⊑-unknown-or-absorb False   = ⊑-unknown
⊑-unknown-or-absorb Unknown = ⊑-refl
⊑-unknown-or-absorb Pending = ⊑-pending

-- y ⊑ (Pending ∨TV y) for any y
⊑-pending-or-absorb : ∀ y → y ⊑ (Pending ∨TV y)
⊑-pending-or-absorb True    = ⊑-refl
⊑-pending-or-absorb False   = ⊑-pending
⊑-pending-or-absorb Unknown = ⊑-pending
⊑-pending-or-absorb Pending = ⊑-refl

-- Sound False (Unknown ∧TV y) for any y.
sound-false-unknown-and : ∀ y → Sound False (Unknown ∧TV y)
sound-false-unknown-and True    = sound-unk
sound-false-unknown-and False   = sound-ff
sound-false-unknown-and Unknown = sound-unk
sound-false-unknown-and Pending = sound-pen

-- ============================================================================
-- GENERAL ADEQUACY (step 18h)
-- ============================================================================

-- runL distributes over And: the coalgebra run of And φ ψ equals
-- the ∧TV combination of the individual runs.
-- Proof: list induction on σ. Base case uses finalizeL decomposition.
-- Inductive case uses combineAnd decomposition + IH.

runL-and-decomp : ∀ (table : PredTable) (φ ψ : LTLProc) (σ : List TimedFrame)
  → runL table (And φ ψ) σ ≡ (runL table φ σ) ∧TV (runL table ψ σ)
runL-and-decomp table φ ψ [] with finalizeL φ
... | Fails _ = refl
... | Holds with finalizeL ψ
...   | Fails _ = refl
...   | Holds   = refl
runL-and-decomp table φ ψ (x ∷ σ) with stepL table φ x | stepL table ψ x
... | Violated _   | _             = refl
... | Satisfied    | Violated _    = refl
... | Continue _ a | Violated _    rewrite ∧TV-false-r (runL table a σ) = refl
... | Satisfied    | Satisfied     = refl
... | Satisfied    | Continue _ b  rewrite ∧TV-true-l (runL table b σ) = refl
... | Continue _ a | Satisfied     rewrite ∧TV-true-r (runL table a σ) = refl
... | Continue _ a | Continue _ b  = runL-and-decomp table a b σ

-- runL distributes over Not: coalgebra run of Not φ equals notTV of the inner run.
runL-not-decomp : ∀ (table : PredTable) (φ : LTLProc) (σ : List TimedFrame)
  → runL table (Not φ) σ ≡ notTV (runL table φ σ)
runL-not-decomp table φ [] with finalizeL φ
... | Holds   = refl
... | Fails _ = refl
runL-not-decomp table φ (x ∷ σ) with stepL table φ x
... | Satisfied    = refl
... | Violated _   = refl
... | Continue _ φ' = runL-not-decomp table φ' σ

-- runL distributes over Or: dual of runL-and-decomp.
runL-or-decomp : ∀ (table : PredTable) (φ ψ : LTLProc) (σ : List TimedFrame)
  → runL table (Or φ ψ) σ ≡ (runL table φ σ) ∨TV (runL table ψ σ)
runL-or-decomp table φ ψ [] with finalizeL φ
... | Holds = refl
... | Fails _ with finalizeL ψ
...   | Holds   = refl
...   | Fails _ = refl
runL-or-decomp table φ ψ (x ∷ σ) with stepL table φ x | stepL table ψ x
... | Satisfied    | _             = refl
... | Violated _   | Satisfied     = refl
... | Violated _   | Violated _    = refl
... | Violated _   | Continue _ b  rewrite ∨TV-false-l (runL table b σ) = refl
... | Continue _ a | Satisfied     rewrite ∨TV-true-r (runL table a σ) = refl
... | Continue _ a | Violated _    rewrite ∨TV-false-r (runL table a σ) = refl
... | Continue _ a | Continue _ b  = runL-or-decomp table a b σ

-- runL distributes over Always: coalgebra run decomposes like the denotational semantics.
-- Always φ steps as combineAnd (stepL φ) (Continue 0 (Always φ)), matching ⟦φ⟧∧TV⟦G φ⟧.
runL-always-decomp : ∀ (table : PredTable) (φ : LTLProc) (x : TimedFrame) (rest : List TimedFrame)
  → runL table (Always φ) (x ∷ rest) ≡ (runL table φ (x ∷ rest)) ∧TV (runL table (Always φ) rest)
runL-always-decomp table φ x rest with stepL table φ x
... | Satisfied     rewrite ∧TV-true-l (runL table (Always φ) rest) = refl
... | Violated _    = refl
... | Continue _ φ' = runL-and-decomp table φ' (Always φ) rest

-- runL distributes over Eventually: dual of Always decomposition.
-- Eventually φ steps as combineOr (stepL φ) (Continue 0 (Eventually φ)), matching ⟦φ⟧∨TV⟦F φ⟧.
runL-eventually-decomp : ∀ (table : PredTable) (φ : LTLProc) (x : TimedFrame) (rest : List TimedFrame)
  → runL table (Eventually φ) (x ∷ rest) ≡ (runL table φ (x ∷ rest)) ∨TV (runL table (Eventually φ) rest)
runL-eventually-decomp table φ x rest with stepL table φ x
... | Satisfied     = refl
... | Violated _    rewrite ∨TV-false-l (runL table (Eventually φ) rest) = refl
... | Continue _ φ' = runL-or-decomp table φ' (Eventually φ) rest

-- runL distributes over Until: φ U ψ ≡ ψ ∨ (φ ∧ X(φ U ψ)).
-- stepL(Until φ ψ) = combineOr (stepL ψ) (combineAnd (stepL φ) (Continue 0 (Until φ ψ)))
runL-until-decomp : ∀ (table : PredTable) (φ ψ : LTLProc) (x : TimedFrame) (rest : List TimedFrame)
  → runL table (Until φ ψ) (x ∷ rest)
    ≡ (runL table ψ (x ∷ rest)) ∨TV ((runL table φ (x ∷ rest)) ∧TV (runL table (Until φ ψ) rest))
runL-until-decomp table φ ψ x rest with stepL table ψ x | stepL table φ x
... | Satisfied     | _             = refl
... | Violated _    | Violated _    = refl
... | Violated _    | Satisfied
    rewrite ∧TV-true-l (runL table (Until φ ψ) rest)
          | ∨TV-false-l (runL table (Until φ ψ) rest) = refl
... | Violated _    | Continue _ φ'
    rewrite ∨TV-false-l ((runL table φ' rest) ∧TV (runL table (Until φ ψ) rest))
    = runL-and-decomp table φ' (Until φ ψ) rest
... | Continue _ ψ' | Violated _
    rewrite ∨TV-false-r (runL table ψ' rest) = refl
... | Continue _ ψ' | Satisfied
    rewrite ∧TV-true-l (runL table (Until φ ψ) rest)
    = runL-or-decomp table ψ' (Until φ ψ) rest
... | Continue _ ψ' | Continue _ φ'
    rewrite sym (runL-and-decomp table φ' (Until φ ψ) rest)
    = runL-or-decomp table ψ' (And φ' (Until φ ψ)) rest

-- runL distributes over Release: φ R ψ ≡ ψ ∧ (φ ∨ X(φ R ψ)).
-- stepL(Release φ ψ) = combineAnd (stepL ψ) (combineOr (stepL φ) (Continue 0 (Release φ ψ)))
runL-release-decomp : ∀ (table : PredTable) (φ ψ : LTLProc) (x : TimedFrame) (rest : List TimedFrame)
  → runL table (Release φ ψ) (x ∷ rest)
    ≡ (runL table ψ (x ∷ rest)) ∧TV ((runL table φ (x ∷ rest)) ∨TV (runL table (Release φ ψ) rest))
runL-release-decomp table φ ψ x rest with stepL table ψ x | stepL table φ x
... | Violated _    | _             = refl
... | Satisfied     | Satisfied     = refl
... | Satisfied     | Violated _
    rewrite ∨TV-false-l (runL table (Release φ ψ) rest)
          | ∧TV-true-l (runL table (Release φ ψ) rest) = refl
... | Satisfied     | Continue _ φ'
    rewrite ∧TV-true-l ((runL table φ' rest) ∨TV (runL table (Release φ ψ) rest))
    = runL-or-decomp table φ' (Release φ ψ) rest
... | Continue _ ψ' | Satisfied
    rewrite ∧TV-true-r (runL table ψ' rest) = refl
... | Continue _ ψ' | Violated _
    rewrite ∨TV-false-l (runL table (Release φ ψ) rest)
    = runL-and-decomp table ψ' (Release φ ψ) rest
... | Continue _ ψ' | Continue _ φ'
    rewrite sym (runL-or-decomp table φ' (Release φ ψ) rest)
    = runL-and-decomp table ψ' (Or φ' (Release φ ψ)) rest

-- ============================================================================
-- METRIC OPERATOR HELPERS
-- ============================================================================

-- Bridge between met-*-go helpers and ⟦ Metric* (suc start) ⟧.
-- The go helpers are top-level mutual functions in Semantics.agda.
-- Key property: met-ev-go w φ start σ ≡ ⟦ MetricEventually w (suc start) φ ⟧ σ
-- This is NOT definitional for abstract σ (both are stuck pattern matches),
-- but holds by case split on σ (both clauses are refl).

private
  met-ev-go-denot : ∀ (w : ℕ) (φ : LTL (TimedFrame → SignalVal)) (start : ℕ) (σ : List TimedFrame)
    → met-ev-go w φ start σ ≡ ⟦ Syntax.MetricEventually w (suc start) φ ⟧ σ
  met-ev-go-denot w φ start [] = refl
  met-ev-go-denot w φ start (_ ∷ _) = refl

  met-al-go-denot : ∀ (w : ℕ) (φ : LTL (TimedFrame → SignalVal)) (start : ℕ) (σ : List TimedFrame)
    → met-al-go w φ start σ ≡ ⟦ Syntax.MetricAlways w (suc start) φ ⟧ σ
  met-al-go-denot w φ start [] = refl
  met-al-go-denot w φ start (_ ∷ _) = refl

  met-un-go-denot : ∀ (w : ℕ) (φ ψ : LTL (TimedFrame → SignalVal)) (start : ℕ) (σ : List TimedFrame)
    → met-un-go w φ ψ start σ ≡ ⟦ Syntax.MetricUntil w (suc start) φ ψ ⟧ σ
  met-un-go-denot w φ ψ start [] = refl
  met-un-go-denot w φ ψ start (_ ∷ _) = refl

  met-re-go-denot : ∀ (w : ℕ) (φ ψ : LTL (TimedFrame → SignalVal)) (start : ℕ) (σ : List TimedFrame)
    → met-re-go w φ ψ start σ ≡ ⟦ Syntax.MetricRelease w (suc start) φ ψ ⟧ σ
  met-re-go-denot w φ ψ start [] = refl
  met-re-go-denot w φ ψ start (_ ∷ _) = refl

-- Generic monitor-side transport: rewrite the monitor argument of Sound
-- along an equality, without generating with-auxiliaries (unlike rewrite).
-- This is the single pattern that all operational transport lemmas use.

sound-transport-monitor : ∀ {m₁ m₂ d} → m₁ ≡ m₂ → Sound m₁ d → Sound m₂ d
sound-transport-monitor {d = d} eq = subst (λ m → Sound m d) eq

sound-transport-denot : ∀ {m d₁ d₂} → d₁ ≡ d₂ → Sound m d₁ → Sound m d₂
sound-transport-denot {m = m} eq = subst (Sound m) eq

-- Denotational transport: convert adequacy IH from ⟦ MetricOp (suc start) ⟧
-- to met-*-go. These avoid `rewrite met-*-go-denot` which generates
-- with-auxiliaries that hide recursive calls from the termination checker.

met-ev-go-sound : ∀ {m} w φ start rest →
  Sound m (⟦ Syntax.MetricEventually w (suc start) φ ⟧ rest) →
  Sound m (met-ev-go w φ start rest)
met-ev-go-sound w φ start rest =
  sound-transport-denot (sym (met-ev-go-denot w φ start rest))

met-al-go-sound : ∀ {m} w φ start rest →
  Sound m (⟦ Syntax.MetricAlways w (suc start) φ ⟧ rest) →
  Sound m (met-al-go w φ start rest)
met-al-go-sound w φ start rest =
  sound-transport-denot (sym (met-al-go-denot w φ start rest))

met-un-go-sound : ∀ {m} w φ ψ start rest →
  Sound m (⟦ Syntax.MetricUntil w (suc start) φ ψ ⟧ rest) →
  Sound m (met-un-go w φ ψ start rest)
met-un-go-sound w φ ψ start rest =
  sound-transport-denot (sym (met-un-go-denot w φ ψ start rest))

met-re-go-sound : ∀ {m} w φ ψ start rest →
  Sound m (⟦ Syntax.MetricRelease w (suc start) φ ψ ⟧ rest) →
  Sound m (met-re-go w φ ψ start rest)
met-re-go-sound w φ ψ start rest =
  sound-transport-denot (sym (met-re-go-denot w φ ψ start rest))

-- Monitor-side transport: convert between runL on composed formulas
-- and ∨TV/∧TV of decomposed runL results.

runL-or-sound : ∀ {d} (table : PredTable) (φ ψ : LTLProc) (σ : List TimedFrame)
  → Sound (runL table φ σ ∨TV runL table ψ σ) d
  → Sound (runL table (Or φ ψ) σ) d
runL-or-sound table φ ψ σ =
  sound-transport-monitor (sym (runL-or-decomp table φ ψ σ))

runL-and-sound : ∀ {d} (table : PredTable) (φ ψ : LTLProc) (σ : List TimedFrame)
  → Sound (runL table φ σ ∧TV runL table ψ σ) d
  → Sound (runL table (And φ ψ) σ) d
runL-and-sound table φ ψ σ =
  sound-transport-monitor (sym (runL-and-decomp table φ ψ σ))

-- ============================================================================
-- METRIC DECOMPOSITION LEMMAS
-- ============================================================================

-- Conditional decomposition: when inWindow ≡ true, the metric operators
-- decompose like their unbounded counterparts (Eventually/Always/Until/Release).
-- The false case is absurd (discharged via () on the equality proof).

-- MetricEventually: mirrors runL-eventually-decomp
runL-metric-eventually-decomp : ∀ (table : PredTable) (w s : ℕ) (φ : LTLProc) (x : TimedFrame) (rest : List TimedFrame)
  → ((timestamp x ∸ decodeStart s (timestamp x)) ≤ᵇ w) ≡ true
  → runL table (MetricEventuallyProc w s φ) (x ∷ rest)
    ≡ (runL table φ (x ∷ rest)) ∨TV (runL table (MetricEventuallyProc w (suc (decodeStart s (timestamp x))) φ) rest)
runL-metric-eventually-decomp table w s φ x rest eq
  with (timestamp x ∸ decodeStart s (timestamp x)) ≤ᵇ w
runL-metric-eventually-decomp table w s φ x rest () | false
runL-metric-eventually-decomp table w s φ x rest eq | true with stepL table φ x
... | Satisfied     = refl
... | Violated _    rewrite ∨TV-false-l (runL table (MetricEventuallyProc w (suc (decodeStart s (timestamp x))) φ) rest) = refl
... | Continue _ φ' = runL-or-decomp table φ' (MetricEventuallyProc w (suc (decodeStart s (timestamp x))) φ) rest

-- MetricAlways: mirrors runL-always-decomp
runL-metric-always-decomp : ∀ (table : PredTable) (w s : ℕ) (φ : LTLProc) (x : TimedFrame) (rest : List TimedFrame)
  → ((timestamp x ∸ decodeStart s (timestamp x)) ≤ᵇ w) ≡ true
  → runL table (MetricAlwaysProc w s φ) (x ∷ rest)
    ≡ (runL table φ (x ∷ rest)) ∧TV (runL table (MetricAlwaysProc w (suc (decodeStart s (timestamp x))) φ) rest)
runL-metric-always-decomp table w s φ x rest eq
  with (timestamp x ∸ decodeStart s (timestamp x)) ≤ᵇ w
runL-metric-always-decomp table w s φ x rest () | false
runL-metric-always-decomp table w s φ x rest eq | true with stepL table φ x
... | Satisfied     rewrite ∧TV-true-l (runL table (MetricAlwaysProc w (suc (decodeStart s (timestamp x))) φ) rest) = refl
... | Violated _    = refl
... | Continue _ φ' = runL-and-decomp table φ' (MetricAlwaysProc w (suc (decodeStart s (timestamp x))) φ) rest

-- MetricUntil: mirrors runL-until-decomp
runL-metric-until-decomp : ∀ (table : PredTable) (w s : ℕ) (φ ψ : LTLProc) (x : TimedFrame) (rest : List TimedFrame)
  → ((timestamp x ∸ decodeStart s (timestamp x)) ≤ᵇ w) ≡ true
  → runL table (MetricUntilProc w s φ ψ) (x ∷ rest)
    ≡ (runL table ψ (x ∷ rest)) ∨TV ((runL table φ (x ∷ rest)) ∧TV (runL table (MetricUntilProc w (suc (decodeStart s (timestamp x))) φ ψ) rest))
runL-metric-until-decomp table w s φ ψ x rest eq
  with (timestamp x ∸ decodeStart s (timestamp x)) ≤ᵇ w
runL-metric-until-decomp table w s φ ψ x rest () | false
runL-metric-until-decomp table w s φ ψ x rest eq | true with stepL table ψ x | stepL table φ x
... | Satisfied     | _             = refl
... | Violated _    | Violated _    = refl
... | Violated _    | Satisfied
    rewrite ∧TV-true-l (runL table (MetricUntilProc w (suc (decodeStart s (timestamp x))) φ ψ) rest)
          | ∨TV-false-l (runL table (MetricUntilProc w (suc (decodeStart s (timestamp x))) φ ψ) rest) = refl
... | Violated _    | Continue _ φ'
    rewrite ∨TV-false-l ((runL table φ' rest) ∧TV (runL table (MetricUntilProc w (suc (decodeStart s (timestamp x))) φ ψ) rest))
    = runL-and-decomp table φ' (MetricUntilProc w (suc (decodeStart s (timestamp x))) φ ψ) rest
... | Continue _ ψ' | Violated _
    rewrite ∨TV-false-r (runL table ψ' rest) = refl
... | Continue _ ψ' | Satisfied
    rewrite ∧TV-true-l (runL table (MetricUntilProc w (suc (decodeStart s (timestamp x))) φ ψ) rest)
    = runL-or-decomp table ψ' (MetricUntilProc w (suc (decodeStart s (timestamp x))) φ ψ) rest
... | Continue _ ψ' | Continue _ φ'
    rewrite sym (runL-and-decomp table φ' (MetricUntilProc w (suc (decodeStart s (timestamp x))) φ ψ) rest)
    = runL-or-decomp table ψ' (And φ' (MetricUntilProc w (suc (decodeStart s (timestamp x))) φ ψ)) rest

-- MetricRelease: mirrors runL-release-decomp
runL-metric-release-decomp : ∀ (table : PredTable) (w s : ℕ) (φ ψ : LTLProc) (x : TimedFrame) (rest : List TimedFrame)
  → ((timestamp x ∸ decodeStart s (timestamp x)) ≤ᵇ w) ≡ true
  → runL table (MetricReleaseProc w s φ ψ) (x ∷ rest)
    ≡ (runL table ψ (x ∷ rest)) ∧TV ((runL table φ (x ∷ rest)) ∨TV (runL table (MetricReleaseProc w (suc (decodeStart s (timestamp x))) φ ψ) rest))
runL-metric-release-decomp table w s φ ψ x rest eq
  with (timestamp x ∸ decodeStart s (timestamp x)) ≤ᵇ w
runL-metric-release-decomp table w s φ ψ x rest () | false
runL-metric-release-decomp table w s φ ψ x rest eq | true with stepL table ψ x | stepL table φ x
... | Violated _    | _             = refl
... | Satisfied     | Satisfied     = refl
... | Satisfied     | Violated _
    rewrite ∨TV-false-l (runL table (MetricReleaseProc w (suc (decodeStart s (timestamp x))) φ ψ) rest)
          | ∧TV-true-l (runL table (MetricReleaseProc w (suc (decodeStart s (timestamp x))) φ ψ) rest) = refl
... | Satisfied     | Continue _ φ'
    rewrite ∧TV-true-l ((runL table φ' rest) ∨TV (runL table (MetricReleaseProc w (suc (decodeStart s (timestamp x))) φ ψ) rest))
    = runL-or-decomp table φ' (MetricReleaseProc w (suc (decodeStart s (timestamp x))) φ ψ) rest
... | Continue _ ψ' | Satisfied
    rewrite ∧TV-true-r (runL table ψ' rest) = refl
... | Continue _ ψ' | Violated _
    rewrite ∨TV-false-l (runL table (MetricReleaseProc w (suc (decodeStart s (timestamp x))) φ ψ) rest)
    = runL-and-decomp table ψ' (MetricReleaseProc w (suc (decodeStart s (timestamp x))) φ ψ) rest
... | Continue _ ψ' | Continue _ φ'
    rewrite sym (runL-or-decomp table φ' (MetricReleaseProc w (suc (decodeStart s (timestamp x))) φ ψ) rest)
    = runL-and-decomp table ψ' (Or φ' (MetricReleaseProc w (suc (decodeStart s (timestamp x))) φ ψ)) rest

-- ============================================================================
-- METRIC ADEQUACY HELPERS (non-recursive)
-- ============================================================================

-- These helpers extract the boolean + stepL case analysis from adequacy,
-- so that adequacy itself has zero `with`s for metric operators.
-- The termination checker can then see the direct recursive calls.

-- MetricEventually: boolean guard + stepL case split. Non-recursive.
adequacy-met-ev : ∀ (table : PredTable) (w s : ℕ) (φ : LTLProc) (y : TimedFrame) (rest : List TimedFrame)
  → Sound (runL table φ (y ∷ rest)) (⟦ denot table φ ⟧ (y ∷ rest))
  → Sound (runL table (MetricEventuallyProc w (suc (decodeStart s (timestamp y))) φ) rest)
          (met-ev-go w (denot table φ) (decodeStart s (timestamp y)) rest)
  → Sound (runL table (MetricEventuallyProc w s φ) (y ∷ rest))
          (⟦ denot table (MetricEventuallyProc w s φ) ⟧ (y ∷ rest))
adequacy-met-ev table w s φ y rest ih-φ ih-MEP
  with (timestamp y ∸ decodeStart s (timestamp y)) ≤ᵇ w
... | false = sound-ff
... | true with stepL table φ y
...   | Satisfied   = sound-or ih-φ ih-MEP
...   | Violated _  = sound-or-false-l ih-φ ih-MEP
...   | Continue _ φ' = runL-or-sound table φ' (MetricEventuallyProc w (suc (decodeStart s (timestamp y))) φ) rest
                          (sound-or ih-φ ih-MEP)

-- MetricAlways: dual of MetricEventually (∧ instead of ∨, sound-tt on window expiry).
adequacy-met-al : ∀ (table : PredTable) (w s : ℕ) (φ : LTLProc) (y : TimedFrame) (rest : List TimedFrame)
  → Sound (runL table φ (y ∷ rest)) (⟦ denot table φ ⟧ (y ∷ rest))
  → Sound (runL table (MetricAlwaysProc w (suc (decodeStart s (timestamp y))) φ) rest)
          (met-al-go w (denot table φ) (decodeStart s (timestamp y)) rest)
  → Sound (runL table (MetricAlwaysProc w s φ) (y ∷ rest))
          (⟦ denot table (MetricAlwaysProc w s φ) ⟧ (y ∷ rest))
adequacy-met-al table w s φ y rest ih-φ ih-MAP
  with (timestamp y ∸ decodeStart s (timestamp y)) ≤ᵇ w
... | false = sound-tt
... | true with stepL table φ y
...   | Satisfied   = sound-and-true-l ih-φ ih-MAP
...   | Violated _  = sound-and ih-φ ih-MAP
...   | Continue _ φ' = runL-and-sound table φ' (MetricAlwaysProc w (suc (decodeStart s (timestamp y))) φ) rest
                          (sound-and ih-φ ih-MAP)

-- MetricUntil: simultaneous (stepL ψ × stepL φ) after boolean guard. Non-recursive.
adequacy-met-un : ∀ (table : PredTable) (w s : ℕ) (φ ψ : LTLProc) (y : TimedFrame) (rest : List TimedFrame)
  → Sound (runL table φ (y ∷ rest)) (⟦ denot table φ ⟧ (y ∷ rest))
  → Sound (runL table ψ (y ∷ rest)) (⟦ denot table ψ ⟧ (y ∷ rest))
  → Sound (runL table (MetricUntilProc w (suc (decodeStart s (timestamp y))) φ ψ) rest)
          (met-un-go w (denot table φ) (denot table ψ) (decodeStart s (timestamp y)) rest)
  → Sound (runL table (MetricUntilProc w s φ ψ) (y ∷ rest))
          (⟦ denot table (MetricUntilProc w s φ ψ) ⟧ (y ∷ rest))
adequacy-met-un table w s φ ψ y rest ih-φ ih-ψ ih-MUP
  with (timestamp y ∸ decodeStart s (timestamp y)) ≤ᵇ w
... | false = sound-ff
... | true with stepL table ψ y | stepL table φ y
...   | Satisfied     | _             = sound-or ih-ψ (sound-and ih-φ ih-MUP)
...   | Violated _    | Satisfied     = sound-or-false-l ih-ψ (sound-and-true-l ih-φ ih-MUP)
...   | Violated _    | Violated _    = sound-or ih-ψ (sound-and ih-φ ih-MUP)
...   | Violated _    | Continue _ φ' = sound-or-false-l ih-ψ
                                          (runL-and-sound table φ' (MetricUntilProc w (suc (decodeStart s (timestamp y))) φ ψ) rest
                                            (sound-and ih-φ ih-MUP))
...   | Continue _ ψ' | Satisfied     = runL-or-sound table ψ' (MetricUntilProc w (suc (decodeStart s (timestamp y))) φ ψ) rest
                                          (sound-or ih-ψ (sound-and-true-l ih-φ ih-MUP))
...   | Continue _ ψ' | Violated _    = sound-or-false-r ih-ψ (sound-and ih-φ ih-MUP)
...   | Continue _ ψ' | Continue _ φ' = runL-or-sound table ψ' (And φ' (MetricUntilProc w (suc (decodeStart s (timestamp y))) φ ψ)) rest
                                          (sound-or ih-ψ
                                            (runL-and-sound table φ' (MetricUntilProc w (suc (decodeStart s (timestamp y))) φ ψ) rest
                                              (sound-and ih-φ ih-MUP)))

-- MetricRelease: dual of MetricUntil (∧/∨ swapped). Non-recursive.
-- Decomposition: ψ ∧ (φ ∨ MRP). Simultaneous with on stepL ψ and stepL φ.
adequacy-met-re : ∀ (table : PredTable) (w s : ℕ) (φ ψ : LTLProc) (y : TimedFrame) (rest : List TimedFrame)
  → Sound (runL table φ (y ∷ rest)) (⟦ denot table φ ⟧ (y ∷ rest))
  → Sound (runL table ψ (y ∷ rest)) (⟦ denot table ψ ⟧ (y ∷ rest))
  → Sound (runL table (MetricReleaseProc w (suc (decodeStart s (timestamp y))) φ ψ) rest)
          (met-re-go w (denot table φ) (denot table ψ) (decodeStart s (timestamp y)) rest)
  → Sound (runL table (MetricReleaseProc w s φ ψ) (y ∷ rest))
          (⟦ denot table (MetricReleaseProc w s φ ψ) ⟧ (y ∷ rest))
adequacy-met-re table w s φ ψ y rest ih-φ ih-ψ ih-MRP
  with (timestamp y ∸ decodeStart s (timestamp y)) ≤ᵇ w
... | false = sound-tt
... | true with stepL table ψ y | stepL table φ y
...   | Violated _    | _             = sound-and ih-ψ (sound-or ih-φ ih-MRP)
...   | Satisfied     | Satisfied     = sound-and ih-ψ (sound-or ih-φ ih-MRP)
...   | Satisfied     | Violated _    = sound-and-true-l ih-ψ (sound-or-false-l ih-φ ih-MRP)
...   | Satisfied     | Continue _ φ' = sound-and-true-l ih-ψ
                                          (runL-or-sound table φ' (MetricReleaseProc w (suc (decodeStart s (timestamp y))) φ ψ) rest
                                            (sound-or ih-φ ih-MRP))
...   | Continue _ ψ' | Satisfied     = sound-and-true-r ih-ψ (sound-or ih-φ ih-MRP)
...   | Continue _ ψ' | Violated _    = runL-and-sound table ψ' (MetricReleaseProc w (suc (decodeStart s (timestamp y))) φ ψ) rest
                                          (sound-and ih-ψ (sound-or-false-l ih-φ ih-MRP))
...   | Continue _ ψ' | Continue _ φ' = runL-and-sound table ψ' (Or φ' (MetricReleaseProc w (suc (decodeStart s (timestamp y))) φ ψ)) rest
                                          (sound-and ih-ψ
                                            (runL-or-sound table φ' (MetricReleaseProc w (suc (decodeStart s (timestamp y))) φ ψ) rest
                                              (sound-or ih-φ ih-MRP)))

-- ============================================================================
-- ADEQUACY THEOREM
-- ============================================================================

-- The crown jewel: for any LTLProc and trace, the coalgebra execution (runL)
-- is sound with respect to the denotational semantics (⟦_⟧).
-- Structural induction on LTLProc (outer) + list induction on σ (inner).

adequacy : ∀ (table : PredTable) (proc : LTLProc) (σ : List TimedFrame)
  → Sound (runL table proc σ) (⟦ denot table proc ⟧ σ)

-- Atomic: empty trace
adequacy table (Atomic n) [] = sound-ff

-- Atomic: non-empty trace — case split on table n x
adequacy table (Atomic n) (x ∷ rest) with table n x
... | True    = sound-tt
... | False   = sound-ff
... | Unknown = sound-unk
... | Pending = sound-pen

-- And: decompose runL to ∧TV, then compose with sound-and + IH
adequacy table (And φ ψ) σ rewrite runL-and-decomp table φ ψ σ = sound-and (adequacy table φ σ) (adequacy table ψ σ)

-- Or: decompose runL to ∨TV, then compose with sound-or + IH
adequacy table (Or φ ψ) σ rewrite runL-or-decomp table φ ψ σ = sound-or (adequacy table φ σ) (adequacy table ψ σ)

-- Next: empty → sound-ff; non-empty → IH on tail
adequacy table (Next φ) [] = sound-ff
adequacy table (Next φ) (x ∷ rest) = adequacy table φ rest

-- Always: empty → sound-tt (vacuous); non-empty → decompose + sound-and + IH
-- Uses subst (not rewrite) to avoid with-generated auxiliary that confuses termination checker.
adequacy table (Always φ) [] = sound-tt
adequacy table (Always φ) (x ∷ rest) =
  subst (λ m → Sound m (⟦ denot table φ ⟧ (x ∷ rest) ∧TV ⟦ Syntax.Always (denot table φ) ⟧ rest))
        (sym (runL-always-decomp table φ x rest))
        (sound-and (adequacy table φ (x ∷ rest)) (adequacy table (Always φ) rest))

-- Eventually: empty → sound-ff; non-empty → decompose + sound-or + IH
adequacy table (Eventually φ) [] = sound-ff
adequacy table (Eventually φ) (x ∷ rest) =
  subst (λ m → Sound m (⟦ denot table φ ⟧ (x ∷ rest) ∨TV ⟦ Syntax.Eventually (denot table φ) ⟧ rest))
        (sym (runL-eventually-decomp table φ x rest))
        (sound-or (adequacy table φ (x ∷ rest)) (adequacy table (Eventually φ) rest))

-- Until: empty → sound-ff; non-empty → ψ ∨ (φ ∧ Until), subst on monitor
adequacy table (Until φ ψ) [] = sound-ff
adequacy table (Until φ ψ) (x ∷ rest) =
  subst (λ m → Sound m (⟦ denot table ψ ⟧ (x ∷ rest)
                          ∨TV (⟦ denot table φ ⟧ (x ∷ rest)
                               ∧TV ⟦ Syntax.Until (denot table φ) (denot table ψ) ⟧ rest)))
        (sym (runL-until-decomp table φ ψ x rest))
        (sound-or (adequacy table ψ (x ∷ rest))
                  (sound-and (adequacy table φ (x ∷ rest))
                             (adequacy table (Until φ ψ) rest)))

-- Release: empty → sound-tt; non-empty → ψ ∧ (φ ∨ Release), subst on monitor
adequacy table (Release φ ψ) [] = sound-tt
adequacy table (Release φ ψ) (x ∷ rest) =
  subst (λ m → Sound m (⟦ denot table ψ ⟧ (x ∷ rest)
                          ∧TV (⟦ denot table φ ⟧ (x ∷ rest)
                               ∨TV ⟦ Syntax.Release (denot table φ) (denot table ψ) ⟧ rest)))
        (sym (runL-release-decomp table φ ψ x rest))
        (sound-and (adequacy table ψ (x ∷ rest))
                   (sound-or (adequacy table φ (x ∷ rest))
                             (adequacy table (Release φ ψ) rest)))

-- MetricEventually: delegate to non-recursive helper (zero `with`s here)
adequacy table (MetricEventuallyProc w s φ) [] = sound-ff
adequacy table (MetricEventuallyProc w s φ) (y ∷ rest) =
  adequacy-met-ev table w s φ y rest
    (adequacy table φ (y ∷ rest))
    (met-ev-go-sound w (denot table φ) (decodeStart s (timestamp y)) rest
      (adequacy table (MetricEventuallyProc w (suc (decodeStart s (timestamp y))) φ) rest))

-- MetricAlways: delegate to non-recursive helper (zero `with`s here)
adequacy table (MetricAlwaysProc w s φ) [] = sound-tt
adequacy table (MetricAlwaysProc w s φ) (y ∷ rest) =
  adequacy-met-al table w s φ y rest
    (adequacy table φ (y ∷ rest))
    (met-al-go-sound w (denot table φ) (decodeStart s (timestamp y)) rest
      (adequacy table (MetricAlwaysProc w (suc (decodeStart s (timestamp y))) φ) rest))

-- MetricUntil: delegate to non-recursive helper (zero `with`s here)
adequacy table (MetricUntilProc w s φ ψ) [] = sound-ff
adequacy table (MetricUntilProc w s φ ψ) (y ∷ rest) =
  adequacy-met-un table w s φ ψ y rest
    (adequacy table φ (y ∷ rest))
    (adequacy table ψ (y ∷ rest))
    (met-un-go-sound w (denot table φ) (denot table ψ) (decodeStart s (timestamp y)) rest
      (adequacy table (MetricUntilProc w (suc (decodeStart s (timestamp y))) φ ψ) rest))

-- MetricRelease: delegate to non-recursive helper (zero `with`s here)
adequacy table (MetricReleaseProc w s φ ψ) [] = sound-tt
adequacy table (MetricReleaseProc w s φ ψ) (y ∷ rest) =
  adequacy-met-re table w s φ ψ y rest
    (adequacy table φ (y ∷ rest))
    (adequacy table ψ (y ∷ rest))
    (met-re-go-sound w (denot table φ) (denot table ψ) (decodeStart s (timestamp y)) rest
      (adequacy table (MetricReleaseProc w (suc (decodeStart s (timestamp y))) φ ψ) rest))

-- Not: decompose runL to notTV, then compose with sound-not + IH
adequacy table (Not φ) σ rewrite runL-not-decomp table φ σ = sound-not (adequacy table φ σ)
