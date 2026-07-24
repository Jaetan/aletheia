-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Erased-proof decidables for hot-path predicates.
--
-- Purpose: a `Dec₀ P` carries a runtime Bool (`does₀`) together with an
--   ERASED certificate (`@0 proof₀ : Reflects P does₀`).  MAlonzo compiles
--   the record to a GHC newtype over Bool (the erased field vanishes), so a
--   `Dec₀`-valued predicate costs exactly what its bare-Bool fast path costs
--   — while the erasure checker mechanically enforces that the Bool and its
--   meaning can never drift apart.  This replaces the convention of pairing
--   a Bool fast path with a free-floating equivalence lemma.
--
-- Construction discipline (empirically pinned; see DEFERRED_ITEMS §C.2
-- provenance): build `Dec₀` values from Bool PRIMITIVES (`_≡ᵇ_` / `_≤ᵇ_`
-- style) via `fromBridges` / `dec₀` — NEVER by wrapping a stock stdlib
-- decider, which would allocate the full relevant `Dec` upstream and lose
-- the zero-cost property.
--
-- Consumption discipline: the certificate is erased, so it can only be used
-- in erased positions (`@0` argument slots, other erased fields, proofs
-- inside `@0` context).  A consumer that needs a RELEVANT witness must
-- re-decide relevantly (`recompute₀` bridges an erased witness back through
-- a relevant decider).  Cold verification paths that feed soundness lemmas
-- keep stock relevant `Dec` — erasure and lemma-consumption are mutually
-- exclusive uses of one proof.
module Aletheia.Data.Dec0 where

open import Data.Bool using (Bool; true; false; T; _∧_; _∨_; not)
open import Data.Empty using (⊥)
open import Data.Unit using (tt)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_)
open import Level using (Level)
open import Relation.Nullary.Decidable.Core using (Dec; yes; no)
open import Relation.Nullary.Negation.Core using (¬_)
open import Relation.Nullary.Reflects using
  (Reflects; ofʸ; ofⁿ; invert; fromEquivalence; _⊎-reflects_)

private
  variable
    p q : Level
    P : Set p
    Q : Set q

-- ============================================================================
-- THE RECORD
-- ============================================================================

-- MAlonzo shape: one relevant field → GHC newtype over Bool (pinned by the
-- Shakefile `check-erasure` gate).
record Dec₀ {p} (P : Set p) : Set p where
  constructor _because₀_
  field
    does₀     : Bool
    @0 proof₀ : Reflects P does₀

open Dec₀ public using (does₀; proof₀)

-- ============================================================================
-- CONSTRUCTION (from Bool primitives)
-- ============================================================================

-- Build from the two `T`-bridges of a Bool primitive — the standard shape
-- for `_≡ᵇ_` / `_≤ᵇ_`-style predicates whose stdlib bridges are
-- `≡ᵇ⇒≡` / `≡⇒≡ᵇ` (and friends).
fromBridges : (b : Bool) → @0 (T b → P) → @0 (P → T b) → Dec₀ P
fromBridges b sound complete = b because₀ fromEquivalence sound complete

-- Build from an already-erased Reflects (e.g. a stdlib `≤ᵇ-reflects-≤`
-- applied in erased context).
dec₀ : (b : Bool) → @0 Reflects P b → Dec₀ P
dec₀ b r = b because₀ r

-- ============================================================================
-- ERASED-WITNESS RESURRECTION
-- ============================================================================

private
  -- The erased-absurd trick: an erased ⊥ still eliminates, because the
  -- absurd match has no clauses to compile.
  absurd₀ : ∀ {a} {A : Set a} → @0 ⊥ → A
  absurd₀ ()

-- Resurrect an erased witness through a RELEVANT decider: when a consumer
-- holds `@0 P` but needs `P`, a relevant `Dec P` re-decides; the erased
-- witness rules out the `no` branch.  (stdlib `recompute` wants a
-- dot-irrelevant argument and rejects `@0` — this is the `@0` twin.)
recompute₀ : Dec P → @0 P → P
recompute₀ (yes a) _  = a
recompute₀ (no ¬a) a₀ = absurd₀ (¬a a₀)

-- ============================================================================
-- COMBINATORS
-- ============================================================================

-- Map through a proposition isomorphism (both directions needed to carry the
-- Reflects certificate; runtime shape unchanged — the Bool passes through).
map₀ : ∀ {p q} {P : Set p} {Q : Set q} → @0 (P → Q) → @0 (Q → P) → Dec₀ P → Dec₀ Q
map₀ {P = P} {Q = Q} to from (b because₀ r) = b because₀ helper b r
  where
    @0 helper : ∀ b′ → Reflects P b′ → Reflects Q b′
    helper true  r₁ = ofʸ (to (invert r₁))
    helper false r₁ = ofⁿ (λ q₁ → invert r₁ (from q₁))

-- Certified disjunction: `does₀` is the Bool `_∨_` of the components.
or₀ : Dec₀ P → Dec₀ Q → Dec₀ (P ⊎ Q)
or₀ (a because₀ ra) (b because₀ rb) = (a ∨ b) because₀ (ra ⊎-reflects rb)

-- ============================================================================
-- `T`-BRIDGES (structural matches on the implicit Bools — cheaper to
-- elaborate than the stdlib `T-∧` equivalence records; erased use only)
-- ============================================================================

T-∧→ : ∀ {x y : Bool} → T (x ∧ y) → T x × T y
T-∧→ {true} {true} _ = tt , tt

T-∧← : ∀ {x y : Bool} → T x → T y → T (x ∧ y)
T-∧← {true} {true} _ _ = tt

T-not→ : ∀ {x : Bool} → T (not x) → ¬ T x
T-not→ {false} _ ()

T-not← : ∀ {x : Bool} → ¬ T x → T (not x)
T-not← {false} _  = tt
T-not← {true}  ¬t = ¬t tt
