{-# OPTIONS --safe --without-K #-}

-- DecRat refinement types — `IntDecRat` (integer-valued) and
-- `NatDecRat` (non-negative integer-valued).
--
-- Project-wide convention (per `memory/project_decrat_universal_principle.md`):
-- "all numbers are `DecRat` except on the frame hot path".  This module
-- packages the type-level refinements that distinguish integer-bounded
-- DBC slots (e.g. `ATInt` min/max bounds, `AVInt` values) from
-- general-rational slots (`ATFloat` bounds, `AVFloat` values).  The
-- runtime integer-ness check happens once — at the parser boundary,
-- when the wire form is decoded — and the proof is then carried as
-- compile-time evidence through the rest of the pipeline.
--
-- Pattern mirrors `Aletheia.DBC.Identifier`'s `Identifier` record
-- (validity field as `T predicateᵇ`).  The validity field is kept
-- relevant (no `.` modality) to match the Identifier post-T3-fix
-- discipline — irrelevant `.canonical`-style fields broke `_≟_` under
-- `--without-K` for Identifier (see `project_identifier_eq_revisit.md`),
-- so we apply the same caution here.
--
-- Underlying invariant on `DecRat = mkDecRat num twoExp fiveExp _`:
--   * `twoExp = 0 ∧ fiveExp = 0`  ⟺  denominator `2^0 · 5^0 = 1`
--                                ⟺  the rational is an integer.
--
--   * `numerator ≥ 0 ∧ twoExp = 0 ∧ fiveExp = 0`
--                                ⟺  the rational is a non-negative
--                                    integer (i.e., a natural number).

module Aletheia.DBC.DecRat.Refinement where

open import Data.Bool using (Bool; true; false; T)
open import Data.Bool.Properties using (T-irrelevant)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Integer using (ℤ; +_; -[1+_])
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; cong₂; subst)

open import Aletheia.DBC.DecRat using (DecRat; mkDecRat; fromℤ; 0ᵈ; 1ᵈ)

-- ============================================================================
-- INTEGER PREDICATE
-- ============================================================================

isIntegerᵇ : DecRat → Bool
isIntegerᵇ (mkDecRat _ zero    zero    _) = true
isIntegerᵇ (mkDecRat _ (suc _) _       _) = false
isIntegerᵇ (mkDecRat _ _       (suc _) _) = false

-- ============================================================================
-- NON-NEGATIVE INTEGER PREDICATE
-- ============================================================================

isNonNegIntegerᵇ : DecRat → Bool
isNonNegIntegerᵇ (mkDecRat (+ _)    zero    zero    _) = true
isNonNegIntegerᵇ (mkDecRat -[1+ _ ] _       _       _) = false
isNonNegIntegerᵇ (mkDecRat _        (suc _) _       _) = false
isNonNegIntegerᵇ (mkDecRat _        _       (suc _) _) = false

-- ============================================================================
-- IntDecRat — integer-valued DecRat
-- ============================================================================

record IntDecRat : Set where
  constructor mkIntDecRat
  field
    value : DecRat
    isInt : T (isIntegerᵇ value)

-- ----------------------------------------------------------------------------
-- ℤ → IntDecRat — smart constructor
-- ----------------------------------------------------------------------------

isIntegerᵇ-fromℤ : ∀ z → isIntegerᵇ (fromℤ z) ≡ true
isIntegerᵇ-fromℤ (+ zero)    = refl
isIntegerᵇ-fromℤ (+ suc _)   = refl
isIntegerᵇ-fromℤ -[1+ _ ]    = refl

mkIntDecRatFromℤ : ℤ → IntDecRat
mkIntDecRatFromℤ z =
  mkIntDecRat (fromℤ z) (subst T (sym (isIntegerᵇ-fromℤ z)) tt)

-- ----------------------------------------------------------------------------
-- IntDecRat → ℤ — projection
-- ----------------------------------------------------------------------------
--
-- Total: the `T (isIntegerᵇ value)` witness rules out non-integer
-- DecRats at the type level (the `(suc _)` cases for `twoExp` /
-- `fiveExp` make `isIntegerᵇ` reduce to `false`, so `T false = ⊥`
-- and the witness can be eliminated with `()`).

intDecRatToℤ : IntDecRat → ℤ
intDecRatToℤ (mkIntDecRat (mkDecRat z zero    zero    _) _) = z
intDecRatToℤ (mkIntDecRat (mkDecRat _ zero    (suc _) _) ())
intDecRatToℤ (mkIntDecRat (mkDecRat _ (suc _) _       _) ())

-- ----------------------------------------------------------------------------
-- Roundtrips
-- ----------------------------------------------------------------------------

intDecRatToℤ-mkIntDecRatFromℤ : ∀ z → intDecRatToℤ (mkIntDecRatFromℤ z) ≡ z
intDecRatToℤ-mkIntDecRatFromℤ (+ zero)    = refl
intDecRatToℤ-mkIntDecRatFromℤ (+ suc _)   = refl
intDecRatToℤ-mkIntDecRatFromℤ -[1+ _ ]    = refl

-- Other direction: IntDecRat → ℤ → IntDecRat recovers the original
-- record value.  Needs `T-irrelevant` to discharge the witness slot
-- (two `T true` proofs are propositionally equal).  The DecRat slot
-- closes definitionally because `DecRat.canonical` is irrelevant —
-- `mkDecRat z 0 0 c₁` and `mkDecRat z 0 0 c₂` (the latter from
-- `fromℤ z`) are syntactically identical up to irrelevant arguments.
mkIntDecRatFromℤ-intDecRatToℤ : ∀ v → mkIntDecRatFromℤ (intDecRatToℤ v) ≡ v
mkIntDecRatFromℤ-intDecRatToℤ
  (mkIntDecRat (mkDecRat (+ zero)    zero    zero    _) wf) =
  cong (mkIntDecRat _) (T-irrelevant _ wf)
mkIntDecRatFromℤ-intDecRatToℤ
  (mkIntDecRat (mkDecRat (+ suc _)   zero    zero    _) wf) =
  cong (mkIntDecRat _) (T-irrelevant _ wf)
mkIntDecRatFromℤ-intDecRatToℤ
  (mkIntDecRat (mkDecRat -[1+ _ ]    zero    zero    _) wf) =
  cong (mkIntDecRat _) (T-irrelevant _ wf)
mkIntDecRatFromℤ-intDecRatToℤ
  (mkIntDecRat (mkDecRat _           zero    (suc _) _) ())
mkIntDecRatFromℤ-intDecRatToℤ
  (mkIntDecRat (mkDecRat _           (suc _) _       _) ())

-- ============================================================================
-- NatDecRat — non-negative integer-valued DecRat
-- ============================================================================

record NatDecRat : Set where
  constructor mkNatDecRat
  field
    value : DecRat
    isNat : T (isNonNegIntegerᵇ value)

-- ----------------------------------------------------------------------------
-- ℕ → NatDecRat — smart constructor
-- ----------------------------------------------------------------------------

isNonNegIntegerᵇ-fromℕ : ∀ n → isNonNegIntegerᵇ (fromℤ (+ n)) ≡ true
isNonNegIntegerᵇ-fromℕ zero    = refl
isNonNegIntegerᵇ-fromℕ (suc _) = refl

mkNatDecRatFromℕ : ℕ → NatDecRat
mkNatDecRatFromℕ n =
  mkNatDecRat (fromℤ (+ n)) (subst T (sym (isNonNegIntegerᵇ-fromℕ n)) tt)

-- ----------------------------------------------------------------------------
-- NatDecRat → ℕ — projection
-- ----------------------------------------------------------------------------

natDecRatToℕ : NatDecRat → ℕ
natDecRatToℕ (mkNatDecRat (mkDecRat (+ n)    zero    zero    _) _)  = n
natDecRatToℕ (mkNatDecRat (mkDecRat (+ _)    zero    (suc _) _) ())
natDecRatToℕ (mkNatDecRat (mkDecRat (+ _)    (suc _) _       _) ())
natDecRatToℕ (mkNatDecRat (mkDecRat -[1+ _ ] _       _       _) ())

-- ----------------------------------------------------------------------------
-- Roundtrips
-- ----------------------------------------------------------------------------

natDecRatToℕ-mkNatDecRatFromℕ : ∀ n → natDecRatToℕ (mkNatDecRatFromℕ n) ≡ n
natDecRatToℕ-mkNatDecRatFromℕ zero    = refl
natDecRatToℕ-mkNatDecRatFromℕ (suc _) = refl

mkNatDecRatFromℕ-natDecRatToℕ : ∀ v → mkNatDecRatFromℕ (natDecRatToℕ v) ≡ v
mkNatDecRatFromℕ-natDecRatToℕ
  (mkNatDecRat (mkDecRat (+ zero)    zero    zero    _) wf) =
  cong (mkNatDecRat _) (T-irrelevant _ wf)
mkNatDecRatFromℕ-natDecRatToℕ
  (mkNatDecRat (mkDecRat (+ suc _)   zero    zero    _) wf) =
  cong (mkNatDecRat _) (T-irrelevant _ wf)
mkNatDecRatFromℕ-natDecRatToℕ
  (mkNatDecRat (mkDecRat (+ _)       zero    (suc _) _) ())
mkNatDecRatFromℕ-natDecRatToℕ
  (mkNatDecRat (mkDecRat (+ _)       (suc _) _       _) ())
mkNatDecRatFromℕ-natDecRatToℕ
  (mkNatDecRat (mkDecRat -[1+ _ ]    _       _       _) ())

-- ============================================================================
-- Cross-conversion: NatDecRat → IntDecRat (a ℕ is also a ℤ)
-- ============================================================================

isInt-from-isNat : ∀ d → T (isNonNegIntegerᵇ d) → T (isIntegerᵇ d)
isInt-from-isNat (mkDecRat (+ _)     zero    zero    _) _   = tt
isInt-from-isNat (mkDecRat (+ _)     zero    (suc _) _) ()
isInt-from-isNat (mkDecRat (+ _)     (suc _) _       _) ()
isInt-from-isNat (mkDecRat -[1+ _ ]  _       _       _) ()

natDecRatToIntDecRat : NatDecRat → IntDecRat
natDecRatToIntDecRat (mkNatDecRat d wf) =
  mkIntDecRat d (isInt-from-isNat d wf)
