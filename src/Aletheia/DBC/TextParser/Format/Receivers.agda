{-# OPTIONS --safe --without-K #-}

-- B.3.d Layer 3 3d.5.c-γ.1 — DSL-side `canonicalReceiversFmt`.
--
-- Companion to `Aletheia.DBC.CanonicalReceivers` (which hosts the
-- refinement carrier upstream of `Types.agda`).  This module adds the
-- Format DSL extension: a `Format CanonicalReceivers` whose universal
-- `roundtrip` discharges `parse f pos (emit f x ++ suffix) ≡ just …`
-- via the iso bijection law alone.
--
-- Compositional structure:
--   `pair ident (many (withPrefix "," ident))` : Format (Identifier × List Identifier)
--   ↓ iso fwd bwd bijection
--   Format CanonicalReceivers
--
-- The iso bijection law `(∀ b → fwd (bwd b) ≡ b)` closes via three cases:
--   * empty AST: `bwd` returns `(vectorXXX-id , [])`; `fwd` evaluates
--     `T? (isVectorXXXᵇ vectorXXX-id)` = yes (via `≡csᵇ-refl-eq`),
--     yielding back `mkCanonical [] tt`.
--   * singleton AST `(r ∷ [])` with witness `wit : T (not (isVectorXXXᵇ r))`:
--     `bwd` returns `(r , [])`; `fwd`'s case-split on `T? (isVectorXXXᵇ r)`
--     refutes the `yes` branch via `T-not-and-T wit`, the `no` branch
--     yields `mkCanonical (r ∷ []) (¬T→T-not ¬p)`, equal to the input
--     up to `T-irrelevant`.
--   * length≥2 AST: bwd returns the verbatim head/tail split, fwd
--     reassembles via the second clause; both sides definitionally
--     equal (canonicalᵇ for length≥2 is unconditionally `true`, so
--     witnesses are `tt : ⊤`).
module Aletheia.DBC.TextParser.Format.Receivers where

open import Data.Bool using (Bool; true; false; T; not)
open import Data.Bool.Properties using (T?; T-irrelevant)
open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; subst)
open import Relation.Nullary using (yes; no)

open import Aletheia.DBC.Identifier
  using (Identifier; _≡csᵇ_; ≡csᵇ-refl-eq)
open import Aletheia.DBC.CanonicalReceivers
  using (CanonicalReceivers; mkCanonical;
         vectorXXX-name; vectorXXX-id;
         isVectorXXXᵇ; isCanonicalReceiversᵇ;
         ¬T→T-not; T-not-and-T; mkCanonicalFromList)

open import Aletheia.DBC.TextParser.Format
  using (Format; ident; pair; many; iso; withPrefix)

-- ============================================================================
-- WIRE → CANONICAL ISO
-- ============================================================================

private
  -- Forward: classify the wire-format pair `(h , t)` as a canonical AST.
  -- Reuses `mkCanonicalFromList` on the consed list, so the strip rule
  -- lives in one place (`CanonicalReceivers.mkCanonicalFromList`).
  fwd : Identifier × List Identifier → CanonicalReceivers
  fwd (h , t) = mkCanonicalFromList (h ∷ t)

  -- Backward: encode the canonical AST as a wire-format pair.  Empty
  -- AST goes to the `vectorXXX-id` placeholder; singleton/multi cases
  -- project the head/tail.
  bwd : CanonicalReceivers → Identifier × List Identifier
  bwd (mkCanonical []             _) = vectorXXX-id , []
  bwd (mkCanonical (r ∷ [])       _) = r , []
  bwd (mkCanonical (r ∷ s ∷ rest) _) = r , s ∷ rest

  -- Bijection law.  Three cases mirror `bwd`:
  --   * empty: `fwd (vectorXXX-id , [])` enters the `yes` branch
  --     because `isVectorXXXᵇ vectorXXX-id` reduces to
  --     `vectorXXX-name ≡csᵇ vectorXXX-name`, which is `true` by
  --     `≡csᵇ-refl-eq`.  Both sides become `mkCanonical [] tt`.
  --   * singleton: the input's `wit : T (not (isVectorXXXᵇ r))` refutes
  --     the `yes` branch via `T-not-and-T`, leaving the `no` branch.
  --     T-irrelevant collapses the synthesised witness to the user's.
  --   * length≥2: `mkCanonical` witness slot is `T true = ⊤`,
  --     uniquely inhabited by `tt`; both sides are `mkCanonical … tt`.
  fwd-bwd : ∀ b → fwd (bwd b) ≡ b
  fwd-bwd (mkCanonical [] _) with T? (isVectorXXXᵇ vectorXXX-id)
  ... | yes _   = refl
  ... | no  ¬wit = ⊥-elim (¬wit (subst T (sym (≡csᵇ-refl-eq vectorXXX-name)) tt))
  fwd-bwd (mkCanonical (r ∷ []) wit) with T? (isVectorXXXᵇ r)
  ... | yes p   = ⊥-elim (T-not-and-T wit p)
  ... | no  ¬p  = cong (mkCanonical (r ∷ []))
                       (T-irrelevant (¬T→T-not ¬p) wit)
  fwd-bwd (mkCanonical (r ∷ s ∷ rest) _) = refl

-- ============================================================================
-- CANONICAL RECEIVERS FORMAT
-- ============================================================================

-- Wire: one-or-more comma-separated identifiers.  AST: refined list with
-- the singleton-Vector__XXX placeholder stripped to `[]` and the
-- canonical witness extracted at parse time.  The universal `roundtrip`
-- theorem in `Format` discharges the parse-after-emit law for this
-- format with a single call backed by the iso's bijection equation.
canonicalReceiversFmt : Format CanonicalReceivers
canonicalReceiversFmt =
  iso fwd bwd fwd-bwd
      (pair ident (many (withPrefix (',' ∷ []) ident)))
