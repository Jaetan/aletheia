{-# OPTIONS --safe --without-K #-}

-- Properties of the LTL coalgebra initialization.
--
-- Purpose: Prove initProc produces the correct initial state for denot.
-- Key theorem: initProc-correct — denot table (initProc φ) ≡ mapLTL table φ
--
-- This closes a gap in the adequacy chain: the adequacy theorem takes proc
-- as a parameter, but production code uses initProc to create proc.
-- Without this proof, adequacy could be vacuously sound for a wrong initial state.
module Aletheia.LTL.Coalgebra.Properties where

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Aletheia.LTL.Syntax using (LTL; mapLTL)
open import Aletheia.LTL.Coalgebra using (PredTable; initProc; denot)

-- initProc correctly initializes the LTL process state:
-- denot recovers the intended formula (atoms mapped through PredTable).
--
-- Since LTLProc = LTL ℕ, initProc is identity, and denot = mapLTL table.
-- The equality holds by reflexivity.
initProc-correct : ∀ (table : PredTable) (φ : LTL ℕ)
  → denot table (initProc φ) ≡ mapLTL table φ
initProc-correct table φ = refl
