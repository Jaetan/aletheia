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
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)

open import Aletheia.LTL.Syntax using (LTL; Atomic; Not; And; Or; Next; Always; Eventually; Until; Release; MetricEventually; MetricAlways; MetricUntil; MetricRelease)
open import Aletheia.LTL.Coalgebra using (PredTable; initProc; denot)

-- Functorial map on LTL formulas: replace each atom via f.
mapLTL : ∀ {A B : Set} → (A → B) → LTL A → LTL B
mapLTL f (Atomic a)                = Atomic (f a)
mapLTL f (Not φ)                   = Not (mapLTL f φ)
mapLTL f (And φ ψ)                 = And (mapLTL f φ) (mapLTL f ψ)
mapLTL f (Or φ ψ)                  = Or (mapLTL f φ) (mapLTL f ψ)
mapLTL f (Next φ)                  = Next (mapLTL f φ)
mapLTL f (Always φ)                = Always (mapLTL f φ)
mapLTL f (Eventually φ)            = Eventually (mapLTL f φ)
mapLTL f (Until φ ψ)               = Until (mapLTL f φ) (mapLTL f ψ)
mapLTL f (Release φ ψ)             = Release (mapLTL f φ) (mapLTL f ψ)
mapLTL f (MetricEventually w s φ)       = MetricEventually w s (mapLTL f φ)
mapLTL f (MetricAlways w s φ)           = MetricAlways w s (mapLTL f φ)
mapLTL f (MetricUntil w s φ ψ)         = MetricUntil w s (mapLTL f φ) (mapLTL f ψ)
mapLTL f (MetricRelease w s φ ψ)       = MetricRelease w s (mapLTL f φ) (mapLTL f ψ)

-- initProc correctly initializes the LTL process state:
-- denot recovers the intended formula (atoms mapped through PredTable).
--
-- Combined with adequacy (Sound (runL table proc σ) (⟦ denot table proc ⟧ σ)),
-- this gives: runL table (initProc φ) σ is sound w.r.t. ⟦ mapLTL table φ ⟧ σ.
initProc-correct : ∀ (table : PredTable) (φ : LTL ℕ)
  → denot table (initProc φ) ≡ mapLTL table φ
initProc-correct table (Atomic n)        = refl
initProc-correct table (Not φ)           = cong Not (initProc-correct table φ)
initProc-correct table (And φ ψ)         = cong₂ And (initProc-correct table φ) (initProc-correct table ψ)
initProc-correct table (Or φ ψ)          = cong₂ Or (initProc-correct table φ) (initProc-correct table ψ)
initProc-correct table (Next φ)          = cong Next (initProc-correct table φ)
initProc-correct table (Always φ)        = cong Always (initProc-correct table φ)
initProc-correct table (Eventually φ)    = cong Eventually (initProc-correct table φ)
initProc-correct table (Until φ ψ)       = cong₂ Until (initProc-correct table φ) (initProc-correct table ψ)
initProc-correct table (Release φ ψ)     = cong₂ Release (initProc-correct table φ) (initProc-correct table ψ)
initProc-correct table (MetricEventually w s φ)   = cong (MetricEventually w s) (initProc-correct table φ)
initProc-correct table (MetricAlways w s φ)       = cong (MetricAlways w s) (initProc-correct table φ)
initProc-correct table (MetricUntil w s φ ψ)      = cong₂ (MetricUntil w s) (initProc-correct table φ) (initProc-correct table ψ)
initProc-correct table (MetricRelease w s φ ψ)    = cong₂ (MetricRelease w s) (initProc-correct table φ) (initProc-correct table ψ)
