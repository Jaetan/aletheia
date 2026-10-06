-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- The loader's verdict on a DBC within its size bounds: every issue the
-- validator reports when one is an error, otherwise the DBC as a `ValidDBC`,
-- with the proof that it is valid, and the warnings.  The proof is the
-- validity theorem's (`Aletheia.DBC.Validity.Theorem.soundness`), erased;
-- this module runs the validator once and hands the theorem its premises,
-- the bound proof the `BoundedDBC` carries and the validator's clean verdict.
module Aletheia.DBC.Validated where

open import Aletheia.DBC.Types using (ValidationIssue)
open import Aletheia.DBC.Bounds using (BoundedDBC; bounded)
open import Aletheia.DBC.Validator using (validateDBCFull; hasAnyError; warningIssues)
open import Aletheia.DBC.Validity using (ValidDBC; validated)
open import Aletheia.DBC.Validity.Composition using (noError-errorIssues)
open import Aletheia.DBC.Validity.Theorem using (soundness)
open import Data.Bool using (true; false)
open import Data.List using (List)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)

validate : BoundedDBC → List ValidationIssue ⊎ (ValidDBC × List ValidationIssue)
validate (bounded dbc b) = settle (validateDBCFull dbc) refl
  where
    settle : (issues : List ValidationIssue) → @0 validateDBCFull dbc ≡ issues
           → List ValidationIssue ⊎ (ValidDBC × List ValidationIssue)
    settle issues same with hasAnyError issues in clean
    ... | true  = inj₁ issues
    ... | false =
      inj₂ ( validated dbc (soundness dbc b (noError-errorIssues (validateDBCFull dbc) (trans (cong hasAnyError same) clean)))
           , warningIssues issues )
