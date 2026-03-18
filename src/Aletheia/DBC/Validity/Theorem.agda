{-# OPTIONS --safe --without-K #-}

-- Top-level soundness and completeness theorems for DBC validation.
--
-- soundness   : errorIssues (validateDBCFull dbc) ≡ [] → ValidDBC dbc
-- completeness : ValidDBC dbc → errorIssues (validateDBCFull dbc) ≡ []
--
-- Together these establish: the validator reports no errors if and only if
-- the DBC satisfies all 9 formal validity conditions.
module Aletheia.DBC.Validity.Theorem where

open import Aletheia.DBC.Types using (DBC)
open import Aletheia.DBC.Validator using (errorIssues; validateDBCFull; checkDuplicateMessageIds; checkAllDuplicateSignalNames; checkAllFactorZero; checkAllMuxFound; checkAllMuxAlwaysPresent; checkAllGlobalNameCollisions; checkAllMinMax; checkAllSignalExceedsDLC; checkAllSignalOverlaps; checkAllBitLengthZero; checkDuplicateMessageNames; checkAllDLCOutOfRange; checkAllOffsetScaleRange; checkAllEmptyMessage; checkAllStartBitOutOfRange; checkAllBitLengthExcessive)
open import Aletheia.DBC.Validity using (ValidDBC)
open import Aletheia.DBC.Validity.Composition using (ei-split; ei-combine; ei-from-≡[]; errorIssues-allE-nil; errorIssues-allW; checkDuplicateMessageIds-allE; checkAllDuplicateSignalNames-allE; checkAllFactorZero-allE; checkAllMuxFound-allE; checkAllMuxAlwaysPresent-allE; checkAllSignalExceedsDLC-allE; checkAllSignalOverlaps-allE; checkAllBitLengthZero-allE; checkAllDLCOutOfRange-allE)
open import Aletheia.DBC.Validity.ErrorChecks using (checkDuplicateMessageIds-sound; checkDuplicateMessageIds-complete; checkAllDuplicateSignalNames-sound; checkAllDuplicateSignalNames-complete; checkAllFactorZero-sound; checkAllFactorZero-complete; checkAllMuxFound-sound; checkAllMuxFound-complete; checkAllMuxAlwaysPresent-sound; checkAllMuxAlwaysPresent-complete; checkAllSignalExceedsDLC-sound; checkAllSignalExceedsDLC-complete; checkAllSignalOverlaps-sound; checkAllSignalOverlaps-complete; checkAllBitLengthZero-sound; checkAllBitLengthZero-complete; checkAllDLCOutOfRange-sound; checkAllDLCOutOfRange-complete)
open import Aletheia.DBC.Validity.WarningChecks using (checkAllGlobalNameCollisions-allW; checkAllMinMax-allW; checkDuplicateMessageNames-allW; checkAllOffsetScaleRange-allW; checkAllEmptyMessage-allW; checkAllStartBitOutOfRange-allW; checkAllBitLengthExcessive-allW)
open import Data.List using (List; []) renaming (_++_ to _++ₗ_)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- ============================================================================
-- SOUNDNESS: no errors reported ⟹ DBC is valid
-- ============================================================================

soundness : ∀ dbc → errorIssues (validateDBCFull dbc) ≡ [] → ValidDBC dbc
soundness dbc eq₀ = record
  { uniqueIds        = checkDuplicateMessageIds-sound msgs
      (errorIssues-allE-nil _ (checkDuplicateMessageIds-allE msgs) (proj₁ s₁))
  ; uniqueSigNames   = checkAllDuplicateSignalNames-sound msgs
      (errorIssues-allE-nil _ (checkAllDuplicateSignalNames-allE msgs) (proj₁ s₂))
  ; nonZeroFactors   = checkAllFactorZero-sound msgs
      (errorIssues-allE-nil _ (checkAllFactorZero-allE msgs) (proj₁ s₃))
  ; muxExist         = checkAllMuxFound-sound msgs
      (errorIssues-allE-nil _ (checkAllMuxFound-allE msgs) (proj₁ s₄))
  ; muxAlwaysPresent = checkAllMuxAlwaysPresent-sound msgs
      (errorIssues-allE-nil _ (checkAllMuxAlwaysPresent-allE msgs) (proj₁ s₅))
  ; bitsInFrame      = checkAllSignalExceedsDLC-sound msgs
      (errorIssues-allE-nil _ (checkAllSignalExceedsDLC-allE msgs) (proj₁ s₈))
  ; sigPairsValid    = checkAllSignalOverlaps-sound msgs
      (errorIssues-allE-nil _ (checkAllSignalOverlaps-allE msgs) (proj₁ s₉))
  ; nonZeroBitLengths = checkAllBitLengthZero-sound msgs
      (errorIssues-allE-nil _ (checkAllBitLengthZero-allE msgs) (proj₁ s₁₀))
  ; validDLCs        = checkAllDLCOutOfRange-sound msgs
      (errorIssues-allE-nil _ (checkAllDLCOutOfRange-allE msgs) (proj₁ s₁₂))
  }
  where
    msgs = DBC.messages dbc
    s₁  = ei-split (checkDuplicateMessageIds msgs) _ eq₀
    s₂  = ei-split (checkAllDuplicateSignalNames msgs) _ (proj₂ s₁)
    s₃  = ei-split (checkAllFactorZero msgs) _ (proj₂ s₂)
    s₄  = ei-split (checkAllMuxFound msgs) _ (proj₂ s₃)
    s₅  = ei-split (checkAllMuxAlwaysPresent msgs) _ (proj₂ s₄)
    s₆  = ei-split (checkAllGlobalNameCollisions msgs) _ (proj₂ s₅)
    s₇  = ei-split (checkAllMinMax msgs) _ (proj₂ s₆)
    s₈  = ei-split (checkAllSignalExceedsDLC msgs) _ (proj₂ s₇)
    s₉  = ei-split (checkAllSignalOverlaps msgs) _ (proj₂ s₈)
    s₁₀ = ei-split (checkAllBitLengthZero msgs) _ (proj₂ s₉)
    s₁₁ = ei-split (checkDuplicateMessageNames msgs) _ (proj₂ s₁₀)
    s₁₂ = ei-split (checkAllDLCOutOfRange msgs) _ (proj₂ s₁₁)

-- ============================================================================
-- COMPLETENESS: DBC is valid ⟹ no errors reported
-- ============================================================================

completeness : ∀ dbc → ValidDBC dbc → errorIssues (validateDBCFull dbc) ≡ []
completeness dbc v =
  ei-combine (checkDuplicateMessageIds msgs) _
    (ei-from-≡[] _ (checkDuplicateMessageIds-complete msgs (ValidDBC.uniqueIds v)))
  (ei-combine (checkAllDuplicateSignalNames msgs) _
    (ei-from-≡[] _ (checkAllDuplicateSignalNames-complete msgs (ValidDBC.uniqueSigNames v)))
  (ei-combine (checkAllFactorZero msgs) _
    (ei-from-≡[] _ (checkAllFactorZero-complete msgs (ValidDBC.nonZeroFactors v)))
  (ei-combine (checkAllMuxFound msgs) _
    (ei-from-≡[] _ (checkAllMuxFound-complete msgs (ValidDBC.muxExist v)))
  (ei-combine (checkAllMuxAlwaysPresent msgs) _
    (ei-from-≡[] _ (checkAllMuxAlwaysPresent-complete msgs (ValidDBC.muxAlwaysPresent v)))
  (ei-combine (checkAllGlobalNameCollisions msgs) _
    (errorIssues-allW _ (checkAllGlobalNameCollisions-allW msgs))
  (ei-combine (checkAllMinMax msgs) _
    (errorIssues-allW _ (checkAllMinMax-allW msgs))
  (ei-combine (checkAllSignalExceedsDLC msgs) _
    (ei-from-≡[] _ (checkAllSignalExceedsDLC-complete msgs (ValidDBC.bitsInFrame v)))
  (ei-combine (checkAllSignalOverlaps msgs) _
    (ei-from-≡[] _ (checkAllSignalOverlaps-complete msgs (ValidDBC.sigPairsValid v)))
  (ei-combine (checkAllBitLengthZero msgs) _
    (ei-from-≡[] _ (checkAllBitLengthZero-complete msgs (ValidDBC.nonZeroBitLengths v)))
  (ei-combine (checkDuplicateMessageNames msgs) _
    (errorIssues-allW _ (checkDuplicateMessageNames-allW msgs))
  (ei-combine (checkAllDLCOutOfRange msgs) _
    (ei-from-≡[] _ (checkAllDLCOutOfRange-complete msgs (ValidDBC.validDLCs v)))
  (ei-combine (checkAllOffsetScaleRange msgs) _
    (errorIssues-allW _ (checkAllOffsetScaleRange-allW msgs))
  (ei-combine (checkAllEmptyMessage msgs) _
    (errorIssues-allW _ (checkAllEmptyMessage-allW msgs))
  (ei-combine (checkAllStartBitOutOfRange msgs) _
    (errorIssues-allW _ (checkAllStartBitOutOfRange-allW msgs))
    (errorIssues-allW _ (checkAllBitLengthExcessive-allW msgs))
  ))))))))))))))
  where
    msgs = DBC.messages dbc
