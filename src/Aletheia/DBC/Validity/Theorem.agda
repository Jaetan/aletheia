{-# OPTIONS --safe --without-K #-}

-- Top-level soundness and completeness theorems for DBC validation.
--
-- soundness   : errorIssues (validateDBCFull dbc) ≡ [] → ValidDBC dbc
-- completeness : ValidDBC dbc → errorIssues (validateDBCFull dbc) ≡ []
--
-- Together these establish: the validator reports no errors if and only if
-- the DBC satisfies all 8 formal validity conditions.
module Aletheia.DBC.Validity.Theorem where

open import Aletheia.DBC.Types using (DBC)
open import Aletheia.DBC.Validator using
  ( errorIssues; validateDBCFull
  ; checkDuplicateMessageIds; checkAllDuplicateSignalNames
  ; checkAllFactorZero; checkAllMuxFound; checkAllMuxCycle
  ; checkAllMuxScaling; checkAllGlobalNameCollisions; checkAllMinMax
  ; checkAllSignalExceedsDLC; checkAllSignalOverlaps
  ; checkAllBitLengthZero; checkDuplicateMessageNames
  ; checkAllOffsetScaleRange
  ; checkAllEmptyMessage; checkAllStartBitOutOfRange
  ; checkAllBitLengthExcessive
  ; checkDuplicateAttributeNames; checkAllUnknownCommentTargets
  ; checkAllUnknownMessageSenders
  )
open import Aletheia.DBC.Validity using (ValidDBC)
open import Aletheia.DBC.Validity.Composition using
  ( ei-split; ei-combine; ei-from-≡[]; errorIssues-allE-nil
  ; errorIssues-allW
  ; checkDuplicateMessageIds-allE; checkAllDuplicateSignalNames-allE
  ; checkAllFactorZero-allE; checkAllMuxFound-allE
  ; checkAllMuxCycle-allE; checkAllSignalExceedsDLC-allE
  ; checkAllSignalOverlaps-allE; checkAllBitLengthZero-allE
  )
open import Aletheia.DBC.Validity.ErrorChecks using
  ( checkDuplicateMessageIds-sound; checkDuplicateMessageIds-complete
  ; checkAllDuplicateSignalNames-sound
  ; checkAllDuplicateSignalNames-complete
  ; checkAllFactorZero-sound; checkAllFactorZero-complete
  ; checkAllMuxFound-sound; checkAllMuxFound-complete
  ; checkAllMuxCycle-sound
  ; checkAllMuxCycle-complete
  ; checkAllSignalExceedsDLC-sound; checkAllSignalExceedsDLC-complete
  ; checkAllSignalOverlaps-sound; checkAllSignalOverlaps-complete
  ; checkAllBitLengthZero-sound; checkAllBitLengthZero-complete
  )
open import Aletheia.DBC.Validity.WarningChecks using
  ( checkAllMuxScaling-allW; checkAllGlobalNameCollisions-allW
  ; checkAllMinMax-allW; checkDuplicateMessageNames-allW
  ; checkAllOffsetScaleRange-allW; checkAllEmptyMessage-allW
  ; checkAllStartBitOutOfRange-allW; checkAllBitLengthExcessive-allW
  ; checkDuplicateAttributeNames-allW; checkAllUnknownCommentTargets-allW
  ; checkAllUnknownMessageSenders-allW
  )
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
  ; muxAcyclic       = checkAllMuxCycle-sound msgs
      (errorIssues-allE-nil _ (checkAllMuxCycle-allE msgs) (proj₁ s₅))
  ; bitsInFrame      = checkAllSignalExceedsDLC-sound msgs
      (errorIssues-allE-nil _ (checkAllSignalExceedsDLC-allE msgs) (proj₁ s₈))
  ; sigPairsValid    = checkAllSignalOverlaps-sound msgs
      (errorIssues-allE-nil _ (checkAllSignalOverlaps-allE msgs) (proj₁ s₉))
  ; nonZeroBitLengths = checkAllBitLengthZero-sound msgs
      (errorIssues-allE-nil _ (checkAllBitLengthZero-allE msgs) (proj₁ s₁₀))
  }
  where
    msgs = DBC.messages dbc
    s₁  = ei-split (checkDuplicateMessageIds msgs) _ eq₀
    s₂  = ei-split (checkAllDuplicateSignalNames msgs) _ (proj₂ s₁)
    s₃  = ei-split (checkAllFactorZero msgs) _ (proj₂ s₂)
    s₄  = ei-split (checkAllMuxFound msgs) _ (proj₂ s₃)
    s₅  = ei-split (checkAllMuxCycle msgs) _ (proj₂ s₄)
    s₅b = ei-split (checkAllMuxScaling msgs) _ (proj₂ s₅)
    s₆  = ei-split (checkAllGlobalNameCollisions msgs) _ (proj₂ s₅b)
    s₇  = ei-split (checkAllMinMax msgs) _ (proj₂ s₆)
    s₈  = ei-split (checkAllSignalExceedsDLC msgs) _ (proj₂ s₇)
    s₉  = ei-split (checkAllSignalOverlaps msgs) _ (proj₂ s₈)
    s₁₀ = ei-split (checkAllBitLengthZero msgs) _ (proj₂ s₉)

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
  (ei-combine (checkAllMuxCycle msgs) _
    (ei-from-≡[] _ (checkAllMuxCycle-complete msgs (ValidDBC.muxAcyclic v)))
  (ei-combine (checkAllMuxScaling msgs) _
    (errorIssues-allW _ (checkAllMuxScaling-allW msgs))
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
  (ei-combine (checkAllOffsetScaleRange msgs) _
    (errorIssues-allW _ (checkAllOffsetScaleRange-allW msgs))
  (ei-combine (checkAllEmptyMessage msgs) _
    (errorIssues-allW _ (checkAllEmptyMessage-allW msgs))
  (ei-combine (checkAllStartBitOutOfRange msgs) _
    (errorIssues-allW _ (checkAllStartBitOutOfRange-allW msgs))
  (ei-combine (checkAllBitLengthExcessive msgs) _
    (errorIssues-allW _ (checkAllBitLengthExcessive-allW msgs))
  (ei-combine (checkDuplicateAttributeNames attrs) _
    (errorIssues-allW _ (checkDuplicateAttributeNames-allW attrs))
  (ei-combine (checkAllUnknownCommentTargets msgs nodes envVars cmts) _
    (errorIssues-allW _ (checkAllUnknownCommentTargets-allW msgs nodes envVars cmts))
    (errorIssues-allW _ (checkAllUnknownMessageSenders-allW msgs nodes))
  )))))))))))))))))
  where
    msgs    = DBC.messages dbc
    nodes   = DBC.nodes dbc
    envVars = DBC.environmentVars dbc
    cmts    = DBC.comments dbc
    attrs   = DBC.attributes dbc
