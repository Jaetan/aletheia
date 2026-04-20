{-# OPTIONS --safe --without-K #-}

-- DBC structural validator: public API.
--
-- Purpose: Re-export check functions and formatting utilities, and compose
-- all 16 checks into the full validateDBCFull entry point.
-- Submodules:
--   Checks     — individual check functions (per-element and lifted)
--   Formatting — hasAnyError, formatIssuesText, errorIssues
-- Role: Used by Protocol.Handlers (validateDBCFull), Validity proofs
--   (individual checks), and Protocol.ResponseFormat (hasAnyError).
module Aletheia.DBC.Validator where

open import Aletheia.DBC.Types using (DBC; ValidationIssue)
open import Data.List using (List) renaming (_++_ to _++ₗ_)

-- ============================================================================
-- RE-EXPORTS
-- ============================================================================

open import Aletheia.DBC.Validator.Checks public
open import Aletheia.DBC.Validator.Formatting public

-- ============================================================================
-- FULL VALIDATOR
-- ============================================================================

validateDBCFull : DBC → List ValidationIssue
validateDBCFull dbc =
  let msgs    = DBC.messages dbc
      nodes   = DBC.nodes dbc
      envVars = DBC.environmentVars dbc
      cmts    = DBC.comments dbc
      attrs   = DBC.attributes dbc
  in checkDuplicateMessageIds msgs
     ++ₗ checkAllDuplicateSignalNames msgs
     ++ₗ checkAllFactorZero msgs
     ++ₗ checkAllMuxFound msgs
     ++ₗ checkAllMuxCycle msgs
     ++ₗ checkAllMuxScaling msgs
     ++ₗ checkAllGlobalNameCollisions msgs
     ++ₗ checkAllMinMax msgs
     ++ₗ checkAllSignalExceedsDLC msgs
     ++ₗ checkAllSignalOverlaps msgs
     ++ₗ checkAllBitLengthZero msgs
     ++ₗ checkDuplicateMessageNames msgs
     ++ₗ checkAllOffsetScaleRange msgs
     ++ₗ checkAllEmptyMessage msgs
     ++ₗ checkAllStartBitOutOfRange msgs
     ++ₗ checkAllBitLengthExcessive msgs
     ++ₗ checkDuplicateAttributeNames attrs
     ++ₗ checkAllUnknownCommentTargets msgs nodes envVars cmts
     ++ₗ checkAllUnknownMessageSenders msgs nodes
