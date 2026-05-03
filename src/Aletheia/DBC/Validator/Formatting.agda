{-# OPTIONS --safe --without-K #-}

-- DBC validator output formatting and filtering.
--
-- Purpose: Utilities for processing ValidationIssue lists after validation.
-- Exports: hasAnyError, formatIssuesText, errorIssues, warningIssues.
-- Role: Used by Protocol.Handlers and Protocol.ResponseFormat to present
--   validation results to the user.
module Aletheia.DBC.Validator.Formatting where

open import Aletheia.DBC.Types using
  ( ValidationIssue; IssueSeverity; IsError; IsWarning )
open import Data.List using (List; []; _∷_)
open import Data.List.Base using (filterᵇ)
open import Data.Bool.ListAction using (any)
open import Data.String using (String) renaming (_++_ to _++ₛ_)
open import Data.Bool using (Bool; true; false)

private
  isError : ValidationIssue → Bool
  isError i with ValidationIssue.severity i
  ... | IsError   = true
  ... | IsWarning = false

  isWarning : ValidationIssue → Bool
  isWarning i with ValidationIssue.severity i
  ... | IsError   = false
  ... | IsWarning = true

-- Check if any issue in a list is an error
hasAnyError : List ValidationIssue → Bool
hasAnyError = any isError

-- Format issue list as a single human-readable error string
formatIssuesText : List ValidationIssue → String
formatIssuesText [] = ""
formatIssuesText (i ∷ []) = ValidationIssue.detail i
formatIssuesText (i ∷ rest) = ValidationIssue.detail i ++ₛ "; " ++ₛ formatIssuesText rest

-- Filter only error-severity issues
errorIssues : List ValidationIssue → List ValidationIssue
errorIssues = filterᵇ isError

-- Filter only warning-severity issues
warningIssues : List ValidationIssue → List ValidationIssue
warningIssues = filterᵇ isWarning
