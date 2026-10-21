-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- The validation issues of a DBC: filtered by severity, asked whether any is
-- an error, and written as the one text a refusal's message carries.
module Aletheia.DBC.Validator.Formatting where

open import Aletheia.DBC.Types using
  ( ValidationIssue; IsError; IsWarning )
open import Data.Char using (Char)
open import Data.List using (List; []; _∷_) renaming (_++_ to _++ₗ_)
open import Data.List.Base using (filterᵇ)
open import Data.Bool.ListAction using (any)
open import Data.String using (String; toList; fromList)
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

-- The details joined by "; ", as characters: each step copies one detail in
-- front of the rest, so the join is linear in the text it writes (a string
-- append copies both sides, and a join of appends copies the tail at every
-- step).
formatIssuesChars : List ValidationIssue → List Char
formatIssuesChars []             = []
formatIssuesChars (i ∷ [])       = toList (ValidationIssue.detail i)
formatIssuesChars (i ∷ j ∷ rest) = toList (ValidationIssue.detail i) ++ₗ ';' ∷ ' ' ∷ formatIssuesChars (j ∷ rest)

formatIssuesText : List ValidationIssue → String
formatIssuesText issues = fromList (formatIssuesChars issues)

-- Filter only error-severity issues
errorIssues : List ValidationIssue → List ValidationIssue
errorIssues = filterᵇ isError

-- Filter only warning-severity issues
warningIssues : List ValidationIssue → List ValidationIssue
warningIssues = filterᵇ isWarning
