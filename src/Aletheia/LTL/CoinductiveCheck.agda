{-# OPTIONS --without-K --guardedness --sized-types #-}

-- Bridge module: Provides coinductive LTL checking for list-based input
-- NOTE: Uses --sized-types, incompatible with --safe
-- This module isolates the unsafe boundary for SignalPredicate integration

module Aletheia.LTL.CoinductiveCheck where

open import Size using (∞)
open import Data.List using (List; length)
open import Data.Maybe using (Maybe)
open import Data.Bool using (Bool)
open import Data.Nat using (ℕ)

open import Aletheia.LTL.Syntax
open import Aletheia.Trace.CANTrace using (TimedFrame)
open import Aletheia.LTL.Coinductive using (checkPropertyList; runWithFuel)

-- Check LTL property on a list using coinductive semantics
-- Uses list length as fuel for extraction
checkCoinductive : LTL (TimedFrame → Bool) → List TimedFrame → Maybe Bool
checkCoinductive φ frames = runWithFuel (length frames) (checkPropertyList φ frames)

-- Check with explicit fuel (for larger traces)
checkCoinductiveWithFuel : ℕ → LTL (TimedFrame → Bool) → List TimedFrame → Maybe Bool
checkCoinductiveWithFuel fuel φ frames = runWithFuel fuel (checkPropertyList φ frames)
