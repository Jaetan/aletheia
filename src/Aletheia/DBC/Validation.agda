{-# OPTIONS --safe --without-K #-}

module Aletheia.DBC.Validation where

open import Aletheia.DBC.Types
open import Aletheia.CAN.Frame
open import Aletheia.CAN.Signal
open import Data.String using (String)
open import Data.String.Base renaming (_++_ to _++ₛ_)
open import Data.String.Properties renaming (_≟_ to _≟ₛ_)
open import Data.Rational using (ℚ; 0ℚ)
open import Data.Rational.Properties renaming (_≟_ to _≟ᵣ_; _≤?_ to _≤?ᵣ_)
open import Data.Nat using (ℕ; _+_; _≤ᵇ_)
open import Data.Nat.Show renaming (show to showℕ)
open import Data.Fin using (toℕ)
open import Data.List using (List; []; _∷_; map; concatMap; null; _++_)
open import Data.Bool using (Bool; true; false; _∧_; _∨_; not; if_then_else_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Nullary.Decidable using (⌊_⌋)

-- ============================================================================
-- VALIDATION ERROR TYPES
-- ============================================================================

data ValidationError : Set where
  -- Two signals overlap in bit positions
  SignalOverlap : (msg : String) → (sig1 : String) → (sig2 : String) → ValidationError

  -- Signal extends beyond frame boundary
  SignalOutOfFrame : (msg : String) → (sig : String) → (endBit : ℕ) → ValidationError

  -- Signal has invalid range (min > max)
  InvalidRange : (msg : String) → (sig : String) → (min : ℚ) → (max : ℚ) → ValidationError

  -- Signal has zero factor (division by zero)
  ZeroFactor : (msg : String) → (sig : String) → ValidationError

-- ============================================================================
-- VALIDATION HELPER FUNCTIONS
-- ============================================================================

-- Get the start and end bit positions of a signal
signalBitRange : DBCSignal → ℕ × ℕ
signalBitRange sig =
  let startBit = toℕ (SignalDef.startBit (DBCSignal.signalDef sig))
      bitLength = toℕ (SignalDef.bitLength (DBCSignal.signalDef sig))
  in (startBit , startBit + bitLength)

-- Check if two signals overlap in bit positions
signalsOverlap : DBCSignal → DBCSignal → Bool
signalsOverlap sig1 sig2 =
  let (start1 , end1) = signalBitRange sig1
      (start2 , end2) = signalBitRange sig2
      -- Overlap if: start1 < end2 AND start2 < end1
      overlap1 = (start1 Data.Nat.<ᵇ end2)
      overlap2 = (start2 Data.Nat.<ᵇ end1)
  in overlap1 ∧ overlap2
  where open import Data.Nat using (_<ᵇ_)

-- Check if signal fits within frame (64 bits for standard CAN)
signalFitsInFrame : DBCSignal → Bool
signalFitsInFrame sig =
  let (_ , endBit) = signalBitRange sig
  in endBit ≤ᵇ 64

-- ============================================================================
-- SIGNAL VALIDATION
-- ============================================================================

validateSignal : String → DBCSignal → List ValidationError
validateSignal msgName sig =
  let sigName = DBCSignal.name sig
      def = DBCSignal.signalDef sig
      errors = []

      -- Check if signal fits in frame
      errors₁ = if signalFitsInFrame sig
                then errors
                else SignalOutOfFrame msgName sigName (proj₂ (signalBitRange sig)) ∷ errors

      -- Check if range is valid (min ≤ max)
      minVal = SignalDef.minimum def
      maxVal = SignalDef.maximum def
      validRange = ⌊ minVal ≤?ᵣ maxVal ⌋
      errors₂ = if validRange
                then errors₁
                else InvalidRange msgName sigName minVal maxVal ∷ errors₁

      -- Check if factor is non-zero
      factor = SignalDef.factor def
      isZero = ⌊ factor ≟ᵣ 0ℚ ⌋
      errors₃ = if isZero
                then ZeroFactor msgName sigName ∷ errors₂
                else errors₂

  in errors₃

-- ============================================================================
-- MESSAGE VALIDATION
-- ============================================================================

-- Check all pairs of signals for overlap
checkSignalOverlaps : String → List DBCSignal → List ValidationError
checkSignalOverlaps msgName [] = []
checkSignalOverlaps msgName (sig ∷ rest) =
  checkAgainstRest sig rest ++ checkSignalOverlaps msgName rest
  where
    -- Check current signal against all remaining signals
    checkAgainstRest : DBCSignal → List DBCSignal → List ValidationError
    checkAgainstRest _ [] = []
    checkAgainstRest s (other ∷ others) =
      let overlapError = if signalsOverlap s other
                         then SignalOverlap msgName (DBCSignal.name s) (DBCSignal.name other) ∷ []
                         else []
          restErrs = checkAgainstRest s others
      in overlapError ++ restErrs

validateMessage : DBCMessage → List ValidationError
validateMessage msg =
  let msgName = DBCMessage.name msg
      signals = DBCMessage.signals msg

      -- Validate each signal individually
      signalErrors = concatMap (validateSignal msgName) signals

      -- Check for signal overlaps
      overlapErrors = checkSignalOverlaps msgName signals

  in signalErrors ++ overlapErrors

-- ============================================================================
-- DBC VALIDATION
-- ============================================================================

validateDBC : DBC → List ValidationError
validateDBC dbc = concatMap validateMessage (DBC.messages dbc)

-- Check if DBC is valid (no validation errors)
isValidDBC : DBC → Bool
isValidDBC dbc = null (validateDBC dbc)

-- Format validation error as human-readable message
formatValidationError : ValidationError → String
formatValidationError (SignalOverlap msg sig1 sig2) =
  "In message '" ++ₛ msg ++ₛ "': signals '" ++ₛ sig1 ++ₛ "' and '" ++ₛ sig2 ++ₛ "' overlap in bit positions"
formatValidationError (SignalOutOfFrame msg sig endBit) =
  "In message '" ++ₛ msg ++ₛ "': signal '" ++ₛ sig ++ₛ "' extends beyond frame boundary (end bit: " ++ₛ showℕ endBit ++ₛ " > 64)"
formatValidationError (InvalidRange msg sig minVal maxVal) =
  "In message '" ++ₛ msg ++ₛ "': signal '" ++ₛ sig ++ₛ "' has invalid range (minimum > maximum)"
formatValidationError (ZeroFactor msg sig) =
  "In message '" ++ₛ msg ++ₛ "': signal '" ++ₛ sig ++ₛ "' has zero factor (division by zero)"

-- Format all validation errors as list of messages
formatValidationErrors : List ValidationError → List String
formatValidationErrors errors = Data.List.map formatValidationError errors
  where open import Data.List as DL
