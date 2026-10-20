-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Every value batch extraction keeps fits the binary wire's rational slots.
--
-- Purpose: Prove that the success partition of the shared categoriser, and
--   so of extractAllSignals, holds only values `wireFits` accepts: both
--   components of each at most `max-rational-component-magnitude`.  The
--   FFI shim's binary encoder pokes these as Int64; its arm for a value
--   that does not fit is unreachable.
--   Every definition is erased, so the extraction handler can carry the
--   proof beside the values it returns and MAlonzo compiles none of it.
-- Key results: categorizeWith-values-fit, extractAllSignals-values-fit,
--   wireFits-components.
module Aletheia.CAN.Batch.WireFits where

open import Aletheia.CAN.Frame using (CANFrame)
open import Aletheia.CAN.ExtractionResult using
  (ExtractionResult; Success; SignalNotInDBC; SignalNotPresent; ValueOutOfBounds; ExtractionFailed)
open import Aletheia.Error using
  (MuxValueMismatch; MuxSignalNotFound; MuxChainCycle; MuxExtractionFailed;
   ValueExceedsWireRange; InContext; SignalPastFrameEnd)
open import Aletheia.CAN.SignalExtraction using (extractSignalDirect)
open import Aletheia.CAN.DBCHelpers using (findMessageById)
open import Aletheia.CAN.BatchExtraction using
  ( PartitionedResults; mkPartitionedResults; ExtractionResults
  ; wireFits; categorizeWith; categorizeResult; resultToString
  ; combinePartitioned; emptyPartitioned
  ; extractAllSignalsFromMessage; extractAllSignals
  )
open import Aletheia.DBC.Types using (DBC; DBCMessage; DBCSignal; signalNameStr)
open import Aletheia.Limits using (max-rational-component-magnitude)

open import Data.Bool using (true; false; T)
open import Data.Integer using (∣_∣)
open import Data.List using ([]; _∷_; map; foldr)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.All.Properties using (++⁺)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (suc; _≤_; _⊔′_)
open import Data.Nat.Properties using (≤ᵇ⇒≤; ⊔≡⊔′; m⊔n≤o⇒m≤o; m⊔n≤o⇒n≤o)
open import Data.Product using (_×_; _,_; proj₂)
open import Data.Rational using (ℚ)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; subst)

-- A keyed value whose rational fits the wire.
@0 Fits : ∀ {K : Set} → K × ℚ → Set
Fits p = T (wireFits (proj₂ p))

-- A value that fits has both reduced components within the bound.
@0 wireFits-components : ∀ q → T (wireFits q)
  → ∣ ℚ.numerator q ∣ ≤ max-rational-component-magnitude
  × suc (ℚ.denominator-1 q) ≤ max-rational-component-magnitude
wireFits-components q fits =
  let n = ∣ ℚ.numerator q ∣
      d = suc (ℚ.denominator-1 q)
      both = subst (_≤ max-rational-component-magnitude) (sym (⊔≡⊔′ n d))
               (≤ᵇ⇒≤ (n ⊔′ d) max-rational-component-magnitude fits)
  in m⊔n≤o⇒m≤o n d both , m⊔n≤o⇒n≤o n d both

-- THEOREM: the shared categoriser keeps a value only when it fits; a
-- Success that does not fit lands in the error partition instead.
@0 categorizeWith-values-fit : ∀ {K E : Set} (toErr : K → ExtractionResult → E) (key : K) (r : ExtractionResult)
  → All Fits (PartitionedResults.values (categorizeWith toErr key r))
categorizeWith-values-fit toErr key (Success v) with wireFits v in fits
... | true  = subst T (sym fits) tt ∷ []
... | false = []
categorizeWith-values-fit _ _ SignalNotInDBC                             = []
categorizeWith-values-fit _ _ (SignalNotPresent MuxValueMismatch)        = []
categorizeWith-values-fit _ _ (SignalNotPresent (MuxSignalNotFound _))   = []
categorizeWith-values-fit _ _ (SignalNotPresent MuxChainCycle)           = []
categorizeWith-values-fit _ _ (SignalNotPresent (MuxExtractionFailed _)) = []
categorizeWith-values-fit _ _ (SignalNotPresent ValueExceedsWireRange)   = []
categorizeWith-values-fit _ _ (SignalNotPresent (SignalPastFrameEnd _))  = []
categorizeWith-values-fit _ _ (SignalNotPresent (InContext _ _))         = []
categorizeWith-values-fit _ _ (ValueOutOfBounds _ _ _)                   = []
categorizeWith-values-fit _ _ (ExtractionFailed _)                       = []

-- Combining two partitions whose values all fit gives one whose values all fit.
@0 combinePartitioned-All : ∀ {K E : Set} {P : K × ℚ → Set} (a b : PartitionedResults K E)
  → All P (PartitionedResults.values a) → All P (PartitionedResults.values b)
  → All P (PartitionedResults.values (combinePartitioned a b))
combinePartitioned-All (mkPartitionedResults _ _ _) (mkPartitionedResults _ _ _) pa pb = ++⁺ pa pb

private
  -- One message's signals, each categorised against the frame.
  @0 categorise : ∀ {n} → CANFrame n → DBCMessage → DBCSignal → ExtractionResults
  categorise frame msg sig = categorizeResult (signalNameStr sig) (extractSignalDirect msg frame sig)

  @0 signals-values-fit : ∀ {n} (frame : CANFrame n) (msg : DBCMessage) sigs
    → All Fits (PartitionedResults.values
                 (foldr combinePartitioned emptyPartitioned (map (categorise frame msg) sigs)))
  signals-values-fit frame msg []           = []
  signals-values-fit frame msg (sig ∷ sigs) =
    combinePartitioned-All (categorise frame msg sig)
      (foldr combinePartitioned emptyPartitioned (map (categorise frame msg) sigs))
      (categorizeWith-values-fit resultToString (signalNameStr sig) (extractSignalDirect msg frame sig))
      (signals-values-fit frame msg sigs)

-- Lifted over a message's signals, one categorisation per signal.
@0 extractAllSignalsFromMessage-values-fit : ∀ {n} (frame : CANFrame n) (msg : DBCMessage)
  → All Fits (PartitionedResults.values (extractAllSignalsFromMessage frame msg))
extractAllSignalsFromMessage-values-fit frame msg = signals-values-fit frame msg (DBCMessage.signals msg)

-- THEOREM: every value the string-keyed batch extraction returns fits the
-- binary wire's rational slots.
@0 extractAllSignals-values-fit : ∀ {n} (dbc : DBC) (frame : CANFrame n)
  → All Fits (PartitionedResults.values (extractAllSignals dbc frame))
extractAllSignals-values-fit dbc frame with findMessageById (CANFrame.id frame) dbc
... | nothing  = []
... | just msg = extractAllSignalsFromMessage-values-fit frame msg
