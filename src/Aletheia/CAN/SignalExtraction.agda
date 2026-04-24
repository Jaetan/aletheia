{-# OPTIONS --safe --without-K #-}

-- High-level signal extraction using DBC context.
--
-- Purpose: Extract signals from frames by name using DBC definitions.
-- Operations: extractSignalWithContext (DBC + frame + signal name → ExtractionResult).
-- Role: User-facing API combining DBC lookup with CAN.Encoding.
--
-- Workflow: Lookup signal definition in DBC → validate frame ID → extract bits → scale.
module Aletheia.CAN.SignalExtraction where
open import Aletheia.DBC.Identifier using (Identifier)
open import Aletheia.DBC.Types using (signalNameStr)

open import Aletheia.CAN.Frame using (CANFrame)
open import Aletheia.CAN.Signal using (SignalDef)
open import Aletheia.CAN.Encoding using (extractSignal; extractSignalCoreFast; scaleExtracted; extractionBytes)
open import Aletheia.CAN.Encoding.Arithmetic using (inBounds)
open import Aletheia.CAN.ExtractionResult using (ExtractionResult; Success; SignalNotInDBC; SignalNotPresent; ValueOutOfBounds)
open import Aletheia.DBC.DecRat using (toℚ)
open import Aletheia.CAN.DBCHelpers using (findMessageById; findSignalByName)
open import Aletheia.DBC.Types using (DBC; DBCMessage; DBCSignal; SignalPresence; Always; When)
open import Aletheia.Error using (ExtractionError; MuxValueMismatch; MuxSignalNotFound; MuxChainCycle; MuxExtractionFailed)
open import Data.String using (String)
open import Data.Rational using (ℚ; _/_; _≤ᵇ_)
open import Data.Integer using (+_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; _∷_; []; length)
open import Data.Bool.ListAction using (any)
open import Data.List.NonEmpty as List⁺ using (List⁺)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (Bool; if_then_else_; _∧_)

-- ============================================================================
-- SIGNAL EXTRACTION WITH MULTIPLEXING (NESTED CHAINS SUPPORTED)
-- ============================================================================

-- Leaf operation: extract a multiplexor signal's value and check whether it
-- matches any of the expected selector values.
-- Returns: nothing on match, just reason on mismatch or extraction failure.
-- Bool fast path: `_≤ᵇ_` on ℚ compiles to a direct ℤ comparison without
-- allocating a Dec proof term per selector per call. The previous
-- `⌊ ℚ-Props._≟_ _ _ ⌋` form built a Dec for every selector on every mux
-- signal — an allocation hazard of the same class as the 5aa345e regression.
matchMuxValue : ∀ {n} → CANFrame n → DBCSignal → List⁺ ℕ → Maybe ExtractionError
matchMuxValue frame muxSig muxValues
  with extractSignal frame (DBCSignal.signalDef muxSig) (DBCSignal.byteOrder muxSig)
... | nothing = just (MuxExtractionFailed (signalNameStr muxSig))
... | just muxVal =
      let matches = any (λ v → let vℚ = (+ v) / 1
                                in (muxVal ≤ᵇ vℚ) ∧ (vℚ ≤ᵇ muxVal))
                        (List⁺.toList muxValues)
      in if matches
         then nothing
         else just MuxValueMismatch

-- Recursive presence check with bounded fuel, parameterised by SignalPresence
-- (not by DBCSignal). Pattern-matching directly on the presence keeps the
-- function reduction-friendly for proofs that need the leaf cases to compute.
--
-- For a When-multiplexed signal, the multiplexor itself may also be
-- conditionally present (nested mux). We walk the chain bottom-up: each
-- mux ancestor must itself be present AND its extracted value must match.
--
-- Termination: fuel ≤ length (DBCMessage.signals msg) at entry (the sole
-- caller `checkSignalPresence` passes exactly this value) and strictly
-- decreases at every recursive call (`suc f → f`). Structural recursion
-- on ℕ discharges Agda's termination checker — no well-founded machinery
-- or `<-Rec` wrapper is needed because the fuel argument is already the
-- decreasing measure.
--
-- Soundness of the fuel bound: the maximum length of an acyclic mux chain
-- through n signals is n — each signal name is visited at most once before
-- reaching an `Always` sink, so a chain longer than n must revisit a signal
-- (i.e. contain a cycle). A correctly validated DBC is acyclic (check 5 in
-- Validator.Checks rejects MultiplexorCycle), so exhausting fuel is only
-- possible if validation was skipped; the `just …` fallback below is a
-- defensive runtime error message for that case rather than a proof of
-- termination on malformed DBCs.
checkPresenceP : ∀ {n} → ℕ → CANFrame n → DBCMessage → SignalPresence → Maybe ExtractionError
checkPresenceP _       _     _   Always         = nothing
checkPresenceP zero    _     _   (When _ _)     =
  just MuxChainCycle
checkPresenceP (suc f) frame msg (When muxName muxValues)
  with findSignalByName (Identifier.name muxName) msg
... | nothing  = just (MuxSignalNotFound (Identifier.name muxName))
... | just muxSig with checkPresenceP f frame msg (DBCSignal.presence muxSig)
...   | just reason = just reason
...   | nothing     = matchMuxValue frame muxSig muxValues

-- Check if a signal is present in a frame (handles arbitrary nested mux).
-- Returns: nothing if present, just reason if not present.
checkSignalPresence : ∀ {n} → CANFrame n → DBCMessage → DBCSignal → Maybe ExtractionError
checkSignalPresence frame msg sig =
  checkPresenceP (length (DBCMessage.signals msg)) frame msg (DBCSignal.presence sig)

-- Extract signal from frame given known message and signal (no DBC lookups)
-- This is the fast path used by batch extraction.
extractSignalDirect : ∀ {n} → DBCMessage → CANFrame n → DBCSignal → ExtractionResult
extractSignalDirect msg frame sig with checkSignalPresence frame msg sig
... | just reason = SignalNotPresent reason
... | nothing =
        let sigDef = DBCSignal.signalDef sig
            bo = DBCSignal.byteOrder sig
            bytes = extractionBytes frame bo
            raw = extractSignalCoreFast bytes sigDef
            value = scaleExtracted raw sigDef
            minVal = toℚ (SignalDef.minimum sigDef)
            maxVal = toℚ (SignalDef.maximum sigDef)
        in if inBounds value minVal maxVal
           then Success value
           else ValueOutOfBounds value minVal maxVal

-- Extract signal value from frame with full error reporting
-- This is the primary interface for single signal extraction by name.
extractSignalWithContext : ∀ {n} → DBC → CANFrame n → String → ExtractionResult
extractSignalWithContext dbc frame signalName with findMessageById (CANFrame.id frame) dbc
... | nothing = SignalNotInDBC
... | just msg with findSignalByName signalName msg
...   | nothing = SignalNotInDBC
...   | just sig = extractSignalDirect msg frame sig

