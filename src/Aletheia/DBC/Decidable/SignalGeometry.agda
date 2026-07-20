-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Frame-capacity signal-geometry deciders — the decider SSOT shared by the
-- JSON entry gate (`JSONParser.physicalGate`), the text entry gate
-- (`TextParser.Topology.SignalLine.buildSignal`), the text-round-trip WF
-- checker arms (`WellFormedCheck.checkSignalBounds` / `pvGo`), and the
-- structural validator's geometry checks (`Validator.Checks`).  Sharing the
-- exact `Dec` forms is what makes the gate⇒checker deadness theorem
-- (`DBC.Properties.GeometryGateDeadness`) a statement about ONE set of
-- conditions rather than two skewed encodings.
--
-- The bound is the containing message's frame capacity, `dlcBytes (dlc) * 8`
-- — the DLC already encodes classic-CAN vs CAN-FD payload size.  The global
-- `max-physical-bits` constant remains only as the type-level ceiling
-- (`Formatter.WellFormed.WellFormedSignalDef`); every decider here takes the
-- message's `frameBytes` and derives the capacity itself.
--
-- Cold-path (per-DBC ingest / format / validate, never per-frame), so `Dec`
-- allocation is acceptable here; the hot-path performance rule applies to
-- streaming only.
module Aletheia.DBC.Decidable.SignalGeometry where

open import Data.Bool using (if_then_else_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _+_; _*_; _∸_; _<_; _≤_)
open import Data.Nat.Properties using (_<?_; _≤?_)
open import Relation.Nullary.Decidable using (Dec; does)

open import Aletheia.CAN.Endianness using (ByteOrder; LittleEndian; BigEndian; physicalBitPos)
open import Aletheia.Error using
  ( ParseError; SignalBitLengthZero; SignalStartBitExceedsFrame
  ; SignalBitLengthExceedsFrame; SignalBigEndianOverflow )

-- Start bit lies inside the frame.  Both byte orders; the entry gates apply
-- it to the raw (Motorola/DBC-wire) position, the checker arms to the
-- internal (post-conversion) position.
startBitInFrame? : (frameBytes sb : ℕ) → Dec (sb < frameBytes * 8)
startBitInFrame? frameBytes sb = sb <? frameBytes * 8

-- Bit length fits the frame capacity.
bitLengthInFrame? : (frameBytes bl : ℕ) → Dec (bl ≤ frameBytes * 8)
bitLengthInFrame? frameBytes bl = bl ≤? frameBytes * 8

-- Bit length is positive.
bitLengthPositive? : (bl : ℕ) → Dec (1 ≤ bl)
bitLengthPositive? bl = 1 ≤? bl

-- The signal's full extent fits the frame (internal/linear form: the
-- ascending run from the internal start bit stays inside the frame).
-- Decides the same proposition as `Validity.BitsInFrame` (validator CHECK 8)
-- and `PhysicallyValid`'s big-endian fits conjunct.
signalFitsFrame? : (frameBytes sb bl : ℕ) → Dec (sb + bl ≤ frameBytes * 8)
signalFitsFrame? frameBytes sb bl = sb + bl ≤? frameBytes * 8

-- Big-endian no-wrap, on the PRE-conversion (Motorola/DBC-wire) start bit:
-- descending `bl` bits from the MSB at `sb` must not run past the end of
-- the frame, i.e. `bl ∸ 1 ≤ physicalBitPos sb`.  This is the condition
-- under which `convertStartBit`'s monus cannot floor (no silent
-- relocation), and exactly the third hypothesis of
-- `convertStartBit-roundtrip`.
bigEndianNoWrap? : (frameBytes sb bl : ℕ)
  → Dec (bl ∸ 1 ≤ physicalBitPos frameBytes BigEndian sb)
bigEndianNoWrap? frameBytes sb bl = bl ∸ 1 ≤? physicalBitPos frameBytes BigEndian sb

-- ============================================================================
-- ENTRY-GATE CORE
-- ============================================================================

-- The single geometry gate both entry routes run on the RAW
-- (pre-conversion) start bit and bit length: `just` carries the typed
-- refusal (naming the submitted values), `nothing` means the geometry is
-- accepted.  `JSONParser.physicalGate` wraps the refusal as `ParseErr`;
-- the text route's `buildSignal` wraps it as `SignalGeometryError` with
-- the signal's name — one logic, two envelopes.  Both byte orders share
-- the three linear conditions; BE adds the no-wrap condition on the
-- pre-conversion physical MSB position — exactly the hypotheses of
-- `convertStartBit-roundtrip`, so an accepted BE signal's internal start
-- bit unconverts back to the submitted value (the monus in
-- `convertStartBit` cannot floor: no silent relocation).
geometryRefusal : ℕ → ByteOrder → ℕ → ℕ → Maybe ParseError
geometryRefusal frameBytes LittleEndian sb bl =
  if does (bitLengthPositive? bl)
    then (if does (startBitInFrame? frameBytes sb)
      then (if does (bitLengthInFrame? frameBytes bl)
        then nothing
        else just (SignalBitLengthExceedsFrame bl frameBytes))
      else just (SignalStartBitExceedsFrame sb frameBytes))
    else just SignalBitLengthZero
geometryRefusal frameBytes BigEndian sb bl =
  if does (bitLengthPositive? bl)
    then (if does (startBitInFrame? frameBytes sb)
      then (if does (bitLengthInFrame? frameBytes bl)
        then (if does (bigEndianNoWrap? frameBytes sb bl)
          then nothing
          else just (SignalBigEndianOverflow sb bl frameBytes))
        else just (SignalBitLengthExceedsFrame bl frameBytes))
      else just (SignalStartBitExceedsFrame sb frameBytes))
    else just SignalBitLengthZero
