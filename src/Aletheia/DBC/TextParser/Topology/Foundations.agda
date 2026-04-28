{-# OPTIONS --safe --without-K #-}

-- Foundations subset of `Aletheia.DBC.TextParser.Topology` (B.3.d ε.2).
--
-- Hosts the definitions that `Properties.Primitives`, `Attributes`,
-- `Comments`, and the `Properties.{Attributes.Assign,Comments}` family
-- need from Topology — namely the CANID encoding (`buildCANId`,
-- `extFlagBit`) and the SG_ mux-marker primitives (`MuxMarker` data type,
-- `parseMuxMarker`, `parseByteOrderDigit`, `parseSignFlag`).
--
-- Splitting these out breaks the import cycle that previously forced the
-- entire DBC text-parser cluster to bottom out at the monolithic
-- `Topology` module:
--
--   Topology → Format → Properties.Primitives → Attributes → Topology
--
-- After ε.2: `Properties.Primitives`/`Attributes`/etc. import from
-- `Topology.Foundations` directly, leaving `Topology.SignalLine` free to
-- import `Format.Receivers` (the ε.3 prerequisite) without resurrecting
-- the cycle.  Existing importers continue to use `Topology` as a
-- re-export facade.
module Aletheia.DBC.TextParser.Topology.Foundations where

open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _∸_; _^_; _<ᵇ_; _≤ᵇ_)

open import Aletheia.Parser.Combinators using
  (Parser; pure; _>>=_; _<|>_; _*>_; char)
open import Aletheia.DBC.TextParser.Lexer using
  (parseWS; parseNatural)
open import Aletheia.CAN.Frame using (CANId; Standard; Extended)
open import Aletheia.CAN.Endianness using
  (ByteOrder; LittleEndian; BigEndian)
open import Aletheia.CAN.Constants using
  (standard-can-id-max; extended-can-id-max)
open import Aletheia.Prelude using (ifᵀ_then_else_)

-- ============================================================================
-- CANID (text-level bit-31 flag encoding)
-- ============================================================================

-- `2 ^ 31` as a term to sidestep the stdlib `LiteralTooBig` bound.
extFlagBit : ℕ
extFlagBit = 2 ^ 31

-- Decode a raw BO_ ℕ into a CANId, ranged-checked.  Returns `nothing` when
-- the ID is out of range for its (inferred) category.
buildCANId : ℕ → Maybe CANId
buildCANId raw =
  ifᵀ extFlagBit ≤ᵇ raw
    then (λ _ →
      let n = raw ∸ extFlagBit
      in ifᵀ n <ᵇ extended-can-id-max
           then (λ pf → just (Extended n pf))
           else nothing)
    else (ifᵀ raw <ᵇ standard-can-id-max
            then (λ pf → just (Standard raw pf))
            else nothing)

-- ============================================================================
-- SG_ MUX INDICATOR (pre-resolution)
-- ============================================================================

-- Encodes the syntactic mux role before the master's name is known:
--   NotMux    — no marker; always-present signal, not the master.
--   IsMux     — `M`; this signal is the multiplexor master.
--   SelBy n   — `m<n>`; present when the master's value is n.
--   BothMux n — `m<n>M`; nested — both selected by an outer master AND
--               itself a multiplexor for inner signals.  The `n` is the
--               outer-master selector; the inner role is implicit.
data MuxMarker : Set where
  NotMux   : MuxMarker
  IsMux    : MuxMarker
  SelBy    : ℕ → MuxMarker
  BothMux  : ℕ → MuxMarker

-- Parse an optional mux indicator.  Enters via `parseWS` (one required
-- space after the signal name); if the next character isn't `M` or `m`,
-- the outer `<|>` restores state to the pre-`parseWS` position and the
-- caller's next `parseWSOpt` handles separator whitespace.
parseMuxMarker : Parser MuxMarker
parseMuxMarker =
  (parseWS *>
    ((char 'M' *> pure IsMux) <|>
     (char 'm' *> parseNatural >>= λ n →
       (char 'M' *> pure (BothMux n)) <|>
       pure (SelBy n))))
  <|> pure NotMux

parseByteOrderDigit : Parser ByteOrder
parseByteOrderDigit =
  (char '0' *> pure BigEndian) <|>
  (char '1' *> pure LittleEndian)

-- DBC historical encoding: `+` = unsigned, `-` = signed.  Note: the
-- DBCSignal field is `isSigned : Bool`, so `-` ⇒ true, `+` ⇒ false.
parseSignFlag : Parser Bool
parseSignFlag =
  (char '+' *> pure false) <|>
  (char '-' *> pure true)
