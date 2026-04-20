{-# OPTIONS --safe --without-K #-}

-- Topology emitters for the DBC text format (Phase B.3.c.3).
--
-- Grammar slice emitted (mirrors `TextParser.Topology`):
--   bu-section    ::= "BU_:" (ws identifier)* newline
--   message       ::= "BO_" ws nat ws identifier ws? ":" ws nat ws identifier
--                     newline signal*
--   signal        ::= " SG_" ws identifier mux-ind? ws? ":" ws? nat "|" nat
--                     "@" byte-order-digit sign ws? "(" rational "," rational
--                     ")" ws? "[" rational "|" rational "]" ws? string-lit
--                     ws? identifier ("," identifier)* newline
--   mux-ind       ::= ws "M" | ws "m" nat | ws "m" nat "M"
--
-- Canonical choices (cantools parity):
--   * CAN ID encoding — standard IDs emit `n` as-is; extended IDs emit
--     `n + 2^31` (bit-31 flag).  Matches `TextParser.Topology.buildCANId`
--     exactly, so the roundtrip composes.
--   * Byte-order digit — `1` = LittleEndian (Intel), `0` = BigEndian
--     (Motorola); the start-bit is `unconvertStartBit`-transformed back
--     to DBC's MSB convention before emission.
--   * Sign flag — `+` = unsigned, `-` = signed (DBC historical encoding).
--   * Receiver list — emitted comma-separated; an empty in-memory list
--     falls back to `Vector__XXX` (cantools' no-named-receiver placeholder)
--     so the SG_ line always satisfies the grammar's ≥1 receiver requirement.
--   * Mux marker — `M` on the multiplexor itself (found via
--     `findMuxMaster`), `m<N>` on selected signals, no marker on plain
--     always-present signals.  Multi-value selectors (`SG_MUL_VAL_`) and
--     nested multiplexors (`m<N>M`) are deferred to B.3.c.8; this phase
--     emits the head value of the `When _ values` list only, which matches
--     single-value cantools output.
--
-- Each BO_ block ends with the BO_ line + SG_ lines + one trailing blank
-- line separating it from the next block.  `emitMessages` concatenates.
module Aletheia.DBC.TextFormatter.Topology where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_; foldr)
open import Data.List.NonEmpty as List⁺ using (List⁺; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _+_; _^_)
open import Data.String using (String) renaming (_++_ to _++ₛ_)
open import Data.String.Properties using () renaming (_≟_ to _≟ₛ_)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import Aletheia.DBC.Types using
  (DBCMessage; DBCSignal; SignalPresence; Always; When; Node)
open import Aletheia.CAN.DLC using (dlcBytes)
open import Aletheia.CAN.Signal using (SignalDef)
open import Aletheia.CAN.Endianness using
  (ByteOrder; LittleEndian; BigEndian; unconvertStartBit)
open import Aletheia.CAN.Frame using (CANId; Standard; Extended)

open import Aletheia.DBC.TextFormatter.Emitter using
  (showℕ-dec; showℚ-dec; quoteStringLit)

-- ============================================================================
-- BU_ (NODES)
-- ============================================================================

-- `BU_:` + one space per node name + section-closing blank line.  Empty
-- node list emits `"BU_:\n\n"`.
emitBU : List Node → String
emitBU ns =
  "BU_:" ++ₛ foldr (λ n acc → " " ++ₛ Node.name n ++ₛ acc) "\n\n" ns

-- ============================================================================
-- CANID (raw ℕ for BO_ line)
-- ============================================================================

-- Cantools bit-31 flag convention: Standard → raw n; Extended → n + 2^31.
-- Written with a term-form `2 ^ 31` to bypass the stdlib `LiteralTooBig`
-- bound on numeric literals.
extFlagBit : ℕ
extFlagBit = 2 ^ 31

rawCanIdℕ : CANId → ℕ
rawCanIdℕ (Standard n _) = n
rawCanIdℕ (Extended n _) = n + extFlagBit

-- ============================================================================
-- SG_ FIELD EMITTERS
-- ============================================================================

emitByteOrderDigit : ByteOrder → String
emitByteOrderDigit LittleEndian = "1"
emitByteOrderDigit BigEndian    = "0"

-- '-' = signed, '+' = unsigned (DBC historical encoding — opposite of
-- cantools' `isSigned : Bool` field semantics, which is why we flip here).
emitSignFlag : Bool → String
emitSignFlag true  = "-"
emitSignFlag false = "+"

-- Comma-separated receivers; `Vector__XXX` placeholder when empty (matches
-- cantools output and satisfies the grammar's ≥1-receiver requirement).
emitReceivers : List String → String
emitReceivers []       = "Vector__XXX"
emitReceivers (r ∷ rs) =
  r ++ₛ foldr (λ x acc → "," ++ₛ x ++ₛ acc) "" rs

-- ============================================================================
-- MUX RESOLUTION (scan signals for the master)
-- ============================================================================

-- Scan signals for the multiplexor master's name, found via any `When m _`
-- clause.  Returns `nothing` if no signal references a master (no mux in
-- this message).  All well-formed `When` clauses in one message reference
-- the same master (validator invariant), so the first hit is authoritative.
findMuxMaster : List DBCSignal → Maybe String
findMuxMaster [] = nothing
findMuxMaster (s ∷ rest) with DBCSignal.presence s
... | Always   = findMuxMaster rest
... | When m _ = just m

-- Emit the mux indicator for one signal, given the master's name (if any).
--   * `Always` + name == master       ⇒ " M"
--   * `Always` + name != master       ⇒ ""
--   * `When _ (v ∷ _)`                 ⇒ " m<v>" (head value only)
--   * No master (nothing)             ⇒ "" for any Always, still " m<v>"
--                                        for `When` (ill-formed input, but
--                                        emitted faithfully so the
--                                        validator catches it on the next
--                                        reparse).
emitMuxMarker : Maybe String → (thisName : String) → SignalPresence → String
emitMuxMarker nothing       _        Always         = ""
emitMuxMarker (just master) thisName Always         =
  if ⌊ thisName ≟ₛ master ⌋ then " M" else ""
emitMuxMarker _             _        (When _ (v ∷ _)) =
  " m" ++ₛ showℕ-dec v

-- ============================================================================
-- SG_ LINE EMITTER
-- ============================================================================

-- One SG_ line including its trailing newline.  The message's DLC byte
-- count is needed by `unconvertStartBit` to de-normalize the start-bit for
-- BigEndian signals.
emitSignalLine : (master : Maybe String) (frameBytes : ℕ) → DBCSignal → String
emitSignalLine master frameBytes sig =
  let def = DBCSignal.signalDef sig
      bo  = DBCSignal.byteOrder sig
      sb  = unconvertStartBit frameBytes bo
              (SignalDef.startBit def) (SignalDef.bitLength def)
  in " SG_ " ++ₛ DBCSignal.name sig ++ₛ
     emitMuxMarker master (DBCSignal.name sig) (DBCSignal.presence sig) ++ₛ
     " : " ++ₛ showℕ-dec sb ++ₛ "|" ++ₛ showℕ-dec (SignalDef.bitLength def) ++ₛ
     "@" ++ₛ emitByteOrderDigit bo ++ₛ emitSignFlag (SignalDef.isSigned def) ++ₛ
     " (" ++ₛ showℚ-dec (SignalDef.factor def) ++ₛ "," ++ₛ
     showℚ-dec (SignalDef.offset def) ++ₛ ")" ++ₛ
     " [" ++ₛ showℚ-dec (SignalDef.minimum def) ++ₛ "|" ++ₛ
     showℚ-dec (SignalDef.maximum def) ++ₛ "]" ++ₛ
     " " ++ₛ quoteStringLit (DBCSignal.unit sig) ++ₛ
     " " ++ₛ emitReceivers (DBCSignal.receivers sig) ++ₛ "\n"

-- ============================================================================
-- BO_ BLOCK + MESSAGES SECTION
-- ============================================================================

-- One BO_ block: header line + all SG_ lines + single trailing blank.
-- BO_TX_BU_ (message `senders`) is deferred to a future sub-commit; this
-- phase treats the list as unused on the output path.  Callers that need
-- it will emit separate `BO_TX_BU_` lines alongside `emitMessages`.
emitMessage : DBCMessage → String
emitMessage msg =
  let fb     = dlcBytes (DBCMessage.dlc msg)
      sigs   = DBCMessage.signals msg
      master = findMuxMaster sigs
  in "BO_ " ++ₛ showℕ-dec (rawCanIdℕ (DBCMessage.id msg)) ++ₛ
     " " ++ₛ DBCMessage.name msg ++ₛ ": " ++ₛ
     showℕ-dec fb ++ₛ " " ++ₛ DBCMessage.sender msg ++ₛ "\n" ++ₛ
     foldr (λ s acc → emitSignalLine master fb s ++ₛ acc) "" sigs ++ₛ "\n"

emitMessages : List DBCMessage → String
emitMessages = foldr (λ m acc → emitMessage m ++ₛ acc) ""
