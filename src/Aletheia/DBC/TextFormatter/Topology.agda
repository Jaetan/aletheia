{-# OPTIONS --safe --without-K #-}

-- Topology emitters for the DBC text format (Phase B.3.c.3; layer-1 form
-- 2026-04-24).
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
--     nested multiplexors (`m<N>M`) are deferred to a later
--     mux-integration sub-commit; this phase emits the head value of
--     the `When _ values` list only, which matches single-value
--     cantools output.  B.3.c.8 has already wired the parse-side drop
--     parser for `SG_MUL_VAL_` (see `TextParser.ExtendedMux`); the
--     cross-line coordination needed to materialise multi-value
--     `When` selectors is what remains.
--
-- Each BO_ block ends with the BO_ line + SG_ lines + one trailing blank
-- line separating it from the next block.  `emitMessages-chars` concatenates.
--
-- All emitters are `List Char`-valued (B.3.d Option 3a layer-1 layout —
-- see `Emitter` module header).
module Aletheia.DBC.TextFormatter.Topology where
open import Aletheia.DBC.Identifier using (Identifier)

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Char using (Char) renaming (_≟_ to _≟ᶜ_)
import Data.List.Properties as ListProps
open import Data.List using (List; []; _∷_; foldr) renaming (_++_ to _++ₗ_)
open import Data.List.NonEmpty as List⁺ using (List⁺; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _+_; _^_)
open import Data.String using (String; toList)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import Aletheia.DBC.Types using
  (DBCMessage; DBCSignal; SignalPresence; Always; When; Node)
open import Aletheia.CAN.DLC using (dlcBytes)
open import Aletheia.CAN.Signal using (SignalDef)
open import Aletheia.CAN.Endianness using
  (ByteOrder; LittleEndian; BigEndian; unconvertStartBit)
open import Aletheia.CAN.Frame using (CANId; Standard; Extended)

open import Aletheia.DBC.TextFormatter.Emitter using
  (showℕ-dec-chars; showDecRat-dec-chars; quoteStringLit-chars)

-- ============================================================================
-- BU_ (NODES)
-- ============================================================================

-- `BU_:` + one space per node name + section-closing blank line.  Empty
-- node list emits `BU_:\n\n` as `List Char`.
emitBU-chars : List Node → List Char
emitBU-chars ns =
  toList "BU_:" ++ₗ
  foldr (λ n acc → ' ' ∷ Identifier.name (Node.name n) ++ₗ acc) (toList "\n\n") ns

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

emitByteOrderDigit-chars : ByteOrder → List Char
emitByteOrderDigit-chars LittleEndian = '1' ∷ []
emitByteOrderDigit-chars BigEndian    = '0' ∷ []

-- '-' = signed, '+' = unsigned (DBC historical encoding — opposite of
-- cantools' `isSigned : Bool` field semantics, which is why we flip here).
emitSignFlag-chars : Bool → List Char
emitSignFlag-chars true  = '-' ∷ []
emitSignFlag-chars false = '+' ∷ []

-- Comma-separated receivers; `Vector__XXX` placeholder when empty (matches
-- cantools output and satisfies the grammar's ≥1-receiver requirement).
emitReceivers-chars : List Identifier → List Char
emitReceivers-chars []       = toList "Vector__XXX"
emitReceivers-chars (r ∷ rs) =
  Identifier.name r
    ++ₗ foldr (λ x acc → ',' ∷ Identifier.name x ++ₗ acc) [] rs

-- ============================================================================
-- MUX RESOLUTION (scan signals for the master)
-- ============================================================================

-- Scan signals for the multiplexor master's name, found via any `When m _`
-- clause.  Returns `nothing` if no signal references a master (no mux in
-- this message).  All well-formed `When` clauses in one message reference
-- the same master (validator invariant), so the first hit is authoritative.
-- 3d.4: returns `Maybe (List Char)` — `Identifier.name : List Char` post
-- de-tainting, so the result feeds straight into char-list comparison and
-- emission with no String roundtrip.
findMuxMaster : List DBCSignal → Maybe (List Char)
findMuxMaster [] = nothing
findMuxMaster (s ∷ rest) with DBCSignal.presence s
... | Always   = findMuxMaster rest
... | When m _ = just (Identifier.name m)

-- Emit the mux indicator for one signal, given the master's name (if any).
--   * `Always` + name == master       ⇒ " M"
--   * `Always` + name != master       ⇒ ""
--   * `When _ (v ∷ _)`                ⇒ " m<v>" (head value only)
--   * No master (nothing)             ⇒ "" for any Always, still " m<v>"
--                                       for `When` (ill-formed input, but
--                                       emitted faithfully so the
--                                       validator catches it on the next
--                                       reparse).
-- 3d.4: thisName / master are `List Char` (the Identifier name field type).
-- Comparison uses stdlib's lifted list equality (`≡-dec _≟ᶜ_`).
emitMuxMarker-chars : Maybe (List Char) → (thisName : List Char) → SignalPresence → List Char
emitMuxMarker-chars nothing       _        Always         = []
emitMuxMarker-chars (just master) thisName Always         =
  if ⌊ ListProps.≡-dec _≟ᶜ_ thisName master ⌋ then toList " M" else []
emitMuxMarker-chars _             _        (When _ (v ∷ _)) =
  toList " m" ++ₗ showℕ-dec-chars v

-- ============================================================================
-- SG_ LINE EMITTER
-- ============================================================================

-- One SG_ line including its trailing newline.  The message's DLC byte
-- count is needed by `unconvertStartBit` to de-normalize the start-bit for
-- BigEndian signals.
-- 3d.4: master / signal name are `List Char` throughout; no String roundtrip.
emitSignalLine-chars : (master : Maybe (List Char)) (frameBytes : ℕ) → DBCSignal → List Char
emitSignalLine-chars master frameBytes sig =
  let def = DBCSignal.signalDef sig
      bo  = DBCSignal.byteOrder sig
      sb  = unconvertStartBit frameBytes bo
              (SignalDef.startBit def) (SignalDef.bitLength def)
      thisName = Identifier.name (DBCSignal.name sig)
  in toList " SG_ " ++ₗ thisName ++ₗ
     emitMuxMarker-chars master thisName (DBCSignal.presence sig) ++ₗ
     toList " : " ++ₗ showℕ-dec-chars sb ++ₗ
     '|' ∷ showℕ-dec-chars (SignalDef.bitLength def) ++ₗ
     '@' ∷ emitByteOrderDigit-chars bo ++ₗ
     emitSignFlag-chars (SignalDef.isSigned def) ++ₗ
     toList " (" ++ₗ showDecRat-dec-chars (SignalDef.factor def) ++ₗ
     ',' ∷ showDecRat-dec-chars (SignalDef.offset def) ++ₗ
     toList ") " ++ₗ
     '[' ∷ showDecRat-dec-chars (SignalDef.minimum def) ++ₗ
     '|' ∷ showDecRat-dec-chars (SignalDef.maximum def) ++ₗ
     toList "] " ++ₗ
     quoteStringLit-chars (DBCSignal.unit sig) ++ₗ
     ' ' ∷ emitReceivers-chars (DBCSignal.receivers sig) ++ₗ
     '\n' ∷ []

-- ============================================================================
-- BO_ BLOCK + MESSAGES SECTION
-- ============================================================================

-- One BO_ block: header line + all SG_ lines + single trailing blank.
-- BO_TX_BU_ (message `senders`) is deferred to a future sub-commit; this
-- phase treats the list as unused on the output path.
emitMessage-chars : DBCMessage → List Char
emitMessage-chars msg =
  let fb     = dlcBytes (DBCMessage.dlc msg)
      sigs   = DBCMessage.signals msg
      master = findMuxMaster sigs
  in toList "BO_ " ++ₗ showℕ-dec-chars (rawCanIdℕ (DBCMessage.id msg)) ++ₗ
     ' ' ∷ Identifier.name (DBCMessage.name msg) ++ₗ
     toList ": " ++ₗ
     showℕ-dec-chars fb ++ₗ
     ' ' ∷ Identifier.name (DBCMessage.sender msg) ++ₗ
     '\n' ∷
     foldr (λ s acc → emitSignalLine-chars master fb s ++ₗ acc) [] sigs ++ₗ
     '\n' ∷ []

emitMessages-chars : List DBCMessage → List Char
emitMessages-chars =
  foldr (λ m acc → emitMessage-chars m ++ₗ acc) []
