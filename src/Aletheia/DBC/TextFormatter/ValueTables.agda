{-# OPTIONS --safe --without-K #-}

-- Value-table emitters for the DBC text format (Phase B.3.c.4; layer-1
-- form 2026-04-24).
--
-- Grammar slice emitted (mirrors `TextParser.ValueTables`):
--   val-table    ::= "VAL_TABLE_" ws identifier (ws nat ws string-lit)*
--                    ws? ";" newline
--   value-desc   ::= "VAL_" ws nat ws identifier (ws nat ws string-lit)*
--                    ws? ";" newline
--
-- Phase E.5–E.7 — VAL_ emit promotion:
--   `emitValueDescription-chars` (E.5) emits one VAL_ line for a single
--   `RawValueDesc`.  `emitValueDescriptions-chars` (E.7) is the section
--   composer that walks `collectFromMessages d.messages` (encounter-order
--   per the locked `(message-index, signal-index, val-desc-index)` sort
--   key) and concatenates per-line emits.  `formatChars-body` slots this
--   between the messages section and the env-vars section.
--
-- Canonical choices (cantools parity):
--   * One space between every token; one space before the terminating `;`.
--   * Each VAL_TABLE_ line ends with `;\n`; lines are packed directly with
--     no blank-line separator between tables, so `emitValueTables-chars`
--     just concatenates via `foldr` without an inter-line combinator.
--     Blank-line separation to the next section is the composer's job,
--     not this emitter's.
--   * Zero-entry VAL_TABLE_ (e.g. `VAL_TABLE_ Empty ;`) is representable
--     in the record type and emitted faithfully.  The corpus never carries
--     one (cantools drops empty tables), but the grammar allows it and the
--     roundtrip proof in B.3.d needs the case to hold.
--
-- All emitters are `List Char`-valued (B.3.d Option 3a layer-1 layout —
-- see `Emitter` module header).
module Aletheia.DBC.TextFormatter.ValueTables where

open import Data.Char using (Char)
open import Data.List using (List; []; _∷_; foldr) renaming (_++_ to _++ₗ_)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open import Data.String using (toList)

open import Aletheia.DBC.Identifier using (Identifier)
open import Aletheia.DBC.Types using (ValueTable; DBCMessage)
open import Aletheia.DBC.TextParser.ValueTables using (RawValueDesc)
open import Aletheia.DBC.TextParser.ValueDescriptions using (collectFromMessages)
open import Aletheia.DBC.TextFormatter.Topology using (rawCanIdℕ)
open import Aletheia.DBC.TextFormatter.Emitter using
  (showℕ-dec-chars; quoteStringLit-chars)

-- ============================================================================
-- ENTRY EMITTER
-- ============================================================================

-- One `nat ws string-lit` pair, preceded by a single space.  Called in a
-- right fold where the accumulator carries the trailing ` ;\n` terminator,
-- so each entry slot in the grammar just contributes ` <nat> "<str>"`.
-- Post-3d.4 + JSON-mirror: `desc : List Char` (matches `ValueTable.entries
-- : List (ℕ × List Char)` and `quoteStringLit-chars : List Char → List Char`).
emitValueEntry-chars : (ℕ × List Char) → List Char
emitValueEntry-chars (v , desc) =
  ' ' ∷ showℕ-dec-chars v ++ₗ ' ' ∷ quoteStringLit-chars desc

-- ============================================================================
-- VAL_TABLE_ LINE
-- ============================================================================

-- `"VAL_TABLE_" ws identifier entries ws? ";" newline`.  Lines are packed
-- directly, with no blank-line separator between VAL_TABLE_ entries.
-- `parseValueTable` on the parse side tolerates optional trailing blanks
-- via its `many parseNewline` tail (for hand-written inputs), but this
-- emitter never produces any.
emitValueTable-chars : ValueTable → List Char
emitValueTable-chars vt =
  toList "VAL_TABLE_ " ++ₗ Identifier.name (ValueTable.name vt) ++ₗ
  foldr (λ e acc → emitValueEntry-chars e ++ₗ acc)
        (toList " ;\n")
        (ValueTable.entries vt)

-- ============================================================================
-- SECTION EMITTER
-- ============================================================================

-- Zero-or-more VAL_TABLE_ lines, concatenated.  Empty list emits `[]`,
-- matching cantools' behaviour when no value tables are defined.
emitValueTables-chars : List ValueTable → List Char
emitValueTables-chars =
  foldr (λ vt acc → emitValueTable-chars vt ++ₗ acc) []

-- ============================================================================
-- VAL_ LINE (Phase E.5)
-- ============================================================================

-- `"VAL_" ws nat ws identifier (ws nat ws string-lit)* ws? ";" newline`.
-- Mirrors `emitValueTable-chars` with two extra fields up-front (the
-- owning message's CAN ID and the signal name); the entries fold reuses
-- `emitValueEntry-chars` directly because the per-entry grammar is
-- identical between VAL_ and VAL_TABLE_.  The CAN ID encodes via
-- `rawCanIdℕ` (Standard `n` ⇒ `n`; Extended `n` ⇒ `n + 2^31`); the parser
-- inverts via `buildCANId` (`buildCANId-rawCanIdℕ` proves the inverse
-- holds universally).
--
-- `toList "VAL_ "` carries the trailing space that `parseWS` requires
-- (one-or-more); the `' ' ∷` between the encoded ID and the signal name
-- carries the second `parseWS`; the `toList " ;\n"` accumulator carries
-- the canonical-`parseWSOpt` single space, the `;` terminator, and the
-- mandatory line-feed.  Trailing-blank-line tolerance lives in the
-- parser's `many parseNewline` tail, not on the emitter side.
emitValueDescription-chars : RawValueDesc → List Char
emitValueDescription-chars rvd =
  toList "VAL_ " ++ₗ
  showℕ-dec-chars (rawCanIdℕ (RawValueDesc.canId rvd)) ++ₗ
  ' ' ∷ Identifier.name (RawValueDesc.signalName rvd) ++ₗ
  foldr (λ e acc → emitValueEntry-chars e ++ₗ acc)
        (toList " ;\n")
        (RawValueDesc.entries rvd)

-- ============================================================================
-- VAL_ SECTION (Phase E.7)
-- ============================================================================

-- Zero-or-more VAL_ lines, concatenated.  Per the locked C1 sort key, the
-- input is `collectFromMessages d.messages` (encounter-order walk over
-- `messages[i].signals[j].valueDescriptions` skipping empty-vds signals).
-- Empty list emits `[]` — the section disappears when no signal carries
-- value descriptions, matching cantools.
--
-- Two layers:
--   * `emitValueDescriptions-rvds-chars` operates on the rvd list directly
--     — what `BodyBridge.emit-map-TVD-eq` consumes after the per-section
--     `foldr-emit-map-iso` reduction.
--   * `emitValueDescriptions-chars` is the user-facing wrapper that
--     `formatChars-body` calls.  Definitionally `emitValueDescriptions-
--     rvds-chars ∘ collectFromMessages`.
emitValueDescriptions-rvds-chars : List RawValueDesc → List Char
emitValueDescriptions-rvds-chars =
  foldr (λ rvd acc → emitValueDescription-chars rvd ++ₗ acc) []

emitValueDescriptions-chars : List DBCMessage → List Char
emitValueDescriptions-chars msgs =
  emitValueDescriptions-rvds-chars (collectFromMessages msgs)
