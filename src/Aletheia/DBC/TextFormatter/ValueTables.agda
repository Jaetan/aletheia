{-# OPTIONS --safe --without-K #-}

-- Value-table emitters for the DBC text format (Phase B.3.c.4).
--
-- Grammar slice emitted (mirrors `TextParser.ValueTables`):
--   val-table    ::= "VAL_TABLE_" ws identifier (ws nat ws string-lit)*
--                    ws? ";" newline
--   value-desc   ::= "VAL_" ws nat ws identifier (ws nat ws string-lit)*
--                    ws? ";" newline            -- NOT emitted (see below).
--
-- Scope caveat — `VAL_` silently dropped:
--   The Agda `DBCSignal` record has no `valueDescriptions` field, so there
--   is nowhere to store per-signal enum labels.  This mirrors the existing
--   Python pipeline exactly: `cantools` → `dbc_to_json` (see
--   `python/aletheia/dbc_converter.py`) processes `value_tables.items()`
--   but drops `signal.choices`.  The text layer stays faithful to the
--   in-memory data model, so no VAL_ lines are emitted.  If B.3.g needs to
--   preserve `VAL_` for cantools-dropped fixtures, promote
--   `DBCSignal.valueDescriptions` end-to-end first; the text layer will
--   follow the type.
--
-- Canonical choices (cantools parity):
--   * One space between every token; one space before the terminating `;`.
--   * Each VAL_TABLE_ line ends with `;\n`; lines are packed directly with
--     no blank-line separator between tables, so `emitValueTables` just
--     concatenates via `foldr` without an inter-line combinator.  Blank-
--     line separation to the next section is the composer's job, not this
--     emitter's.
--   * Zero-entry VAL_TABLE_ (e.g. `VAL_TABLE_ Empty ;`) is representable
--     in the record type and emitted faithfully.  The corpus never carries
--     one (cantools drops empty tables), but the grammar allows it and the
--     roundtrip proof in B.3.d needs the case to hold.
module Aletheia.DBC.TextFormatter.ValueTables where

open import Data.List using (List; []; _∷_; foldr)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open import Data.String using (String) renaming (_++_ to _++ₛ_)

open import Aletheia.DBC.Types using (ValueTable)
open import Aletheia.DBC.TextFormatter.Emitter using (showℕ-dec; quoteStringLit)

-- ============================================================================
-- ENTRY EMITTER
-- ============================================================================

-- One `nat ws string-lit` pair, preceded by a single space.  Called in a
-- right fold where the accumulator carries the trailing ` ;\n` terminator,
-- so each entry slot in the grammar just contributes ` <nat> "<str>"`.
emitValueEntry : (ℕ × String) → String
emitValueEntry (v , desc) =
  " " ++ₛ showℕ-dec v ++ₛ " " ++ₛ quoteStringLit desc

-- ============================================================================
-- VAL_TABLE_ LINE
-- ============================================================================

-- `"VAL_TABLE_" ws identifier entries ws? ";" newline`.  Lines are packed
-- directly, with no blank-line separator between VAL_TABLE_ entries;
-- `emitValueTables` concatenates via `foldr` without an inter-line
-- combinator.  `parseValueLine` on the parse side tolerates optional
-- trailing blanks via its `many parseNewline` tail (for hand-written
-- inputs), but this emitter never produces any.
emitValueTable : ValueTable → String
emitValueTable vt =
  "VAL_TABLE_ " ++ₛ ValueTable.name vt ++ₛ
  foldr (λ e acc → emitValueEntry e ++ₛ acc) " ;\n" (ValueTable.entries vt)

-- ============================================================================
-- SECTION EMITTER
-- ============================================================================

-- Zero-or-more VAL_TABLE_ lines, concatenated.  Empty list emits `""`,
-- matching cantools' behaviour when no value tables are defined.
emitValueTables : List ValueTable → String
emitValueTables = foldr (λ vt acc → emitValueTable vt ++ₛ acc) ""
