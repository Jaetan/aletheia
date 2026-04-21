{-# OPTIONS --safe --without-K #-}

-- DBC (Database CAN) text format writer — entry point (Phase B.3.c.k).
--
-- Purpose: Emit the canonical ASCII `.dbc` text form of a `DBC` value.
-- Pairs with `Aletheia.DBC.TextParser.parseText` to close the structural
-- roundtrip `parseText ∘ formatText ≡ id` at the DBC value level.
--
-- Role: The per-section emitters live under `Aletheia.DBC.TextFormatter.*`
-- (`Preamble`, `Topology`, `ValueTables`, `Attributes`, `Comments`,
-- `SignalGroups`, `EnvVars`).  `TextFormatter.TopLevel.emitDBCText` pins
-- the canonical section order; this module just delegates.  Keeping the
-- public entry point here (not re-routed through a deeper module)
-- matches the JSON side's `Aletheia.DBC.Formatter` top-level.
--
-- Semantic-equivalence caveat (from PARITY_PLAN.md §B.3.a):
--   The roundtrip target is `parseText ∘ formatText ≡ id` at the DBC
--   *value* level, equivalently: `dbc_to_json (parseText (formatText d))`
--   is byte-identical to `dbc_to_json d`.  It is NOT `formatText ∘
--   parseText ≡ id` at the *String* level — DBC text has many
--   whitespace/ordering variants that normalize to the same DBC value,
--   and the formatter emits a single canonical variant per DBC.  The
--   snapshot corpus (`python/tests/fixtures/dbc_corpus/`) captures the
--   JSON image, not the text image, for precisely this reason.
module Aletheia.DBC.TextFormatter where

open import Data.String using (String)

open import Aletheia.DBC.Types using (DBC)
open import Aletheia.DBC.TextFormatter.TopLevel using (emitDBCText)

-- ============================================================================
-- ENTRY POINT
-- ============================================================================

-- Emit the canonical DBC text image.  See `TextFormatter.TopLevel` for
-- the canonical section ordering and the deliberate omissions of
-- constructs with no retained Agda field.
formatText : DBC → String
formatText = emitDBCText
