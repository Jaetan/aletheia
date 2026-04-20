{-# OPTIONS --safe --without-K #-}

-- DBC (Database CAN) text format writer — skeleton (Phase B.3.b).
--
-- Purpose: Emit the canonical ASCII `.dbc` text form of a `DBC` value.
-- Pairs with `Aletheia.DBC.TextParser` to close the structural roundtrip
-- `parseText ∘ formatText ≡ id` at the DBC level.
--
-- Role: Phase B.3.c fills in per-construct emitters in grammar order;
-- B.3.d proves the structural roundtrip against `parseText`.
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
--
-- Skeleton state (B.3.b):
--   * `formatText` is wired as an empty-string stub; `Aletheia.Main` is
--     intentionally NOT updated — the skeleton stays out of the runtime
--     path until B.3.e.
--
-- Design notes (forward to B.3.c):
--   * Canonical emission order must match the PARITY_PLAN.md §B.3
--     construct inventory and the existing `DBC/Formatter.agda` (JSON)
--     field order so that proof lemmas can reuse the per-construct
--     roundtrip scaffolding under `DBC/Formatter/` directly.
--   * Numeric emission (rationals) mirrors `DBC/Formatter.agda`'s decimal
--     rendering; leading/trailing whitespace is never significant in the
--     DBC text grammar, so the formatter emits a single space between
--     lexemes and `\n` for line terminators.
module Aletheia.DBC.TextFormatter where

open import Data.String using (String)

open import Aletheia.DBC.Types using (DBC)

-- ============================================================================
-- ENTRY POINT
-- ============================================================================

-- Skeleton stub.  Returns an empty string until B.3.c begins wiring the
-- per-construct emitters.
formatText : DBC → String
formatText _ = ""
