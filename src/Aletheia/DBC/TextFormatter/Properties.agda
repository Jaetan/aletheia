{-# OPTIONS --safe --without-K #-}

-- Correctness properties for the DBC text-format writer — facade
-- placeholder (Track B.3.b).
--
-- Purpose: Top-level theorem module for `Aletheia.DBC.TextFormatter`.
-- Split-from-day-one structure mirrors `TextParser/Properties.agda` so
-- the two facades evolve in lockstep during B.3.c/B.3.d.
--
-- Planned sub-files (populated alongside the B.3.c emitters):
--   * Aletheia.DBC.TextFormatter.Canonicalization.agda — the formatter
--     produces a single canonical text form per DBC value (no ordering
--     or whitespace choices depend on call-site state).
--   * Aletheia.DBC.TextFormatter.Lexical.agda — every emitted token
--     satisfies the corresponding grammar terminal from
--     TextParser.agda's BNF (string literals escape `"` correctly,
--     numeric emissions are in the grammar's rational sublanguage,
--     identifiers stay inside the grammar's character class).
--   * Aletheia.DBC.TextFormatter.Idempotence.agda — `formatText` is a
--     fixed point of the parse-format roundtrip on its own output,
--     mirroring the `format-parse-format` corollary in
--     `DBC/Formatter/Properties.agda`.
--
-- Facade contract (B.3.d): this module will `open import ... public
-- using (...)` the sub-file lemmas plus expose the formatter-injective
-- corollary `formatText-injective : ∀ d₁ d₂ → formatText d₁ ≡ formatText
-- d₂ → d₁ ≡ d₂`, derived by composing the roundtrip from
-- `TextParser.Properties`.  For B.3.b the module body is intentionally
-- empty — see the matching caveat in `TextParser/Properties.agda`.
module Aletheia.DBC.TextFormatter.Properties where
