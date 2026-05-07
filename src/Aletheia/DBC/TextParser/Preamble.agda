{-# OPTIONS --safe --without-K #-}

-- Preamble parsers for the DBC text format (Track B.3.c.2; B.3.d
-- Layer 3 3d.5.d migrated 2026-04-29).
--
-- Grammar slice covered (BNF section A from `Aletheia.DBC.TextParser`):
--   version      ::= "VERSION" ws string-lit newline
--   ns           ::= "NS_" ws? ":" newline (blank-line | indent keyword newline)*
--   bs           ::= "BS_" ws? ":" (ws baud-rate-expr)? newline
--
-- Post-3d.5.d-3a: each parser is the η-style wrap `parse <fmt> >>=
-- many parseNewline >>= pure` over its DSL Format
-- (`Aletheia.DBC.TextParser.Format.Preamble`).  The Format DSL captures
-- the section's structural shape; the wrapper's `many parseNewline`
-- absorbs additional trailing blank lines (BU_/EV_/CM_ pattern).
--
-- NS_ is an exception: its body Format already captures the trailing
-- blank line (via the discard-iso over `many nsLineFmt` whose canonical
-- last element is `ns-blank`), so the wrapper just chains `pure tt`
-- after `parse nsFmt` — no extra `many parseNewline`.
--
-- Discarded content: the `DBC` record (`Aletheia.DBC.Types`) has no NS_
-- or BS_ fields (cantools discards them structurally too).  Both
-- `parseNamespace` and `parseBitTiming` return `⊤` — the text is
-- consumed for syntactic correctness but no structural payload is
-- retained.  The roundtrip target is at DBC *value* level (see
-- TextFormatter.agda caveat), so `formatText ∘ parseText` is free to
-- canonicalise the NS_ keyword list and baud-rate expression without
-- breaking the equivalence.
--
-- NS_ body permissiveness: the Format's `many nsLineFmt` accepts any
-- mix of blank and indented-keyword lines, matching the pre-3d.5.d
-- `many parseNSLine` spec.  The formatter emits the cantools-canonical
-- 25-keyword block followed by a blank line; the parser tolerates any
-- subset / superset / vendor-extension keyword list.
module Aletheia.DBC.TextParser.Preamble where

open import Data.Char using (Char)
open import Data.List using (List)
open import Data.Unit using (⊤; tt)

open import Aletheia.Parser.Combinators using
  (Parser; pure; _>>=_; many)
open import Aletheia.DBC.TextParser.Lexer using (parseNewline)
open import Aletheia.DBC.TextParser.Format using (parse)
open import Aletheia.DBC.TextParser.Format.Preamble using
  (versionFmt; bitTimingFmt; nsFmt)

-- ============================================================================
-- VERSION
-- ============================================================================

-- η-style wrap: `parse versionFmt` consumes `"VERSION " <string-lit>
-- <newline>`; the trailing `many parseNewline` absorbs additional blank
-- lines (the formatter emits `"\n\n"`, so `many parseNewline` consumes
-- the second `\n`).
parseVersion : Parser (List Char)
parseVersion =
  parse versionFmt >>= λ v →
  many parseNewline >>= λ _ →
  pure v

-- ============================================================================
-- BS_ (bit timing)
-- ============================================================================

-- η-style wrap: `parse bitTimingFmt` consumes `"BS_:" <opaque-tail>
-- <newline>`; the trailing `many parseNewline` absorbs the second `\n`
-- the formatter emits + any additional blank lines.
parseBitTiming : Parser ⊤
parseBitTiming =
  parse bitTimingFmt >>= λ _ →
  many parseNewline >>= λ _ →
  pure tt

-- ============================================================================
-- NS_ (namespace / symbol set)
-- ============================================================================

-- η-style wrap: `parse nsFmt` captures the entire 27-newline block —
-- header `"NS_ :\n"` + body `(many nsLineFmt)` over the canonical
-- 26-element list (25 keyword lines + 1 trailing blank).  No extra
-- `many parseNewline` after — the body's final element handles the
-- trailing blank line.
parseNamespace : Parser ⊤
parseNamespace =
  parse nsFmt >>= λ _ →
  pure tt
