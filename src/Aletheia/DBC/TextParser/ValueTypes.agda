{-# OPTIONS --safe --without-K #-}

-- Signal value-type parser for the DBC text format (Phase B.3.c.8).
--
-- Grammar slice covered (BNF section F from `Aletheia.DBC.TextParser`):
--   sig-valtype  ::= "SIG_VALTYPE_" ws nat ws identifier ws? ":" ws
--                    ("1" | "2") ws? ";" newline
--
-- Scope note — `SIG_VALTYPE_` parsed but discarded:
--   The Agda `SignalDef` record (`Aletheia.CAN.Signal`) has no `valueType`
--   field; there is nowhere to store the float32/float64 discriminator.
--   The cantools-backed Python pipeline also drops this width flag — the
--   structural `DbcDefinition` seen by Python / C++ / Go never carries a
--   per-signal float-width tag.  Parsing it syntactically keeps
--   ill-formed `SIG_VALTYPE_` lines rejecting the whole file, and a
--   future extension that promotes the flag end-to-end can flip this
--   parser to return `(ℕ × String × Bool)` without re-deriving the
--   grammar.
--
-- Width-digit dispatch:
--   `("1" | "2")` is strictly a single ASCII digit — `1` = IEEE 754
--   float32, `2` = float64.  `0` (default integer signal) is encoded by
--   the absence of any `SIG_VALTYPE_` line, so no zero branch here.
--   Using `char '1' <|> char '2'` rather than `parseNatural` makes the
--   grammar violation (e.g. `SIG_VALTYPE_ ... : 3 ;`) reject at the
--   digit position instead of silently succeeding on a >9 number.
--
-- Longest-first dispatch (future top-level aggregator):
--   `SIG_VALTYPE_` and `SIG_GROUP_` (B.3.c.7) both begin `SIG_` but
--   diverge at position 4 (`V` vs `G`), so neither is a prefix of the
--   other and no longest-first ordering is required to distinguish
--   them.  No ambiguity with `SG_` either — `SIG_` vs `SG_` diverge at
--   position 1.
module Aletheia.DBC.TextParser.ValueTypes where

open import Data.Unit using (⊤; tt)

open import Aletheia.Parser.Combinators using
  (Parser; pure; _>>=_; _<|>_;
   char; string; many)
open import Aletheia.DBC.TextParser.Lexer using
  (parseIdentifier; parseWS; parseWSOpt; parseNewline;
   parseNatural)

-- ============================================================================
-- SIG_VALTYPE_ LINE (parsed, discarded)
-- ============================================================================

-- `"SIG_VALTYPE_" ws nat ws identifier ws? ":" ws ("1"|"2") ws? ";" newline`
-- + trailing blank-line tolerance via `many parseNewline` (matches the
-- VAL_ / CM_ / BA_* stance elsewhere in the family — the emitter never
-- produces blank lines between SIG_VALTYPE_ entries, but the parser
-- stays lenient for hand-written corpora).
--
-- Returns `⊤`; see module header for why the width flag isn't retained.
parseSigValType : Parser ⊤
parseSigValType = do
  _ ← string "SIG_VALTYPE_"
  _ ← parseWS
  _ ← parseNatural       -- message CAN ID, discarded
  _ ← parseWS
  _ ← parseIdentifier    -- signal name, discarded
  _ ← parseWSOpt
  _ ← char ':'
  _ ← parseWS
  _ ← char '1' <|> char '2'  -- float width, discarded
  _ ← parseWSOpt
  _ ← char ';'
  _ ← parseNewline
  _ ← many parseNewline
  pure tt
