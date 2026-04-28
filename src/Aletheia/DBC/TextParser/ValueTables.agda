{-# OPTIONS --safe --without-K #-}

-- Value-table parsers for the DBC text format (Phase B.3.c.4).
--
-- Grammar slice covered (BNF section C from `Aletheia.DBC.TextParser`):
--   val-table    ::= "VAL_TABLE_" ws identifier (ws nat ws string-lit)*
--                    ws? ";" newline
--   value-desc   ::= "VAL_" ws nat ws identifier (ws nat ws string-lit)*
--                    ws? ";" newline
--
-- Scope note — `VAL_` parsed but discarded:
--   The Agda `DBCSignal` record has no `valueDescriptions` field; there is
--   nowhere to store per-signal enum labels.  This matches the existing
--   Python pipeline (cantools → `dbc_to_json` also drops `signal.choices`;
--   see `python/aletheia/dbc_converter.py` — `value_tables.items()` is
--   processed, `signal.choices` is not).  The line is still parsed for
--   syntactic correctness so ill-formed `VAL_` lines reject the whole
--   file, and so a future B.3.g extension that promotes
--   `DBCSignal.valueDescriptions` end-to-end can flip this parser to
--   return the entry list without re-deriving the grammar.
--
-- Prefix ambiguity — `VAL_` is a prefix of `VAL_TABLE_`, so the obvious
-- `parseValueDescription <|> parseValueTable` ordering would succeed on
-- the `VAL_` branch before the parser ever tries `VAL_TABLE_`.  We try
-- the longer-prefix branch first, and the lexer's backtracking `<|>`
-- restores input on the `string "VAL_TABLE_"` mismatch so `parseValueDescription`
-- can still match.  (Cf. `parseMuxMarker` ordering in `TextParser.Topology`.)
--
-- Zero-entry handling: `VAL_TABLE_ Empty ;` is syntactically valid — the
-- `many parseValueEntry` combinator accepts zero entries.  Corpus-never-
-- seen but grammar-allowed; `emitValueTable` mirrors this on the output
-- side so B.3.d composes.
module Aletheia.DBC.TextParser.ValueTables where

open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open import Data.Char using (Char)
open import Data.Unit using (⊤; tt)

open import Aletheia.Parser.Combinators using
  (Parser; pure; _>>=_; _<|>_; _*>_;
   char; string; many)
open import Aletheia.DBC.TextParser.Lexer using
  (parseIdentifier; parseStringLit; parseWS; parseWSOpt; parseNewline;
   parseNatural)
open import Aletheia.DBC.TextParser.Format using (parse)
open import Aletheia.DBC.TextParser.Format.ValueTable using (ValueTable-format)

open import Aletheia.DBC.Types using (ValueTable)

-- ============================================================================
-- ENTRY PARSER
-- ============================================================================

-- One `ws nat ws string-lit` pair.  Called under `many`, which terminates
-- when the next character is the `;` terminator (the mandatory leading
-- `parseWS` fails on `;`, so the repetition stops cleanly without a
-- separator combinator).
-- Post-3d.4 + JSON-mirror: `parseStringLit : Parser (List Char)` and
-- `ValueTable.entries : List (ℕ × List Char)`, so the entry pair carries
-- raw chars throughout.
parseValueEntry : Parser (ℕ × List Char)
parseValueEntry = do
  _ ← parseWS
  v ← parseNatural
  _ ← parseWS
  desc ← parseStringLit
  pure (v , desc)

-- ============================================================================
-- VAL_TABLE_ LINE
-- ============================================================================

-- Post 3d.5.c-η/3d.5.d: derived from the Format DSL `ValueTable-format`,
-- so the universal `roundtrip` theorem in `Format.agda` discharges the
-- parse-after-emit law via a single `EmitsOK` certificate (see
-- `Properties/ValueTables/ValueTable.parseValueTable-roundtrip`).  The
-- DSL handles `"VAL_TABLE_" ws identifier entries ws? ";" newline`
-- (production-permissive whitespace via `withWS`/`withWSCanonOne`,
-- both LF and CR-LF newline via `newlineFmt`).  The trailing `many
-- parseNewline` consumes optional blank lines between tables, mirroring
-- η's `parseSignalLine` vs `parseMessage` split (line consumes one
-- terminator, block-level wrapper absorbs blanks).
parseValueTable : Parser ValueTable
parseValueTable = do
  vt ← parse ValueTable-format
  _ ← many parseNewline
  pure vt

-- ============================================================================
-- VAL_ LINE (parsed, discarded)
-- ============================================================================

-- `"VAL_" ws nat ws identifier entries ws? ";" newline` + trailing blanks.
-- Returns `⊤` — see module header for why the entries aren't retained.
-- The `nat` is the CAN ID of the owning message; `identifier` is the
-- signal name.  Both are parsed but dropped.
parseValueDescription : Parser ⊤
parseValueDescription = do
  _ ← string "VAL_"
  _ ← parseWS
  _ ← parseNatural    -- message CAN ID, discarded
  _ ← parseWS
  _ ← parseIdentifier -- signal name, discarded
  _ ← many parseValueEntry
  _ ← parseWSOpt
  _ ← char ';'
  _ ← parseNewline
  _ ← many parseNewline
  pure tt

-- ============================================================================
-- UNION PARSER
-- ============================================================================

-- One VAL_* line — either a table (retained) or a description (dropped).
-- Caller uses `many parseValueLine` and filters the `Maybe` to collect
-- tables; the `nothing` cases correspond to absorbed-but-dropped VAL_
-- lines, which keeps a single `many` loop driving both productions in a
-- stream-preserving order.
parseValueLine : Parser (Maybe ValueTable)
parseValueLine =
  (parseValueTable >>= λ vt → pure (just vt)) <|>
  (parseValueDescription *> pure nothing)
