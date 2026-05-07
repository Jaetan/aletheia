{-# OPTIONS --safe --without-K #-}

-- Value-table parsers for the DBC text format (Track B.3.c.4).
--
-- Grammar slice covered (BNF section C from `Aletheia.DBC.TextParser`):
--   val-table    ::= "VAL_TABLE_" ws identifier (ws nat ws string-lit)*
--                    ws? ";" newline
--   value-desc   ::= "VAL_" ws nat ws identifier (ws nat ws string-lit)*
--                    ws? ";" newline
--
-- Track E.4 — `VAL_` payload promotion:
--   `parseValueDescription` now yields a `RawValueDesc` carrying the
--   decoded `CANId`, the signal `Identifier`, and the `(value, label)`
--   entries.  Earlier the parser dropped to `⊤` because `DBCSignal` had
--   no place to store per-signal enum labels; with E.1's
--   `DBCSignal.valueDescriptions` field, the value can now be threaded
--   through `TopStmt.TSValueDesc → TopStmtTyped.TVD → attachValueDescs`
--   to land on the owning signal's record.
--
--   The CAN-ID decoding via `buildCANId` is partial: a syntactically-
--   valid `VAL_` line whose ℕ falls outside the standard/extended ID
--   range now rejects the whole file (mirrors `parseMessage`'s stance
--   on `BO_` lines).  All corpus fixtures use IDs that decode cleanly.
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

open import Data.List using (List)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open import Data.Char using (Char)

open import Aletheia.Parser.Combinators using
  (Parser; pure; _>>=_; fail; many)
open import Aletheia.DBC.TextParser.Lexer using
  (parseStringLit; parseWS; parseNewline; parseNatural)
open import Aletheia.DBC.TextParser.Format using (parse)
open import Aletheia.DBC.TextParser.Format.ValueTable using (ValueTable-format)
open import Aletheia.DBC.TextParser.Format.ValueDescription using
  (ValueDescription-format)
open import Aletheia.DBC.TextParser.Topology.Foundations using (buildCANId)

open import Aletheia.DBC.Identifier using (Identifier)
open import Aletheia.CAN.Frame using (CANId)
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
-- VAL_ LINE — RawValueDesc payload
-- ============================================================================

-- `RawValueDesc` is defined in `Aletheia.DBC.Types` so `DBC.unresolved
-- ValueDescs : List RawValueDesc` (Plan B, Track E.8) does not induce a
-- cycle.  Re-exported here so existing parser-side imports keep working
-- without an upstream rewrite.
open import Aletheia.DBC.Types using (RawValueDesc; mkRawValueDesc) public

-- `buildResultP` dispatches the `Maybe CANId` directly via constructor
-- pattern match (NOT `with`-on-Maybe).  Per
-- `feedback_expose_scrutinee_for_external_rewrite.md` and
-- `feedback_with_abstraction_traps.md`, this lets the slim roundtrip
-- proof reduce externally via `cong (buildResultP _)
-- (buildCANId-rawCanIdℕ canId)` without a proof-side `with` — top-level
-- `with` hides the scrutinee inside the elaborated aux.
--
-- Hoisted to top-level (out of `where`) so the slim roundtrip in
-- `Properties.ValueTables.ValueDesc` can reference the exact function
-- `parseValueDescription`'s bind chain calls.  A where-bound version
-- has different identity from any external mirror; `bind-just-step`
-- needs the SAME function on both sides of its equation.
buildResultP : Maybe CANId → Identifier → List (ℕ × List Char)
             → Parser RawValueDesc
buildResultP nothing       _    _   = fail
buildResultP (just canId)  sigId vds = pure (mkRawValueDesc canId sigId vds)

-- `"VAL_" ws nat ws identifier entries ws? ";" newline` + trailing blanks.
-- The `nat` decodes via `buildCANId`; out-of-range IDs (≥ 2^32, or above
-- the standard/extended max) reject the whole file, mirroring
-- `parseMessage`'s stance on `BO_` headers.
--
-- Track E.5β — derived from the Format DSL `ValueDescription-format`
-- (parallels `parseValueTable`'s shape).  The DSL universal in
-- `Format.ValueDescription` discharges the line-shape roundtrip up to
-- the trailing newline; the wrapper here consumes optional blank lines
-- via `many parseNewline` and decodes the raw CAN ID via `buildResultP`.
parseValueDescription : Parser RawValueDesc
parseValueDescription = do
  triple ← parse ValueDescription-format
  _      ← many parseNewline
  buildResultP (buildCANId (proj₁ triple))
               (proj₁ (proj₂ triple))
               (proj₂ (proj₂ triple))
  where
    open import Data.Product using (proj₁; proj₂)
