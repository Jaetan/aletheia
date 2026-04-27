{-# OPTIONS --safe --without-K #-}

-- Extended-multiplex range parser for the DBC text format (Phase B.3.c.8).
--
-- Grammar slice covered (BNF section F from `Aletheia.DBC.TextParser`):
--   sig-mul-val  ::= "SG_MUL_VAL_" ws nat ws identifier ws identifier ws
--                    mux-range ("," ws? mux-range)* ws? ";" newline
--   mux-range    ::= nat "-" nat
--
-- Scope note — `SG_MUL_VAL_` parsed but discarded (for now):
--   The Agda `SignalPresence` already supports multi-value selectors
--   (`When multiplexor (values : List⁺ ℕ)`), and so the core types are
--   ready to carry an extended-mux selector set.  But materialising
--   those values from a `SG_MUL_VAL_` line requires *cross-line*
--   coordination: the line references a (CAN-ID, multiplexor-name,
--   signal-name) triple that has to be matched back to a
--   `RawSignal` / `DBCSignal` captured during `BO_` block parsing —
--   which is not the shape `TextParser.Topology.resolveSignalList`
--   supports today.  That integration is a separate downstream
--   sub-commit; see the forward-reference comments in
--   `TextParser.Topology` (lines 39 / 242) and `TextFormatter.Topology`
--   (lines 28–31).
--
--   For B.3.c.8 the line is parsed for syntactic correctness only, so
--   ill-formed `SG_MUL_VAL_` lines reject the whole file.  Mirrors the
--   parse-and-drop convention of `VAL_` (`ValueTables.parseValueDescription`)
--   and `SIG_VALTYPE_` (`ValueTypes.parseSigValType`).
--
--   cantools parity: the Python pipeline at
--   `python/aletheia/dbc_converter.py` also does not surface multi-value
--   mux ranges on the structural `DbcDefinition` — the `DBCSignal.presence`
--   shape is always single-value after `dbc_to_json` today — so dropping
--   this line at parse time matches the existing Python / C++ / Go
--   binding observables.
--
-- Range separator — `("," ws? mux-range)*`:
--   The grammar allows optional whitespace after the comma but requires
--   the preceding `mux-range` to already have consumed its own boundary.
--   We split the recognizer into `parseMuxRange` (first range, no leading
--   separator) and `parseSubsequentMuxRange` (`,` + ws? + range), then
--   drive the repetition with `many`.  This mirrors
--   `TextFormatter.Attributes`'s comma-separated enum handling on the
--   emit side.
--
-- Range endpoint width:
--   `nat "-" nat` uses the unsigned-only `parseNatural` re-exported from
--   `Aletheia.Protocol.JSON.Parse` via `Lexer`.  `parseNatural` cannot
--   swallow a leading `-`, so the `"-"` separator is unambiguous — no
--   backtracking needed.
--
-- Longest-first dispatch (future top-level aggregator):
--   `SG_MUL_VAL_` shares the `SG_` prefix with the in-BO_ signal line
--   (`" SG_"` — note the leading indent) but diverges at position 3
--   (`_` before `MUL_` on the top-level line, `_` before the SG name
--   with no `M` after).  More importantly, the SG_ signal line is
--   parsed inside `parseMessage` under indentation, never at the top
--   level, so top-level aggregator dispatch only sees `SG_MUL_VAL_`
--   here.  No longest-first ordering required.
module Aletheia.DBC.TextParser.ExtendedMux where

open import Data.Unit using (⊤; tt)

open import Aletheia.Parser.Combinators using
  (Parser; pure; _>>=_;
   char; string; many)
open import Aletheia.DBC.TextParser.Lexer using
  (parseIdentifier; parseWS; parseWSOpt; parseNewline;
   parseNatural)

-- ============================================================================
-- MUX-RANGE PARSERS (parsed, discarded)
-- ============================================================================

-- Single `nat "-" nat` range.  Both endpoints are dropped — see module
-- header for why.  The `-` is a grammar-fixed literal, unambiguous
-- against `parseNatural` (unsigned-only).
parseMuxRange : Parser ⊤
parseMuxRange = do
  _ ← parseNatural   -- range lower bound, discarded
  _ ← char '-'
  _ ← parseNatural   -- range upper bound, discarded
  pure tt

-- `"," ws? mux-range` — each repeated range after the first.  Called
-- under `many`, which terminates when the next character is not `,`
-- (the `char ','` mismatch backtracks cleanly so the caller sees the
-- terminator).  Mirrors `parseValueEntry` in `TextParser.ValueTables`
-- in its "mandatory leading separator fails first" termination stance.
parseSubsequentMuxRange : Parser ⊤
parseSubsequentMuxRange = do
  _ ← char ','
  _ ← parseWSOpt
  parseMuxRange

-- ============================================================================
-- SG_MUL_VAL_ LINE (parsed, discarded)
-- ============================================================================

-- `"SG_MUL_VAL_" ws nat ws identifier ws identifier ws mux-range
-- ("," ws? mux-range)* ws? ";" newline` + trailing blank-line tolerance
-- via `many parseNewline`.  Returns `⊤`; see module header for the
-- cross-line-coordination deferral that keeps this a drop-parser.
--
-- Field order (all discarded):
--   nat         — owning message's CAN ID
--   identifier  — multiplexed signal name (the "child")
--   identifier  — multiplexor signal name (the "parent")
--   mux-range+  — one-or-more inclusive selector ranges
parseSigMulVal : Parser ⊤
parseSigMulVal = do
  _ ← string "SG_MUL_VAL_"
  _ ← parseWS
  _ ← parseNatural       -- message CAN ID, discarded
  _ ← parseWS
  _ ← parseIdentifier    -- multiplexed signal name, discarded
  _ ← parseWS
  _ ← parseIdentifier    -- multiplexor signal name, discarded
  _ ← parseWS
  _ ← parseMuxRange      -- first range, discarded
  _ ← many parseSubsequentMuxRange
  _ ← parseWSOpt
  _ ← char ';'
  _ ← parseNewline
  _ ← many parseNewline
  pure tt
