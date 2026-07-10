-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- DBC (Database CAN) text format parser — entry point.
--
-- Purpose: Parse the canonical ASCII `.dbc` text format directly in Agda,
-- producing the `DBC` structural shape already defined in `Aletheia.DBC.Types`.
-- Replaces the earlier cantools-backed `dbc_to_json` pipeline; together
-- with `Aletheia.DBC.TextFormatter` it closes `parseText ∘ formatText ≡ id`
-- at the DBC value level (see companion Properties module for the
-- semantic-equivalence caveat — byte-identity of the text itself is NOT a
-- target).
--
-- Role: this module wires the concrete combinator-based parsers from
-- `TextParser.TopLevel` into a single `parseText : String → ⊎`.  The
-- structural roundtrip is proven separately, a JSON protocol command
-- exposes it, and the cantools dependency is retired.
--
-- Design notes:
--   * `Aletheia.Parser.Combinators` provides the structural-recursion
--     harness used here (Parser combinators over `List Char`).  String
--     input is funnelled through `Data.String.toList` exactly once.
--   * Error taxonomy stays local to this module instead of extending
--     `Aletheia.Error.ParseError` — the JSON parser's error vocabulary
--     does not overlap with DBC text, so widening the shared ADT would
--     couple two unrelated evolution streams.  The current constructors
--     cover the three distinguishable failure modes from
--     `runParserPartial` + `refineAttributes`:
--
--       * `ParseFailure`             — top-level combinator returned
--                                      `nothing` (wrong token / no
--                                      alternative matched).  The
--                                      combinators lose position info
--                                      on failure, so this is a 0-arg
--                                      constructor — reporting "which
--                                      byte failed" would require a
--                                      redesign of `Parser` to thread
--                                      the last-touched position out of
--                                      `nothing`, which is scoped for a
--                                      future refactor.
--       * `TrailingInput`            — parser succeeded but left bytes
--                                      on the tape.  Position of the
--                                      first unconsumed byte is carried
--                                      so callers can localise the
--                                      error; empty-tape success is
--                                      the ≡ id path.
--       * `AttributeRefinementFailed` — `refineAttributes` failed because
--                                      some default/assignment referenced
--                                      an unknown AttrDef or an
--                                      out-of-range ENUM index.  Carries
--                                      the offending attribute's name so
--                                      the error pinpoints which
--                                      `BA_DEF_` / `BA_DEF_DEF_` / `BA_` /
--                                      `BA_REL_` entry is at fault.
module Aletheia.DBC.TextParser where

open import Data.Char using (Char)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.String using (String; toList; fromList)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Aletheia.Parser.Combinators using
  (ParseResult; value; position; remaining;
   runParserPartial)
open import Aletheia.Parser.Position using (Position)

open import Aletheia.DBC.Types using
  (DBC; Node; DBCAttribute)

open import Aletheia.DBC.TextParser.TopLevel using
  (TopStmt; CollectedTop; partitionTopStmts; parseDBCText)
open import Aletheia.DBC.TextParser.Attributes using
  (refineAttributes)
open import Aletheia.DBC.TextParser.ValueDescriptions using
  (attachValueDescs; unresolvedRVDs)
open import Aletheia.DBC.TextParser.Senders using
  (attachSenders)

open import Aletheia.Error public using
  (DBCTextParseError; ParseFailure; TrailingInput; AttributeRefinementFailed)

-- ============================================================================
-- GRAMMAR (BNF)
-- ============================================================================
--
-- Whitespace (` `, `\t`) between lexemes on the same line is permissive;
-- newlines terminate top-level statements.  Sections below are keyed to the
-- construct-inventory categories — a 1:1 mapping
-- target so new inventory rows always get a grammar line.
--
-- A. Preamble
--   dbc-file     ::= version ns bs bu-section top-stmt*
--   version      ::= "VERSION" ws string-lit newline
--   ns           ::= "NS_" ws? ":" newline (blank-line | indent keyword newline)*
--   bs           ::= "BS_" ws? ":" (ws baud-rate-expr)? newline
--
-- B. Topology
--   bu-section   ::= "BU_" ws? ":" (ws identifier)* newline
--   message      ::= "BO_" ws nat ws identifier ws? ":" ws nat ws identifier newline
--                    (indent signal newline)*
--   signal       ::= "SG_" ws identifier (ws mux-indicator)? ws? ":" ws
--                    nat "|" nat "@" byte-order-digit sign ws
--                    "(" rational "," rational ")" ws
--                    "[" rational "|" rational "]" ws
--                    string-lit ws identifier ("," ws? identifier)*
--   mux-indicator ::= "M" | "m" nat | "m" nat "M"
--   byte-order-digit ::= "0" | "1"
--   sign         ::= "+" | "-"
--
-- C. Value descriptions
--   value-desc   ::= "VAL_" ws nat ws identifier (ws nat ws string-lit)* ws? ";" newline
--   value-table  ::= "VAL_TABLE_" ws identifier (ws nat ws string-lit)* ws? ";" newline
--
-- D. Attributes
--   attr-def     ::= "BA_DEF_" (ws attr-scope)? ws string-lit ws attr-type ws? ";" newline
--   attr-def-rel ::= "BA_DEF_REL_" ws rel-scope ws string-lit ws attr-type ws? ";" newline
--   attr-type    ::= "INT" ws int ws int
--                  | "FLOAT" ws rational ws rational
--                  | "STRING"
--                  | "ENUM" ws string-lit ("," ws? string-lit)*
--                  | "HEX" ws nat ws nat
--   attr-default ::= "BA_DEF_DEF_" ws string-lit ws attr-value ws? ";" newline
--   attr-assign  ::= "BA_" ws string-lit (ws attr-target)? ws attr-value ws? ";" newline
--   attr-rel     ::= "BA_REL_" ws string-lit ws rel-target ws attr-value ws? ";" newline
--   attr-scope   ::= "BU_" | "BO_" | "SG_" | "EV_"
--   rel-scope    ::= "BU_BO_REL_" | "BU_SG_REL_"
--   attr-target  ::= "BU_" ws identifier
--                  | "BO_" ws nat
--                  | "SG_" ws nat ws identifier
--                  | "EV_" ws identifier
--   rel-target   ::= "BU_BO_REL_" ws identifier ws nat
--                  | "BU_SG_REL_" ws identifier ws "SG_" ws nat ws identifier
--   attr-value   ::= string-lit | rational | int
--
-- E. Comments
--   comment      ::= "CM_" (ws comment-target)? ws string-lit ws? ";" newline
--   comment-target ::= "BU_" ws identifier
--                    | "BO_" ws nat
--                    | "SG_" ws nat ws identifier
--                    | "EV_" ws identifier
--
-- F. Signal grouping / value-typing / multiplex ranges
--   sig-group    ::= "SIG_GROUP_" ws nat ws identifier ws nat ws? ":"
--                    (ws identifier)* ws? ";" newline
--   sig-valtype  ::= "SIG_VALTYPE_" ws nat ws identifier ws? ":" ws
--                    ("1" | "2") ws? ";" newline
--   sig-mul-val  ::= "SG_MUL_VAL_" ws nat ws identifier ws identifier ws
--                    mux-range ("," ws? mux-range)* ws? ";" newline
--   mux-range    ::= nat "-" nat
--
-- G. Environment variables (EV_DATA_/ENVVAR_DATA_ declared only in NS_;
--    see corpus README known-divergences)
--   env-var      ::= "EV_" ws identifier ws? ":" ws ("0" | "1" | "2") ws
--                    "[" rational "|" rational "]" ws string-lit ws
--                    rational ws nat ws identifier ws identifier ws? ";"
--                    newline
--   -- Access-list shape follows cantools' `dbc.py` production (single
--   -- `access_type` WORD + single `access_node` WORD, no comma list).
--   -- Corpus example `... DUMMY_NODE_VECTOR0 Host;` confirms the
--   -- whitespace-separated single-node form.
--
-- H. Lexical primitives
--   identifier   ::= (letter | "_") (letter | digit | "_")*
--   string-lit   ::= '"' (any-char-but-quote | '""')* '"'
--   rational     ::= integer-lit ("." digit+)? (("e"|"E") integer-lit)?
--   integer-lit  ::= "-"? digit+
--   int          ::= integer-lit
--   nat          ::= digit+
--   ws           ::= (" " | "\t")+
--   indent       ::= ws
--   newline      ::= "\n" | "\r\n"
--   keyword      ::= identifier        -- used for NS_ continuation lines
--   baud-rate-expr ::= nat (":" nat "," nat)?
--
-- ============================================================================
-- ERROR TAXONOMY
-- ============================================================================

-- Error ADT for DBC-text parsing lives in `Aletheia.Error.DBCTextParseError`,
-- re-exported via the top-level `Error` sum so callers and the JSON
-- envelope share the same vocabulary as the JSON-protocol parser.

-- ============================================================================
-- ENTRY POINT
-- ============================================================================

-- Build a `DBC` record from parsed pieces.  Wire order across the
-- `List TopStmt` is preserved by `partitionTopStmts`; every bucket is
-- therefore in source order, matching the JSON pipeline's invariants.
-- `attributes` carries the refined (resolved-def-reference) list — the
-- raw two-stage split stays internal to the parser.
--
-- `messages` is post-`attachValueDescs`: the parser produces
-- messages with empty `valueDescriptions` on every signal (buildSignal
-- hardcodes `[]`); the refine pass distributes the parsed `RawValueDesc`s
-- (collected separately under `partitionTopStmts.rawValueDescs`) back
-- into the matching signals' `valueDescriptions` field.  The inverse-
-- bridge proof in `Properties.Aggregator.Refine.ValueDescriptions`
-- closes `attachValueDescs (collectFromMessages msgs) (map clearVdsMsg
-- msgs) ≡ msgs` under WF.  `collectFromMessages` is wired into the
-- formatter side; the interim `vds-empty` clauses were lifted and the
-- vacuous TVD arm replaced with a real derivation of
-- `All RawValueDescStop` from `Identifier.valid`.
buildDBC : List Char → List Node → CollectedTop → List DBCAttribute → DBC
buildDBC ver nodes c attrs = record
  { version              = ver
  ; messages             = attachSenders (CollectedTop.rawMsgSenders c)
                             (attachValueDescs (CollectedTop.rawValueDescs c)
                                               (CollectedTop.messages     c))
  ; signalGroups         = CollectedTop.signalGroups    c
  ; environmentVars      = CollectedTop.environmentVars c
  ; valueTables          = CollectedTop.valueTables     c
  ; nodes                = nodes
  ; comments             = CollectedTop.comments        c
  ; attributes           = attrs
  -- Unresolved RVDs are computed against the
  -- pre-attach `CollectedTop.messages` (the same list the resolved RVDs
  -- match against).  Under WF (`unresolvedRVDs-on-collected`) this list
  -- is `[]` for any DBC built from `formatText`, so the universal proof
  -- closes via `WellFormedTextDBCAgg.unresolved-empty`.
  ; unresolvedValueDescs = unresolvedRVDs (CollectedTop.rawValueDescs c)
                                          (CollectedTop.messages       c)
  }

-- Shape the `runParserPartial` result into the public error ⊎ DBC
-- taxonomy.  Broken out from `parseText` so the three-case dispatch
-- does not nest inside the `toList` call — easier to read, and the
-- refinement step is isolated from the outer runner.
finalizeParse : Position × Maybe (ParseResult (List Char × List Node × List TopStmt))
              → DBCTextParseError ⊎ DBC
finalizeParse (w , nothing) = inj₁ (ParseFailure w)
finalizeParse (w , just res) with remaining res
... | (_ ∷ _) = inj₁ (TrailingInput w (position res))
... | []      with value res
...   | (ver , nodes , stmts) with partitionTopStmts stmts
...     | collected with refineAttributes (CollectedTop.rawAttributes collected)
...       | inj₁ (cause , bad) = inj₁ (AttributeRefinementFailed cause (fromList bad))
...       | inj₂ attrs         = inj₂ (buildDBC ver nodes collected attrs)

-- Parse a DBC text image given as a `List Char`.  The parser already
-- operates on `List Char` throughout — `runParserPartial` takes one — so
-- the only `String` site is the public `parseText` boundary, which
-- bridges via `Data.String.toList`.  The universal roundtrip proof
-- composes `parseTextChars (formatChars d) ≡ inj₂ d` (internal,
-- 100% `--safe`) with the `Substrate/Unsafe` bridging axioms.
--
-- Success requires:
--   1. `parseDBCText` consumes every byte of input (no trailing slop).
--   2. `refineAttributes` resolves every BA_DEF_DEF_ / BA_ / BA_REL_
--      against the input's AttrDef list.
-- Failure of either surfaces as the matching `DBCTextParseError` case;
-- the refinement-fail note describes the class of issue, not which
-- specific attribute is broken (the refinement pass currently does not
-- thread that info out — see module header).
parseTextChars : List Char → DBCTextParseError ⊎ DBC
parseTextChars cs = finalizeParse (runParserPartial parseDBCText cs)

-- Parse a DBC text image.  See `parseTextChars` for the `List Char`
-- entry point used by the roundtrip proofs.
parseText : String → DBCTextParseError ⊎ DBC
parseText s = parseTextChars (toList s)
