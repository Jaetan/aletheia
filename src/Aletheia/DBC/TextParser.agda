{-# OPTIONS --safe --without-K #-}

-- DBC (Database CAN) text format parser — skeleton (Phase B.3.b).
--
-- Purpose: Parse the canonical ASCII `.dbc` text format directly in Agda,
-- producing the `DBC` structural shape already defined in `Aletheia.DBC.Types`.
-- Replaces the R17-deferred cantools-backed `dbc_to_json` pipeline; together
-- with `Aletheia.DBC.TextFormatter` it closes `parseText ∘ formatText ≡ id`
-- at the DBC value level (see companion Properties module for the
-- semantic-equivalence caveat — byte-identity of the text itself is NOT a
-- target).
--
-- Role: Phase B.3.c wires concrete combinator-based parsers into this
-- module; B.3.d proves the structural roundtrip; B.3.e exposes a JSON
-- protocol command; B.3.f/g retire the cantools dependency.
--
-- Skeleton state (B.3.b):
--   * Grammar spec captured below as BNF, keyed by the PARITY_PLAN.md §B.3
--     construct inventory so reviewers can diff grammar-vs-inventory in
--     review rounds.
--   * Local error ADT carries exactly one constructor; per-construct
--     refinements land in B.3.c as each grammar category is implemented.
--   * `parseText` is wired as an unimplemented stub; `Aletheia.Main` is
--     intentionally NOT updated — the skeleton stays out of the runtime
--     path until B.3.e.
--
-- Design notes (forward to B.3.c):
--   * `Aletheia.Parser.Combinators` already provides the structural-
--     recursion harness used here (Parser combinators over `List Char`).
--   * Error taxonomy is kept local to this module instead of extending
--     `Aletheia.Error.ParseError`, because DBC text errors don't overlap
--     with the JSON parser vocabulary and widening the shared ADT would
--     couple two unrelated evolution streams.
module Aletheia.DBC.TextParser where

open import Data.String using (String)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Aletheia.DBC.Types using (DBC)

-- ============================================================================
-- GRAMMAR (BNF)
-- ============================================================================
--
-- Whitespace (` `, `\t`) between lexemes on the same line is permissive;
-- newlines terminate top-level statements.  Sections below are keyed to the
-- PARITY_PLAN.md §B.3 construct inventory categories — a 1:1 review audit
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

-- Local error ADT for DBC-text parsing.  Kept separate from
-- `Aletheia.Error.ParseError` (the JSON-protocol parser error) because the
-- two vocabularies do not overlap; each can evolve independently.  B.3.c
-- adds per-construct constructors (e.g. `ExpectedSGKeyword`,
-- `InvalidByteOrderDigit`, `UnterminatedStringLiteral`) as grammar
-- categories get wired.
data DBCTextParseError : Set where
  UnimplementedConstruct : String → DBCTextParseError

-- ============================================================================
-- ENTRY POINT
-- ============================================================================

-- Skeleton stub.  Returns a structured error until B.3.c begins wiring
-- Aletheia.Parser.Combinators-based parsers per grammar category.
parseText : String → DBCTextParseError ⊎ DBC
parseText _ = inj₁ (UnimplementedConstruct "B.3.c: parseText not yet implemented")
