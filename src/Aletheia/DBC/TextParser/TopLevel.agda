{-# OPTIONS --without-K #-}

-- Top-level aggregator for the DBC text format (Phase B.3.c.k).
--
-- Wires the per-construct parsers from B.3.c.1–B.3.c.9 into a single
-- `parseDBCText` combinator that consumes the whole file.  The entry
-- point `Aletheia.DBC.TextParser.parseText` drives this combinator and
-- folds the result into a `DBC` record; see that module for the error
-- shaping layer.
--
-- Grammar slice covered (BNF section composition — see `Aletheia.DBC.
-- TextParser` for the full grammar):
--   dbc-file     ::= version ns bs bu-section top-stmt*
--   top-stmt     ::= val-table | message | bo-tx-bu | env-var | comment
--                  | attribute-line | value-desc | sig-group | sig-valtype
--                  | sig-mul-val
--   bo-tx-bu     ::= "BO_TX_BU_" ws nat ws? ":" ws? identifier
--                    ("," ws? identifier)* ws? ";" newline
--
-- `BO_TX_BU_` arrives here instead of in `TextParser.Topology` because it
-- lives at the top level (sibling of `BO_`), not nested under a message.
-- It is drop-parsed for now — the B.3.b skeleton leaves `senders = []` on
-- `parseMessage`'s output (see `TextParser.Topology` lines 45, 348), and
-- B.3.c.k does not promote senders end-to-end yet.  Wire-syntactic
-- recognition still fires so malformed lines reject the whole file,
-- matching the parse-and-drop stance used for `VAL_` / `SIG_VALTYPE_` /
-- `SG_MUL_VAL_`.
--
-- Dispatch ordering — longest-first where prefixes collide:
--   1. Attribute family via `parseAttrLine` (which itself is longest-
--      first internally: `BA_DEF_REL_` > `BA_DEF_DEF_` > `BA_DEF_` >
--      `BA_REL_` > `BA_`).
--   2. `VAL_TABLE_` before `VAL_`.
--   3. `BO_TX_BU_` before `BO_`.
--   4. `SIG_GROUP_` / `SIG_VALTYPE_` / `SG_MUL_VAL_` — no top-level
--      prefix collisions (first characters diverge at position 1 or 3).
--      Inner `SG_` under a `BO_` block is parsed by `parseMessage`'s
--      `many parseSignalLine`, never by the top-level dispatcher.
--   5. `EV_`, `CM_` — prefix-disjoint from everything else.
--
-- Prefix-collision backtracking discipline: each inner `parseFoo` opens
-- with `string "KEYWORD"`, and the combinator's `<|>` restores input on
-- `nothing`.  So `parseMessage` on `BO_TX_BU_ ...` input matches
-- `string "BO_"` then fails on `parseWS` (next char `T`, not a space);
-- the backtracking `<|>` returns input to the start and dispatch falls
-- through to the next alternative.  This is the same discipline used
-- inside `parseAttrLine` today.
--
-- `TopStmt` projection constraints (enforced by the drop-parsers):
--   * Every parsed `BO_TX_BU_` line collapses to `TSBOTxBu`; the
--     `senders` field on every `DBCMessage` stays `[]`.
--   * Every parsed `SG_MUL_VAL_` line collapses to `TSSigMulVal`; every
--     `DBCSignal.presence` in the output is either `Always` or
--     `When _ (v ∷ [])` (single-value selector).
--   * `VAL_` / `SIG_VALTYPE_` collapse to `TSValueDesc` / `TSSigValType`;
--     no per-signal enum labels or float-width tags survive.
-- These match the existing Python pipeline's structural `DbcDefinition`
-- — the B.3.d roundtrip proof composes at that projection level.
module Aletheia.DBC.TextParser.TopLevel where

open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_)
open import Data.String using (String)
open import Data.Unit using (⊤; tt)

open import Aletheia.Parser.Combinators using
  (Parser; pure; _>>=_; _<|>_; _*>_;
   char; string; many)
open import Aletheia.DBC.TextParser.Lexer using
  (parseIdentifier; parseWS; parseWSOpt; parseNewline;
   parseNatural)
open import Aletheia.DBC.TextParser.Preamble using
  (parseVersion; parseNamespace; parseBitTiming)
open import Aletheia.DBC.TextParser.Topology using
  (parseBU; parseMessage)
open import Aletheia.DBC.TextParser.ValueTables using
  (parseValueTable; parseValueDescription)
open import Aletheia.DBC.TextParser.Attributes using
  (RawDBCAttribute; parseAttrLine)
open import Aletheia.DBC.TextParser.Comments using
  (parseComment)
open import Aletheia.DBC.TextParser.SignalGroups using
  (parseSignalGroup)
open import Aletheia.DBC.TextParser.ValueTypes using
  (parseSigValType)
open import Aletheia.DBC.TextParser.ExtendedMux using
  (parseSigMulVal)
open import Aletheia.DBC.TextParser.EnvVars using
  (parseEnvVar)

open import Aletheia.DBC.Types using
  (DBCMessage; ValueTable; EnvironmentVar; DBCComment; SignalGroup; Node)

-- ============================================================================
-- BO_TX_BU_ DROP PARSER
-- ============================================================================

-- `BO_TX_BU_ ws nat ws? ":" ws? identifier ("," ws? identifier)* ws? ";"
--  newline` + trailing blank-line tolerance via `many parseNewline`.
--
-- Scope — parsed but discarded: `DBCMessage.senders` stays `[]` on the
-- message produced by `parseMessage` (see `TextParser.Topology` line 348).
-- Promoting the sender list requires cross-line coordination with the
-- message table (match by CAN ID), which is a separate future sub-commit.
parseBOTxBu : Parser ⊤
parseBOTxBu = do
  _ ← string "BO_TX_BU_"
  _ ← parseWS
  _ ← parseNatural       -- owning message's CAN ID, discarded
  _ ← parseWSOpt
  _ ← char ':'
  _ ← parseWSOpt
  _ ← parseIdentifier    -- first sender, discarded
  _ ← many (char ',' *> parseWSOpt *> parseIdentifier)
  _ ← parseWSOpt
  _ ← char ';'
  _ ← parseNewline
  _ ← many parseNewline
  pure tt

-- ============================================================================
-- TOP-STATEMENT SUM
-- ============================================================================

-- One top-level DBC statement as parsed from the input.  Payload
-- constructors carry the per-construct parser's output; drop
-- constructors (`TSBOTxBu` / `TSValueDesc` / `TSSigValType` /
-- `TSSigMulVal`) carry no payload — they mark presence of a
-- syntactically-valid but structurally-dropped line so the refinement
-- layer can skip them without re-parsing.
data TopStmt : Set where
  TSValueTable  : ValueTable      → TopStmt
  TSMessage     : DBCMessage      → TopStmt
  TSBOTxBu      :                   TopStmt
  TSEnvVar      : EnvironmentVar  → TopStmt
  TSComment     : DBCComment      → TopStmt
  TSAttribute   : RawDBCAttribute → TopStmt
  TSValueDesc   :                   TopStmt
  TSSignalGroup : SignalGroup     → TopStmt
  TSSigValType  :                   TopStmt
  TSSigMulVal   :                   TopStmt

-- ============================================================================
-- TOP-STATEMENT DISPATCH
-- ============================================================================

-- Try each per-construct parser in longest-first order where prefixes
-- collide.  See module header for the full ordering rationale.
parseTopStmt : Parser TopStmt
parseTopStmt =
  (parseAttrLine         >>= λ a  → pure (TSAttribute a))     <|>
  (parseValueTable       >>= λ vt → pure (TSValueTable vt))   <|>
  (parseValueDescription *> pure TSValueDesc)                 <|>
  (parseBOTxBu           *> pure TSBOTxBu)                    <|>
  (parseMessage          >>= λ m  → pure (TSMessage m))       <|>
  (parseSignalGroup      >>= λ g  → pure (TSSignalGroup g))   <|>
  (parseSigValType       *> pure TSSigValType)                <|>
  (parseSigMulVal        *> pure TSSigMulVal)                 <|>
  (parseEnvVar           >>= λ e  → pure (TSEnvVar e))        <|>
  (parseComment          >>= λ c  → pure (TSComment c))

-- ============================================================================
-- PARTITION INTO PER-FIELD BUCKETS
-- ============================================================================

-- Per-field buckets used by `parseText` to assemble the final `DBC`
-- record.  Wire order is preserved by right-cons insertion in
-- `partitionTopStmts`; `rawAttributes` is fed to `refineAttributes` by
-- the caller before becoming `DBC.attributes`.
record CollectedTop : Set where
  constructor mkCollectedTop
  field
    messages        : List DBCMessage
    valueTables     : List ValueTable
    environmentVars : List EnvironmentVar
    comments        : List DBCComment
    rawAttributes   : List RawDBCAttribute
    signalGroups    : List SignalGroup

emptyCollected : CollectedTop
emptyCollected = mkCollectedTop [] [] [] [] [] []

-- Cons one `TopStmt` onto its matching bucket.  Drop constructors pass
-- the accumulator through unchanged.
consTop : TopStmt → CollectedTop → CollectedTop
consTop (TSValueTable vt)  c =
  record c { valueTables     = vt ∷ CollectedTop.valueTables     c }
consTop (TSMessage m)      c =
  record c { messages        = m  ∷ CollectedTop.messages        c }
consTop TSBOTxBu           c = c
consTop (TSEnvVar e)       c =
  record c { environmentVars = e  ∷ CollectedTop.environmentVars c }
consTop (TSComment cm)     c =
  record c { comments        = cm ∷ CollectedTop.comments        c }
consTop (TSAttribute a)    c =
  record c { rawAttributes   = a  ∷ CollectedTop.rawAttributes   c }
consTop TSValueDesc        c = c
consTop (TSSignalGroup sg) c =
  record c { signalGroups    = sg ∷ CollectedTop.signalGroups    c }
consTop TSSigValType       c = c
consTop TSSigMulVal        c = c

-- Right-fold: each statement is consed onto the tail's accumulator, so
-- wire order is preserved (not reversed) across all buckets.
partitionTopStmts : List TopStmt → CollectedTop
partitionTopStmts [] = emptyCollected
partitionTopStmts (s ∷ rest) = consTop s (partitionTopStmts rest)

-- ============================================================================
-- WHOLE-FILE PARSER
-- ============================================================================

-- Parse the entire DBC file.  NS_/BS_ have no structural payload (see
-- `TextParser.Preamble` — cantools drops them too); the BU_ node list
-- and the trailing top-statement list are both kept.
parseDBCText : Parser (String × List Node × List TopStmt)
parseDBCText = do
  ver   ← parseVersion
  _     ← parseNamespace
  _     ← parseBitTiming
  nodes ← parseBU
  stmts ← many parseTopStmt
  pure (ver , nodes , stmts)
