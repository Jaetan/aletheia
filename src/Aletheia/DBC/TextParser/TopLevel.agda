-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Top-level aggregator for the DBC text format (Track B.3.c.k).
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
-- It is captured as a `RawMsgSenders` (A.2, via the Format DSL `MsgSenders-
-- format`), bucketed by `consTop (TSBOTxBu rms)` into `CollectedTop.
-- rawMsgSenders`, and stitched back into `DBCMessage.senders` by
-- `attachSenders` at `buildDBC` (keyed by CAN ID).  `parseMessage` leaves
-- `senders = []`; the BO_TX_BU_ section restores it — the message-level
-- analogue of how VAL_ restores per-signal `valueDescriptions`.
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
--   * Every parsed `BO_TX_BU_` line carries a `RawMsgSenders` via
--     `TSBOTxBu` (A.2); `partitionTopStmts` buckets it into `rawMsgSenders`
--     and `buildDBC`'s `attachSenders` distributes it onto the owning
--     message's `DBCMessage.senders` (keyed by CAN ID).
--   * Every parsed `SG_MUL_VAL_` line collapses to `TSSigMulVal`; every
--     `DBCSignal.presence` in the output is either `Always` or
--     `When _ (v ∷ [])` (single-value selector).
--   * `SIG_VALTYPE_` collapses to `TSSigValType`; no float-width tags
--     survive.
--   * `VAL_` carries a `RawValueDesc` payload via `TSValueDesc` (Phase
--     E.4); E.5's refine pass attaches it to the owning signal's
--     `DBCSignal.valueDescriptions`.
-- These match the existing Python pipeline's structural `DbcDefinition`
-- — the B.3.d roundtrip proof composes at that projection level.
module Aletheia.DBC.TextParser.TopLevel where

open import Data.Char using (Char)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤)

open import Aletheia.Parser.Combinators using
  (Parser; pure; _>>=_; _<|>_; _*>_;
   fail; many)
open import Aletheia.DBC.TextParser.Lexer using
  (parseNewline)
open import Aletheia.CAN.Frame using (CANId)
open import Aletheia.DBC.Identifier using (Identifier)
open import Aletheia.DBC.TextParser.Format using (parse)
open import Aletheia.DBC.TextParser.Format.MessageSenders using (MsgSenders-format)
open import Aletheia.DBC.TextParser.Topology.Foundations using (buildCANId)
open import Aletheia.DBC.TextParser.Senders using (RawMsgSenders; mkRawMsgSenders)
open import Aletheia.DBC.TextParser.Preamble using
  (parseVersion; parseNamespace; parseBitTiming)
open import Aletheia.DBC.TextParser.Topology using
  (parseBU; parseMessage)
open import Aletheia.DBC.TextParser.ValueTables using
  (parseValueTable; parseValueDescription; RawValueDesc)
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
-- BO_TX_BU_ LINE PARSER
-- ============================================================================

-- `BO_TX_BU_ <id> : n1,n2,…;` + trailing blank-line tolerance.  Derived from
-- the Format DSL `MsgSenders-format` (parallels `parseValueDescription`): the
-- DSL parses the raw `(ℕ , Identifier , List Identifier)` line shape, and the
-- wrapper decodes the CAN ID via `buildCANId` (out-of-range IDs reject the
-- whole file, mirroring `parseMessage` / `parseValueDescription`) and consumes
-- optional trailing blank lines.
--
-- The captured `RawMsgSenders` is bucketed by `consTop` into `CollectedTop.
-- rawMsgSenders` and stitched into `DBCMessage.senders` by `attachSenders`
-- at `buildDBC` (keyed by CAN ID).
buildSendersResult : Maybe CANId → List Identifier → Parser RawMsgSenders
buildSendersResult nothing      _    = fail
buildSendersResult (just canId) snds = pure (mkRawMsgSenders canId snds)

parseBOTxBu : Parser RawMsgSenders
parseBOTxBu = do
  triple ← parse MsgSenders-format
  _      ← many parseNewline
  buildSendersResult (buildCANId (proj₁ triple))
                     (proj₁ (proj₂ triple) ∷ proj₂ (proj₂ triple))

-- ============================================================================
-- TOP-STATEMENT SUM
-- ============================================================================

-- One top-level DBC statement as parsed from the input.  Payload
-- constructors carry the per-construct parser's output; the remaining drop
-- constructors (`TSSigValType` / `TSSigMulVal`) carry no payload — they mark
-- presence of a syntactically-valid but structurally-dropped line so the
-- refinement layer can skip them without re-parsing.  `TSValueDesc` carries
-- `RawValueDesc` post-E.4; E.5's refine pass routes it into `DBCSignal.
-- valueDescriptions`.  `TSBOTxBu` carries `RawMsgSenders` (A.2); its refine
-- pass (`attachSenders`) routes it into `DBCMessage.senders` once wired.
data TopStmt : Set where
  TSValueTable  : ValueTable      → TopStmt
  TSMessage     : DBCMessage      → TopStmt
  TSBOTxBu      : RawMsgSenders   → TopStmt
  TSEnvVar      : EnvironmentVar  → TopStmt
  TSComment     : DBCComment      → TopStmt
  TSAttribute   : RawDBCAttribute → TopStmt
  TSValueDesc   : RawValueDesc    → TopStmt
  TSSignalGroup : SignalGroup     → TopStmt
  TSSigValType  :                   TopStmt
  TSSigMulVal   :                   TopStmt

-- ============================================================================
-- TOP-STATEMENT DISPATCH
-- ============================================================================
--
-- Head-character dispatch.  Each top-level construct begins with a unique
-- 1- or 2-char keyword prefix:
--
--     'V'      → VAL_TABLE_   / VAL_         (parseValueTable / parseValueDescription)
--     'B' 'A'  → BA_DEF_*     / BA_*         (parseAttrLine — its own internal chain)
--     'B' 'O'  → BO_TX_BU_    / BO_<digit>   (parseBOTxBu    / parseMessage)
--     'S' 'I'  → SIG_VALTYPE_ / SIG_GROUP_   (parseSigValType / parseSignalGroup)
--     'S' 'G'  → SG_MUL_VAL_                 (parseSigMulVal)
--     'E' 'V'  → EV_                         (parseEnvVar)
--     'C' 'M'  → CM_                         (parseComment)
--     other    → fail
--
-- Semantically equivalent to the prior 10-way `<|>` chain in longest-first
-- prefix order: every cross-class comparison fails on the first mismatching
-- character (head-disjointness already proved in `Properties/Aggregator/
-- Dispatcher/HeadFails.agda`), so the chain at any concrete head reduces
-- to its head-class bucket.  Same-class collisions still resolve via inner
-- `<|>` (e.g. VAL_TABLE_ vs VAL_, BO_TX_BU_ vs BO_<digit>).
--
-- Why head-dispatch (vs `<|>` chain): elaborating `parseTopStmt pos
-- (emitX-chars x ++ outer) ≡ just r` at concrete-prefix input forces Agda
-- to walk through every leading-fail of the chain (15.7 GB residency
-- measured for one dispatcher under the 10-way variant).  Head-dispatch
-- reduces in a single pattern-match step, keeping per-dispatcher
-- elaboration bounded.
private
  parseTopStmt-V : Parser TopStmt
  parseTopStmt-V = (parseValueTable       >>= λ vt  → pure (TSValueTable vt))
               <|> (parseValueDescription >>= λ rvd → pure (TSValueDesc rvd))

  parseTopStmt-BA : Parser TopStmt
  parseTopStmt-BA = parseAttrLine >>= λ a → pure (TSAttribute a)

  parseTopStmt-BO : Parser TopStmt
  parseTopStmt-BO = (parseBOTxBu  >>= λ rms → pure (TSBOTxBu rms))
                <|> (parseMessage >>= λ m   → pure (TSMessage m))

  parseTopStmt-SI : Parser TopStmt
  parseTopStmt-SI = (parseSigValType  *> pure TSSigValType)
                <|> (parseSignalGroup >>= λ g → pure (TSSignalGroup g))

  parseTopStmt-SG : Parser TopStmt
  parseTopStmt-SG = parseSigMulVal *> pure TSSigMulVal

  parseTopStmt-EV : Parser TopStmt
  parseTopStmt-EV = parseEnvVar >>= λ e → pure (TSEnvVar e)

  parseTopStmt-CM : Parser TopStmt
  parseTopStmt-CM = parseComment >>= λ c → pure (TSComment c)

parseTopStmt : Parser TopStmt
parseTopStmt pos []                   = nothing
parseTopStmt pos ('V' ∷ rest)         = parseTopStmt-V  pos ('V' ∷ rest)
parseTopStmt pos ('B' ∷ 'A' ∷ rest)   = parseTopStmt-BA pos ('B' ∷ 'A' ∷ rest)
parseTopStmt pos ('B' ∷ 'O' ∷ rest)   = parseTopStmt-BO pos ('B' ∷ 'O' ∷ rest)
parseTopStmt pos ('S' ∷ 'I' ∷ rest)   = parseTopStmt-SI pos ('S' ∷ 'I' ∷ rest)
parseTopStmt pos ('S' ∷ 'G' ∷ rest)   = parseTopStmt-SG pos ('S' ∷ 'G' ∷ rest)
parseTopStmt pos ('E' ∷ 'V' ∷ rest)   = parseTopStmt-EV pos ('E' ∷ 'V' ∷ rest)
parseTopStmt pos ('C' ∷ 'M' ∷ rest)   = parseTopStmt-CM pos ('C' ∷ 'M' ∷ rest)
parseTopStmt _   _                    = nothing

-- ============================================================================
-- PARTITION INTO PER-FIELD BUCKETS
-- ============================================================================

-- Per-field buckets used by `parseText` to assemble the final `DBC`
-- record.  Wire order is preserved by right-cons insertion in
-- `partitionTopStmts`; `rawAttributes` is fed to `refineAttributes` by
-- the caller before becoming `DBC.attributes`; `rawValueDescs` is fed
-- to E.6's `attachValueDescs` to land on owning signals'
-- `DBCSignal.valueDescriptions` (Track E.5β).
record CollectedTop : Set where
  constructor mkCollectedTop
  field
    messages        : List DBCMessage
    valueTables     : List ValueTable
    environmentVars : List EnvironmentVar
    comments        : List DBCComment
    rawAttributes   : List RawDBCAttribute
    signalGroups    : List SignalGroup
    rawValueDescs   : List RawValueDesc
    rawMsgSenders   : List RawMsgSenders

emptyCollected : CollectedTop
emptyCollected = mkCollectedTop [] [] [] [] [] [] [] []

-- Cons one `TopStmt` onto its matching bucket.  Drop constructors pass
-- the accumulator through unchanged.
consTop : TopStmt → CollectedTop → CollectedTop
consTop (TSValueTable vt)  c =
  record c { valueTables     = vt ∷ CollectedTop.valueTables     c }
consTop (TSMessage m)      c =
  record c { messages        = m  ∷ CollectedTop.messages        c }
consTop (TSBOTxBu rms)     c =
  record c { rawMsgSenders   = rms ∷ CollectedTop.rawMsgSenders   c }
consTop (TSEnvVar e)       c =
  record c { environmentVars = e  ∷ CollectedTop.environmentVars c }
consTop (TSComment cm)     c =
  record c { comments        = cm ∷ CollectedTop.comments        c }
consTop (TSAttribute a)    c =
  record c { rawAttributes   = a  ∷ CollectedTop.rawAttributes   c }
consTop (TSValueDesc rvd)  c =
  record c { rawValueDescs   = rvd ∷ CollectedTop.rawValueDescs  c }
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
parseDBCText : Parser (List Char × List Node × List TopStmt)
parseDBCText = do
  ver   ← parseVersion
  _     ← parseNamespace
  _     ← parseBitTiming
  nodes ← parseBU
  stmts ← many parseTopStmt
  pure (ver , nodes , stmts)
