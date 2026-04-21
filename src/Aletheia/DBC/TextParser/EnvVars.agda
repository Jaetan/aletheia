{-# OPTIONS --safe --without-K #-}

-- Environment-variable parser for the DBC text format (Phase B.3.c.9).
--
-- Grammar slice covered (BNF section G from `Aletheia.DBC.TextParser`):
--   env-var      ::= "EV_" ws identifier ws? ":" ws ("0" | "1" | "2") ws
--                    "[" rational "|" rational "]" ws string-lit ws
--                    rational ws nat ws identifier ws identifier ws? ";"
--                    newline
--
-- Authoritative grammar source: `cantools/database/can/formats/dbc.py`
-- lines 308-311 (`environment_variable` Sequence, 14 tokens + `;`).  The
-- access-list is a pair of bare `WORD` tokens (`access_type`, `access_node`)
-- — NOT a comma-delimited list.  Corpus `tests/corpus/dbc/*` confirms the
-- whitespace-separated single-node shape
-- (`... DUMMY_NODE_VECTOR0 Host;`).
--
-- `EV_DATA_` / `ENVVAR_DATA_` are *declared* in the `NS_` preamble keyword
-- section (not re-declared at top level anywhere in the corpus), so those
-- keywords fall under the NS_ parser's `keyword newline` recognizer — not
-- this module.  See `TextParser.Preamble.parseNSLine`.
--
-- Scope note — 4 wire fields parsed but discarded:
--   The Agda `EnvironmentVar` record (`Aletheia.DBC.Types`) carries 5
--   semantically-useful fields: `name`, `varType`, `initial`, `minimum`,
--   `maximum`.  The wire format additionally carries `unit`, `env_id`,
--   `access_type`, `access_node` — none of which the structural
--   `DbcDefinition` observed by Python / C++ / Go surfaces today
--   (`python/aletheia/dbc_converter.py` drops them on the way through
--   cantools → `dbc_to_json`).  Parsing them syntactically is still
--   required so ill-formed lines reject the whole file, matching the
--   parse-and-drop stance used by `parseValueDescription`
--   (`TextParser.ValueTables`), `parseSigValType`
--   (`TextParser.ValueTypes`), and `parseSigMulVal`
--   (`TextParser.ExtendedMux`).  A future extension that promotes any of
--   these fields end-to-end can flip this parser to return the richer
--   record without re-deriving the grammar.
--
-- Wire-order vs record-field-order:
--   The wire order is `(name, varType, [min|max], unit, initial, env_id,
--   access_type, access_node)`; the Agda record orders
--   `(name, varType, initial, minimum, maximum)`.  We read in wire order
--   and build the record with *named* field assignment so the offset is
--   explicit and the compiler — not the reviewer — checks correctness.
--
-- `VarType` dispatch — strict digit choice:
--   The BNF fixes the varType token to `"0" | "1" | "2"`.  We dispatch via
--   `(char '0' *> pure IntVar) <|> (char '1' *> pure FloatVar) <|>
--    (char '2' *> pure StringVar)` rather than `parseNatural`, so a
--   grammar violation (e.g. `EV_ name: 3 [...]`) rejects at the digit
--   position instead of silently succeeding on a >9 number.  Mirrors the
--   `"1"|"2"` dispatch in `TextParser.ValueTypes.parseSigValType`.
--
-- Longest-first dispatch (future top-level aggregator):
--   `EV_` shares no prefix with any other top-level DBC keyword (`VERSION`,
--   `NS_`, `BS_`, `BU_`, `BO_`, `CM_`, `BA_*`, `VAL_*`, `SIG_*`,
--   `SG_MUL_VAL_`), so no longest-first ordering is required here.
module Aletheia.DBC.TextParser.EnvVars where

open import Data.Rational using (ℚ)
open import Data.String using (String)
open import Data.Unit using (⊤; tt)

open import Aletheia.Parser.Combinators using
  (Parser; pure; _>>=_; _<|>_; _*>_;
   char; string; many)
open import Aletheia.DBC.TextParser.Lexer using
  (parseIdentifier; parseStringLit; parseWS; parseWSOpt; parseNewline;
   parseNatural; parseRational)

open import Aletheia.DBC.Types using
  (EnvironmentVar; VarType; IntVar; FloatVar; StringVar)

-- ============================================================================
-- VARTYPE DIGIT DISPATCH
-- ============================================================================

-- `"0" | "1" | "2"` mapped to the corresponding `VarType`.  Strict digit
-- choice (see module header).  No fallback — the backtracking `<|>` lets
-- the caller's error propagate when none match.
parseVarType : Parser VarType
parseVarType =
  (char '0' *> pure IntVar)    <|>
  (char '1' *> pure FloatVar)  <|>
  (char '2' *> pure StringVar)

-- ============================================================================
-- EV_ LINE
-- ============================================================================

-- `"EV_" ws identifier ws? ":" ws varType ws "[" rational "|" rational "]"
--  ws string-lit ws rational ws nat ws identifier ws identifier ws? ";"
--  newline` + trailing blank-line tolerance via `many parseNewline`.
--
-- Field read-order mirrors cantools' 14-token Sequence at `dbc.py:308-311`.
-- The record is built with named field assignment so the wire/record
-- offset is explicit.  Dropped fields (unit, env_id, access_type,
-- access_node) are bound to `_` so grammar violations still reject, while
-- the discard is unambiguous to the reader.
parseEnvVar : Parser EnvironmentVar
parseEnvVar = do
  _ ← string "EV_"
  _ ← parseWS
  nm ← parseIdentifier
  _ ← parseWSOpt
  _ ← char ':'
  _ ← parseWS
  vt ← parseVarType
  _ ← parseWS
  _ ← char '['
  mn ← parseRational
  _ ← char '|'
  mx ← parseRational
  _ ← char ']'
  _ ← parseWS
  _ ← parseStringLit      -- unit, discarded
  _ ← parseWS
  ini ← parseRational
  _ ← parseWS
  _ ← parseNatural        -- env_id, discarded
  _ ← parseWS
  _ ← parseIdentifier     -- access_type, discarded
  _ ← parseWS
  _ ← parseIdentifier     -- access_node, discarded
  _ ← parseWSOpt
  _ ← char ';'
  _ ← parseNewline
  _ ← many parseNewline
  pure (record
    { name    = nm
    ; varType = vt
    ; initial = ini
    ; minimum = mn
    ; maximum = mx
    })
