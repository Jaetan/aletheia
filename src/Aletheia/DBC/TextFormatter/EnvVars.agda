{-# OPTIONS --safe --without-K #-}

-- Environment-variable emitters for the DBC text format (Phase B.3.c.9 —
-- companion to `Aletheia.DBC.TextParser.EnvVars`).
--
-- Grammar slice emitted (mirrors `TextParser.EnvVars`):
--   env-var      ::= "EV_" ws identifier ws? ":" ws ("0" | "1" | "2") ws
--                    "[" rational "|" rational "]" ws string-lit ws
--                    rational ws nat ws identifier ws identifier ws? ";"
--                    newline
--
-- Canonical emit shape (cantools parity, `dbc.py:1086`):
--   `EV_ {name}: {type} [{min}|{max}] "{unit}" {initial} {env_id} {access_type} {access_node};\n`
--
-- Synthesized drop-field values (the Agda `EnvironmentVar` record does
-- not carry these, yet the wire grammar requires all 14 tokens):
--   * unit        — `""` (empty quoted string; cantools emits the same
--                   when `env.unit is None`).
--   * env_id      — `0` (cantools default when the input carries
--                   `env.env_id is None`; an integer placeholder that
--                   reparses cleanly).
--   * access_type — `DUMMY_NODE_VECTOR0` (the same `Vector__XXX`-family
--                   placeholder used across DBC tools for an
--                   unassigned-node slot; cantools also emits this when
--                   `env.access_type is None`).
--   * access_node — `Vector__XXX` (cantools' no-named-node placeholder;
--                   matches `TextFormatter.Topology.emitReceivers`'s
--                   fallback choice for the same class of field).
--
-- All four placeholders are *reparseable* by `parseEnvVar`: `""` satisfies
-- `parseStringLit`, `0` satisfies `parseNatural`, and the two WORD tokens
-- satisfy `parseIdentifier`.  The B.3.d roundtrip proof therefore
-- composes — `parseText ∘ formatText ≡ id` holds on the retained 5-field
-- projection.
--
-- Section packing: EV_ lines pack directly with no blank-line separator
-- between entries; `emitEnvVars` concatenates via `foldr` without an
-- inter-line combinator.  `parseEnvVar`'s `many parseNewline` tail
-- tolerates optional blank lines for hand-written corpora but this
-- emitter never produces any, mirroring the pack-direct stance of
-- `emitValueTables`.
module Aletheia.DBC.TextFormatter.EnvVars where

open import Data.List using (List; foldr)
open import Data.String using (String) renaming (_++_ to _++ₛ_)

open import Aletheia.DBC.Types using
  (EnvironmentVar; VarType; IntVar; FloatVar; StringVar)
open import Aletheia.DBC.TextFormatter.Emitter using (showDecRat-dec)

-- ============================================================================
-- VARTYPE DIGIT EMITTER
-- ============================================================================

-- `VarType` → the single ASCII digit the grammar demands.  Mirrors
-- `varTypeToℕ` (in `Aletheia.DBC.Types`) but returns the digit character
-- directly so no intermediate `ℕ` conversion is needed.
emitVarType : VarType → String
emitVarType IntVar    = "0"
emitVarType FloatVar  = "1"
emitVarType StringVar = "2"

-- ============================================================================
-- EV_ LINE
-- ============================================================================

-- One EV_ line with trailing `\n`.  Synthesized drop-field values chosen
-- to reparse cleanly and match cantools' None-handling fallbacks (see
-- module header).
emitEnvVar : EnvironmentVar → String
emitEnvVar ev =
  "EV_ " ++ₛ EnvironmentVar.name ev ++ₛ ": " ++ₛ
  emitVarType (EnvironmentVar.varType ev) ++ₛ
  " [" ++ₛ showDecRat-dec (EnvironmentVar.minimum ev) ++ₛ "|" ++ₛ
  showDecRat-dec (EnvironmentVar.maximum ev) ++ₛ "]" ++ₛ
  " \"\" " ++ₛ                             -- unit (synthesized)
  showDecRat-dec (EnvironmentVar.initial ev) ++ₛ
  " 0" ++ₛ                                 -- env_id (synthesized)
  " DUMMY_NODE_VECTOR0" ++ₛ                -- access_type (synthesized)
  " Vector__XXX" ++ₛ                       -- access_node (synthesized)
  ";\n"

-- ============================================================================
-- SECTION EMITTER
-- ============================================================================

-- Zero-or-more EV_ lines, concatenated without inter-line blanks.  Empty
-- list emits `""`, matching cantools' behaviour when no environment
-- variables are defined.
emitEnvVars : List EnvironmentVar → String
emitEnvVars = foldr (λ ev acc → emitEnvVar ev ++ₛ acc) ""
