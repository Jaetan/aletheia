{-# OPTIONS --safe --without-K #-}

-- Environment-variable emitters for the DBC text format (Phase B.3.c.9 —
-- companion to `Aletheia.DBC.TextParser.EnvVars`; layer-1 form 2026-04-24).
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
--                   matches `TextFormatter.Topology.emitReceivers-chars`'s
--                   fallback choice for the same class of field).
--
-- All four placeholders are *reparseable* by `parseEnvVar`: `""` satisfies
-- `parseStringLit`, `0` satisfies `parseNatural`, and the two WORD tokens
-- satisfy `parseIdentifier`.  The B.3.d roundtrip proof therefore
-- composes — `parseText ∘ formatText ≡ id` holds on the retained 5-field
-- projection.
--
-- Section packing: EV_ lines pack directly with no blank-line separator
-- between entries; `emitEnvVars-chars` concatenates via `foldr` without
-- an inter-line combinator.
--
-- All emitters are `List Char`-valued (B.3.d Option 3a layer-1 layout —
-- see `Emitter` module header).
module Aletheia.DBC.TextFormatter.EnvVars where

open import Data.Char using (Char)
open import Data.List using (List; []; _∷_; foldr) renaming (_++_ to _++ₗ_)
open import Data.String using (toList)

open import Aletheia.DBC.Types using
  (EnvironmentVar; VarType; IntVar; FloatVar; StringVar)
open import Aletheia.DBC.TextFormatter.Emitter using (showDecRat-dec-chars)

-- ============================================================================
-- VARTYPE DIGIT EMITTER
-- ============================================================================

-- `VarType` → the single ASCII digit the grammar demands.
emitVarType-chars : VarType → List Char
emitVarType-chars IntVar    = '0' ∷ []
emitVarType-chars FloatVar  = '1' ∷ []
emitVarType-chars StringVar = '2' ∷ []

-- ============================================================================
-- EV_ LINE
-- ============================================================================

-- One EV_ line with trailing `\n`.  Synthesized drop-field values chosen
-- to reparse cleanly and match cantools' None-handling fallbacks (see
-- module header).
emitEnvVar-chars : EnvironmentVar → List Char
emitEnvVar-chars ev =
  toList "EV_ " ++ₗ toList (EnvironmentVar.name ev) ++ₗ
  toList ": " ++ₗ
  emitVarType-chars (EnvironmentVar.varType ev) ++ₗ
  toList " [" ++ₗ showDecRat-dec-chars (EnvironmentVar.minimum ev) ++ₗ
  '|' ∷ showDecRat-dec-chars (EnvironmentVar.maximum ev) ++ₗ
  toList "]" ++ₗ
  toList " \"\" " ++ₗ                             -- unit (synthesized)
  showDecRat-dec-chars (EnvironmentVar.initial ev) ++ₗ
  toList " 0" ++ₗ                                 -- env_id (synthesized)
  toList " DUMMY_NODE_VECTOR0" ++ₗ                -- access_type (synthesized)
  toList " Vector__XXX" ++ₗ                       -- access_node (synthesized)
  toList ";\n"

-- ============================================================================
-- SECTION EMITTER
-- ============================================================================

-- Zero-or-more EV_ lines, concatenated without inter-line blanks.  Empty
-- list emits `[]`, matching cantools' behaviour when no environment
-- variables are defined.
emitEnvVars-chars : List EnvironmentVar → List Char
emitEnvVars-chars =
  foldr (λ ev acc → emitEnvVar-chars ev ++ₗ acc) []
