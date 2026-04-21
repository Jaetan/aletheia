{-# OPTIONS --safe --without-K #-}

-- Top-level composer for the DBC text format (Phase B.3.c.k).
--
-- Concatenates the per-section emitters from B.3.c.2–B.3.c.9 into a
-- single `emitDBCText : DBC → String`.  `Aletheia.DBC.TextFormatter.
-- formatText` delegates straight here; this module is the one that
-- pins the emission order.
--
-- Canonical section order (matches `minimal.dbc` / `kitchen_sink.dbc`
-- and the `parseText` top-level dispatch, so the B.3.d roundtrip
-- composes):
--   1. VERSION
--   2. NS_
--   3. BS_
--   4. BU_
--   5. VAL_TABLE_
--   6. BO_ blocks (each with inner SG_ lines)
--   7. EV_
--   8. CM_
--   9. BA_DEF_* / BA_DEF_DEF_ / BA_ / BA_REL_
--  10. SIG_GROUP_
--
-- Sections 3 (BS_), 4 (BU_), and 7 (EV_) are emitted even when their
-- source-side lists are empty: BS_ carries its `BS_:\n\n` marker, BU_
-- carries `BU_:\n\n`, and the namespace block is likewise
-- unconditional.  `emitValueTables` / `emitMessages` / `emitEnvVars` /
-- `emitComments` / `emitAttributes` / `emitSignalGroups` each emit `""`
-- on an empty input, so they fall through cleanly without inter-section
-- scaffolding.
--
-- Inter-section separation — no additional blank lines are inserted
-- here; each per-section emitter already terminates with the right
-- number of `\n`s to pack against the next section (`emitVersion` /
-- `emitNamespace` / `emitBitTiming` / `emitBU` each end with `"\n\n"`,
-- `emitMessages` packs one blank line after each BO_ block, and
-- `emitValueTables` / `emitEnvVars` / `emitComments` / `emitAttributes`
-- / `emitSignalGroups` pack line-by-line with no trailing blank).  This
-- matches the per-section parser tolerances in `TextParser.*`, so the
-- roundtrip composes without whitespace drift.
--
-- Deliberate omissions (constructs with no retained Agda field — drop
-- parsers only, see `TextParser.TopLevel` module header):
--   * BO_TX_BU_  — every `DBCMessage.senders` is `[]` out of `parseMessage`
--                  (B.3.b skeleton), so there is no wire-order list to
--                  emit; `parseText` would just drop anything we wrote.
--   * VAL_       — `DBCSignal` has no `valueDescriptions` field; see
--                  `TextFormatter.ValueTables` module header for the
--                  graceful-drop rationale.
--   * SIG_VALTYPE_ — no retained `floatWidth`/`signalType` tag per signal.
--   * SG_MUL_VAL_  — `presence = When _ (v ∷ [])` already captures the
--                    single-value case; multi-value selectors need
--                    cross-line coordination that B.3.c.k does not
--                    introduce.
-- All four are parse-and-drop on the other side of the roundtrip, so
-- the retained 5-field projection (`version, messages, signalGroups,
-- environmentVars, valueTables, nodes, comments, attributes`) is what
-- composes under B.3.d.
module Aletheia.DBC.TextFormatter.TopLevel where

open import Data.String using (String) renaming (_++_ to _++ₛ_)

open import Aletheia.DBC.Types using (DBC)

open import Aletheia.DBC.TextFormatter.Preamble using
  (emitVersion; emitNamespace; emitBitTiming)
open import Aletheia.DBC.TextFormatter.Topology using
  (emitBU; emitMessages)
open import Aletheia.DBC.TextFormatter.ValueTables using
  (emitValueTables)
open import Aletheia.DBC.TextFormatter.EnvVars using
  (emitEnvVars)
open import Aletheia.DBC.TextFormatter.Comments using
  (emitComments)
open import Aletheia.DBC.TextFormatter.Attributes using
  (emitAttributes)
open import Aletheia.DBC.TextFormatter.SignalGroups using
  (emitSignalGroups)

-- ============================================================================
-- WHOLE-FILE EMITTER
-- ============================================================================

-- Emit a full DBC text image.  The returned string is the input to a
-- successful `parseText`; see `Aletheia.DBC.TextParser` for the dual.
emitDBCText : DBC → String
emitDBCText d =
  emitVersion     (DBC.version         d) ++ₛ
  emitNamespace                           ++ₛ
  emitBitTiming                           ++ₛ
  emitBU          (DBC.nodes           d) ++ₛ
  emitValueTables (DBC.valueTables     d) ++ₛ
  emitMessages    (DBC.messages        d) ++ₛ
  emitEnvVars     (DBC.environmentVars d) ++ₛ
  emitComments    (DBC.comments        d) ++ₛ
  emitAttributes  (DBC.attributes      d) ++ₛ
  emitSignalGroups (DBC.signalGroups   d)
