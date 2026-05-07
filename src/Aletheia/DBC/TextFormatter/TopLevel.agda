{-# OPTIONS --safe --without-K #-}

-- Top-level composer for the DBC text format (Phase B.3.c.k; layer-1 form
-- 2026-04-24).
--
-- Concatenates the per-section emitters from B.3.c.2–B.3.c.9 into a
-- single `formatChars : DBC → List Char`.  `Aletheia.DBC.TextFormatter.
-- formatText` delegates to `fromList ∘ formatChars`.  This module is the
-- one that pins the emission order.
--
-- Canonical section order (matches `minimal.dbc` / `kitchen_sink.dbc`
-- and the `parseText` top-level dispatch, so the B.3.d roundtrip
-- composes):
--   1.  VERSION
--   2.  NS_
--   3.  BS_
--   4.  BU_
--   5.  VAL_TABLE_
--   6.  BO_ blocks (each with inner SG_ lines)
--   7.  VAL_                                         (E.7)
--   8.  EV_
--   9.  CM_
--  10.  BA_DEF_* / BA_DEF_DEF_ / BA_ / BA_REL_
--  11.  SIG_GROUP_
--
-- Sections 3 (BS_), 4 (BU_), and 7 (EV_) are emitted even when their
-- source-side lists are empty: BS_ carries its `BS_:\n\n` marker, BU_
-- carries `BU_:\n\n`, and the namespace block is likewise unconditional.
-- `emitValueTables-chars` / `emitMessages-chars` / `emitEnvVars-chars` /
-- `emitComments-chars` / `emitAttributes-chars` / `emitSignalGroups-chars`
-- each emit `[]` on an empty input, so they fall through cleanly without
-- inter-section scaffolding.
--
-- Inter-section separation — no additional blank lines are inserted
-- here; each per-section emitter already terminates with the right
-- number of `\n`s to pack against the next section.  This matches the
-- per-section parser tolerances in `TextParser.*`, so the roundtrip
-- composes without whitespace drift.
--
-- Layer-1 form (B.3.d Option 3a, 2026-04-24):
--   `formatChars : DBC → List Char` is the substrate the top-level
--   roundtrip proof reasons about.  The `String`-typed boundary lives
--   in `Aletheia.DBC.TextFormatter.formatText = fromList ∘ formatChars`,
--   which is the single load-bearing site for the
--   `Substrate/Unsafe.toList∘fromList` axiom (see
--   `memory/project_b3d_stdlib_audit.md` and
--   `Substrate/Unsafe.agda` module header).
module Aletheia.DBC.TextFormatter.TopLevel where

open import Data.Char using (Char)
open import Data.List using (List) renaming (_++_ to _++ₗ_)

open import Aletheia.DBC.Types using (DBC)

open import Aletheia.DBC.TextFormatter.Preamble using
  (emitVersion-chars; emitNamespace-chars; emitBitTiming-chars)
open import Aletheia.DBC.TextFormatter.Topology using
  (emitBU-chars; emitMessages-chars)
open import Aletheia.DBC.TextFormatter.ValueTables using
  (emitValueTables-chars; emitValueDescriptions-chars)
open import Aletheia.DBC.TextFormatter.EnvVars using
  (emitEnvVars-chars)
open import Aletheia.DBC.TextFormatter.Comments using
  (emitComments-chars)
open import Aletheia.DBC.TextFormatter.Attributes using
  (emitAttributes-chars)
open import Aletheia.DBC.TextFormatter.SignalGroups using
  (emitSignalGroups-chars)

-- ============================================================================
-- WHOLE-FILE EMITTER (List Char form)
-- ============================================================================

-- Emit a full DBC text image as `List Char`.  `formatText : DBC → String`
-- in `Aletheia.DBC.TextFormatter` is `fromList ∘ formatChars`.
formatChars : DBC → List Char
formatChars d =
  emitVersion-chars           (DBC.version         d) ++ₗ
  emitNamespace-chars                                 ++ₗ
  emitBitTiming-chars                                 ++ₗ
  emitBU-chars                (DBC.nodes           d) ++ₗ
  emitValueTables-chars       (DBC.valueTables     d) ++ₗ
  emitMessages-chars          (DBC.messages        d) ++ₗ
  emitValueDescriptions-chars (DBC.messages        d) ++ₗ
  emitEnvVars-chars           (DBC.environmentVars d) ++ₗ
  emitComments-chars          (DBC.comments        d) ++ₗ
  emitAttributes-chars        (DBC.attributes      d) ++ₗ
  emitSignalGroups-chars      (DBC.signalGroups    d)
