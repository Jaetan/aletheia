{-# OPTIONS --safe --without-K #-}

-- B.3.d Layer 3 Commit 3c.3 — `parseRawAttrAssign` and `parseRawAttrRel`
-- per-line construct roundtrips — facade module.
--
-- `parseRawAttrAssign` consumes
--   `"BA_" ws string-lit ws (attr-target ws)? raw-value ws? ";" newline ...`
-- with 5 target cases (ATgtNetwork as fall-through, ATgtNode /
-- ATgtMessage / ATgtSignal / ATgtEnvVar via 4-way `<|>` keyword
-- dispatch in `parseStandardAttrTarget`).
--
-- `parseRawAttrRel` consumes
--   `"BA_REL_" ws string-lit ws rel-target raw-value ws? ";" newline ...`
-- with 2 target cases (ATgtNodeMsg / ATgtNodeSig via `parseRelTarget`
-- 2-way `<|>`).
--
-- Sub-files (per-target × per emit-shape, 21 cases total):
--   * `Assign/Common.agda`  — shared head-classify and value-stops
--     helpers.
--   * `Assign/Network.agda` — ATgtNetwork × {RavString, frac, bareInt}
--     (3 dispatchers; fall-through case).
--   * `Assign/Node.agda`    — ATgtNode × 3 (BU_ keyword + ident).
--   * `Assign/Message.agda` — ATgtMessage × 3 (BO_ keyword + nat ID +
--     `wrapMsgTarget`).
--   * `Assign/Signal.agda`  — ATgtSignal × 3 (SG_ keyword + nat ID +
--     ident + `wrapSigTarget`).
--   * `Assign/EnvVar.agda`  — ATgtEnvVar × 3 (EV_ keyword + ident).
--   * `Assign/Rel.agda`     — ATgtNodeMsg + ATgtNodeSig × 3 (BA_REL_
--     plus per-target rel-keyword chain).
--
-- Splitting follows `feedback_properties_facade_split.md` and
-- pre-empts the soft-cap line growth.

module Aletheia.DBC.TextParser.Properties.Attributes.Assign where

-- ============================================================================
-- R22-PRE-CLOSE: stale `using (...)` re-exports — RE-EVALUATE BEFORE MERGE
-- ============================================================================
-- Per-file type-check (e.g. via `agda Properties/Aggregator/Dispatcher/
-- Attribute/TopStmt/Default.agda`) surfaces 18 `ModuleDoesntExport` warnings
-- emitted from the six `open import ... public` clauses below.  Each named
-- import-clause references identifiers that the cited submodule no longer
-- exports (presumably renamed or absorbed during a prior split refactor).
-- The warnings are non-fatal (agda treats them as `-W[no]ModuleDoesntExport`
-- so `cabal run shake -- build` and `check-properties` both pass), but they
-- pollute every type-check trace in this subtree and risk masking a real
-- export break later.
--
-- Discovered: 2026-05-18 during R22 batch 15 (commit `afd5ea7`) when the
-- per-file type-check of `Properties/Aggregator/Dispatcher/Attribute/
-- TopStmt/Default.agda` printed the full warning list.  See commit body
-- for the disposition rationale at b15 (out-of-scope for the dead-import
-- prune; the using-clauses are STALE not DEAD — they reference names the
-- submodule once exported, not names this file imports-but-doesn't-use).
--
-- Pre-close action required (one of):
--   1. **Prune the stale names** from each `using (...)` clause to whatever
--      the cited submodule actually exports today (likely the right call —
--      mirrors R22's dead-import prune posture).
--   2. **Restore the missing exports** in the submodules if those names
--      were intended to remain public (less likely — the rename happened
--      with reason).
--   3. **Document** if the warnings are intentional (very unlikely — the
--      warning class exists specifically to flag stale references).
--
-- DO NOT MERGE R22 → main without resolving this.  Tracked in
-- `.session-state.md` → Pre-close checklist.
-- ============================================================================

open import Aletheia.DBC.TextParser.Properties.Attributes.Assign.Network public
  using ( parseRawAttrAssign-roundtrip-ATgtNetwork-RavString
        ; parseRawAttrAssign-roundtrip-ATgtNetwork-RavDecRatFrac
        ; parseRawAttrAssign-roundtrip-ATgtNetwork-RavDecRatBareInt)

open import Aletheia.DBC.TextParser.Properties.Attributes.Assign.Node public
  using ( IdentNameStop
        ; parseRawAttrAssign-roundtrip-ATgtNode-RavString
        ; parseRawAttrAssign-roundtrip-ATgtNode-RavDecRatFrac
        ; parseRawAttrAssign-roundtrip-ATgtNode-RavDecRatBareInt)

open import Aletheia.DBC.TextParser.Properties.Attributes.Assign.Message public
  using ( parseRawAttrAssign-roundtrip-ATgtMessage-RavString
        ; parseRawAttrAssign-roundtrip-ATgtMessage-RavDecRatFrac
        ; parseRawAttrAssign-roundtrip-ATgtMessage-RavDecRatBareInt)

open import Aletheia.DBC.TextParser.Properties.Attributes.Assign.Signal public
  using ( parseRawAttrAssign-roundtrip-ATgtSignal-RavString
        ; parseRawAttrAssign-roundtrip-ATgtSignal-RavDecRatFrac
        ; parseRawAttrAssign-roundtrip-ATgtSignal-RavDecRatBareInt)

open import Aletheia.DBC.TextParser.Properties.Attributes.Assign.EnvVar public
  using ( parseRawAttrAssign-roundtrip-ATgtEnvVar-RavString
        ; parseRawAttrAssign-roundtrip-ATgtEnvVar-RavDecRatFrac
        ; parseRawAttrAssign-roundtrip-ATgtEnvVar-RavDecRatBareInt)

open import Aletheia.DBC.TextParser.Properties.Attributes.Assign.Rel public
  using ( parseRawAttrRel-roundtrip-ATgtNodeMsg-RavString
        ; parseRawAttrRel-roundtrip-ATgtNodeMsg-RavDecRatFrac
        ; parseRawAttrRel-roundtrip-ATgtNodeMsg-RavDecRatBareInt
        ; parseRawAttrRel-roundtrip-ATgtNodeSig-RavString
        ; parseRawAttrRel-roundtrip-ATgtNodeSig-RavDecRatFrac
        ; parseRawAttrRel-roundtrip-ATgtNodeSig-RavDecRatBareInt)
