{-# OPTIONS --safe --without-K #-}

-- Per-line-construct roundtrips for the DBC value-table section (B.3.d
-- Layer 3 Commit 3b) — facade module.
--
-- Re-exports `parseValueTable-roundtrip` from
-- `Properties/ValueTables/ValueTable.agda`.  Mirrors the
-- `Properties/Topology.agda` and `Properties/Preamble.agda` pattern; the
-- per-construct submodule lives under `Properties/ValueTables/` so each
-- file stays near the ~600–800-line soft cap (see
-- `feedback_properties_facade_split.md`).
module Aletheia.DBC.TextParser.Properties.ValueTables where

open import Aletheia.DBC.TextParser.Properties.ValueTables.ValueTable public
  using (parseValueTable-roundtrip; ValueTableNameStop)
