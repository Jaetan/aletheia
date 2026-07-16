-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Per-line-construct roundtrips for the DBC value-table section — facade
-- module.
--
-- Re-exports `parseValueTable-roundtrip` from
-- `Properties/ValueTables/ValueTable.agda` and the
-- `parseValueDescription-roundtrip` from `Properties/ValueTables/
-- ValueDesc.agda`.  Mirrors the `Properties/Topology.agda` and
-- `Properties/Preamble.agda` pattern; the per-construct submodule lives
-- under `Properties/ValueTables/` so each file stays near the ~600–800-
-- line soft cap.
module Aletheia.DBC.TextParser.Properties.ValueTables where

open import Aletheia.DBC.TextParser.Properties.ValueTables.ValueTable public
  using (parseValueTable-roundtrip; ValueTableNameStop)

open import Aletheia.DBC.TextParser.Properties.ValueTables.ValueDesc public
  using ()
