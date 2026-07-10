-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Per-line-construct roundtrips for the DBC environment-variable section
-- — facade module.
--
-- Re-exports `parseEnvVar-roundtrip` from `Properties/EnvVars/EnvVar.agda`.
-- Mirrors the `Properties/Topology.agda` and `Properties/Preamble.agda`
-- pattern; the per-construct submodule lives under `Properties/EnvVars/`
-- so each file stays near the ~600–800-line soft cap (see
-- `feedback_properties_facade_split.md`).
module Aletheia.DBC.TextParser.Properties.EnvVars where

open import Aletheia.DBC.TextParser.Properties.EnvVars.EnvVar public
  using (parseEnvVar-roundtrip; EnvVarNameStop;
         parseEnvVars-roundtrip)
