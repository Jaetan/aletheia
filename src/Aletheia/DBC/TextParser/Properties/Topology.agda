{-# OPTIONS --without-K #-}

-- Per-line-construct roundtrips for the DBC topology section (B.3.d
-- Layer 3) — facade module.
--
-- Currently re-exports the BU_ (node-list) roundtrip from Layer 3
-- Commit 3b.  Future commits in the same layer (3d) will land BO_
-- (message) and SG_ (signal) roundtrips here alongside Nodes.agda.
--
-- Split into per-construct submodules under `Properties/Topology/` to
-- keep each file near the ~500-line soft cap (see
-- `feedback_properties_facade_split.md`).
module Aletheia.DBC.TextParser.Properties.Topology where

open import Aletheia.DBC.TextParser.Properties.Topology.Nodes public
  using (parseBU-roundtrip; NodeNameStop)
