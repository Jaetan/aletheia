{-# OPTIONS --safe --without-K #-}

-- Per-line-construct roundtrips for the DBC topology section (B.3.d
-- Layer 3) — facade module.
--
-- Re-exports:
--   * BU_ (node-list) roundtrip — Commit 3b.
--   * Receivers (comma-separated identifier list inside SG_) — post-η
--     bridge between DSL `canonicalReceiversFmt` and the existing
--     `emitReceivers-chars`; consumed by the signal-line bridge.
--   * SG_ (parseSignalLine) per-MuxMarker dispatchers — slim wrappers
--     over the DSL's universal `signalLine-roundtrip`.
--
-- Future Layer-3 commits (3d.6–3d.8) will land BO_ (parseMessage)
-- composers + the many-recursion principle.
--
-- Split into per-construct submodules under `Properties/Topology/` to
-- keep each file near the ~500-line soft cap (see
-- `feedback_properties_facade_split.md`).
module Aletheia.DBC.TextParser.Properties.Topology where

open import Aletheia.DBC.TextParser.Properties.Topology.Nodes public
  using (parseBU-roundtrip; NodeNameStop)

open import Aletheia.DBC.TextParser.Properties.Topology.Receivers public
  using ( isReceiverCont
        ; emit-canonicalReceiversFmt-eq-emitReceivers)

-- 3d.5.c-η: SG_ parseSignalLine per-MuxMarker-shape roundtrip
-- dispatchers — slim wrappers over `Format.SignalLine.signalLine-
-- roundtrip` + the local `emit-signalLineFmt-eq-emitSignalLine-chars`
-- bridge.  BothMux is dead-under-formatter (see G-A6 in
-- `WellFormedText.agda`'s module header) so only NotMux / IsMux /
-- SelBy v are exposed.
open import Aletheia.DBC.TextParser.Properties.Topology.Signal public
  using ( SignalNameStop; expectedRaw
        ; parseSignalLine-roundtrip-NotMux
        ; parseSignalLine-roundtrip-IsMux
        ; parseSignalLine-roundtrip-SelBy)
