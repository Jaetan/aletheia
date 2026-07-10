-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Per-line-construct roundtrips for the DBC topology section — facade
-- module.
--
-- Re-exports:
--   * BU_ (node-list) roundtrip.
--   * Receivers (comma-separated identifier list inside SG_) — post-η
--     bridge between DSL `canonicalReceiversFmt` and the existing
--     `emitReceivers-chars`; consumed by the signal-line bridge.
--   * SG_ (parseSignalLine) per-MuxMarker dispatchers — slim wrappers
--     over the DSL's universal `signalLine-roundtrip`.
--
-- Future commits will land BO_ (parseMessage)
-- composers + the many-recursion principle.
--
-- Split into per-construct submodules under `Properties/Topology/` to
-- keep each file near the ~500-line soft cap (see
-- `feedback_properties_facade_split.md`).
module Aletheia.DBC.TextParser.Properties.Topology where

open import Aletheia.DBC.TextParser.Properties.Topology.Nodes public
  using (NodeNameStop)

open import Aletheia.DBC.TextParser.Properties.Topology.Receivers public
  using ( )

-- SG_ parseSignalLine per-MuxMarker-shape roundtrip
-- dispatchers — slim wrappers over `Format.SignalLine.signalLine-
-- roundtrip` + the local `emit-signalLineFmt-eq-emitSignalLine-chars`
-- bridge.  BothMux is dead-under-formatter (see G-A6 in
-- `WellFormedText.agda`'s module header) so only NotMux / IsMux /
-- SelBy v are exposed.
open import Aletheia.DBC.TextParser.Properties.Topology.Signal public
  using ( )

-- SG_ block (`many parseSignalLine`) roundtrip — list-level
-- composition of `signalLine-roundtrip` via the framework's universal
-- `roundtrip (many signalLineFmt)`.
open import Aletheia.DBC.TextParser.Properties.Topology.SignalList public
  using ( )

-- `resolveSignalList`-roundtrip — recovers `List DBCSignal` from
-- the formatter-emitted `List RawSignal` under MasterCoherent +
-- per-signal WellFormedSignal + PhysicallyValid + WellFormedTextPresence.
open import Aletheia.DBC.TextParser.Properties.Topology.Resolve public
  using ( )

-- `parseMessage`-roundtrip — full BO_ block composer.  Composes
-- `messageHeader-roundtrip` (DSL universal on `messageHeaderFmt`) +
-- `parseSignalLines-roundtrip` + `manyHelper-parseNewline-exhaust`
-- + `buildMessage-roundtrip` (canid/dlc roundtrips + `resolveSignalList`).
open import Aletheia.DBC.TextParser.Properties.Topology.Message public
  using ( parseMessage-roundtrip
        -- list-level lift via the polymorphic `many-η-roundtrip`.
        ; MessageWF)
