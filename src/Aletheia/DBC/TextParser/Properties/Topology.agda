{-# OPTIONS --without-K #-}

-- Per-line-construct roundtrips for the DBC topology section (B.3.d
-- Layer 3) — facade module.
--
-- Re-exports:
--   * BU_ (node-list) roundtrip — Commit 3b.
--   * Receivers (comma-separated identifier list inside SG_) — Commit
--     3d.2 primitive; composed downstream by parseSignalLine-roundtrip.
--
-- Future Layer-3 commits (3d.3–3d.6) will land SG_ (parseSignalLine) and
-- BO_ (parseMessage) roundtrips here alongside Nodes.agda and
-- Receivers.agda.
--
-- Split into per-construct submodules under `Properties/Topology/` to
-- keep each file near the ~500-line soft cap (see
-- `feedback_properties_facade_split.md`).
module Aletheia.DBC.TextParser.Properties.Topology where

open import Aletheia.DBC.TextParser.Properties.Topology.Nodes public
  using (parseBU-roundtrip; NodeNameStop)

open import Aletheia.DBC.TextParser.Properties.Topology.Receivers public
  using ( isReceiverCont
        ; ident-VectorXXX
        ; parseReceiverList-roundtrip-empty
        ; parseReceiverList-roundtrip-cons
        ; stripVectorPlaceholder-vectorXXX
        ; stripVectorPlaceholder-no-vectorXXX
        ; parseReceiverList∘strip-roundtrip)

-- 3d.3 (in progress): SG_ parseSignalLine roundtrip — see Signal.agda
-- header.  Currently exposes the `parseSignalTail` extraction +
-- `parseSignalLine-decompose` lemma (closes by refl) + `expectedRaw`
-- shape + `SignalNameStop` precondition.  Per-MuxMarker-shape main
-- theorems land in 3d.3b alongside the 28-step bind-just-step chain.
open import Aletheia.DBC.TextParser.Properties.Topology.Signal public
  using ( SignalNameStop; expectedRaw
        ; parseSignalTail; parseSignalLine-decompose)
