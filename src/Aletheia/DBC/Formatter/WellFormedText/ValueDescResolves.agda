{-# OPTIONS --safe --without-K #-}

-- Phase E.8 — `ValueDescResolves` predicate: per-`RawValueDesc` cross-DBC
-- existence check for the `(canId, signalName)` lookup target.
--
-- Bool-decidable primary `resolvesᵇ` (delegates to `resolvesᵇ-msgs` over
-- `DBC.messages`) + `Set` lift `ValueDescResolves = T ∘ resolvesᵇ`.
-- E.11 (validator CHECK 23 `UnknownValueDescriptionTarget`) consumes the
-- Bool form; structural well-formedness consumes the Set lift.
--
-- Wiring (Plan B, 2026-05-07): `DBC.unresolvedValueDescs` carries entries
-- whose `(canId, signalName)` did not resolve against `messages`.
-- `WellFormedDBC.unresolved-empty` requires this list to be empty for the
-- text-roundtrip universal in `Substrate/Unsafe.agda` to close.  CHECK 23
-- in the validator walks `DBC.unresolvedValueDescs` and emits one
-- `UnknownValueDescriptionTarget` warning per entry.
--
-- Universal-proof note: a successfully-resolved `RawValueDesc` from
-- `collectFromMessages (DBC.messages d)` carries `RawValueDescNameStop`
-- for free via the chain
--
--   rvd.signalName ≡ DBCSignal.name sig   (collectFromMessages construction)
--                  → SignalNameStop sig    (MessageWF.item-pres : All SignalLineWF)
--                  → IdentHeadNonHSpace (DBCSignal.name sig)
--                  → RawValueDescNameStop rvd.signalName
--
-- so E.9's `tvd-WF` arm derives `All RawValueDescStop (collectFromMessages
-- msgs)` directly from existing `MessageWF` data — `ValueDescResolves` is
-- NOT needed for the universal proof.  This module is purely for the
-- validator side (E.11 CHECK 23).
module Aletheia.DBC.Formatter.WellFormedText.ValueDescResolves where

open import Data.Bool using (Bool; T)

open import Aletheia.DBC.Types using (DBC; RawValueDesc)
open import Aletheia.DBC.TextParser.ValueDescriptions using (resolvesᵇ-msgs)


-- ============================================================================
-- DECIDABLE BOOL CHECK (DBC-level wrapper)
-- ============================================================================

-- `true` iff some message `msg ∈ DBC.messages d` has `DBCMessage.id msg ≡
-- RawValueDesc.canId rvd`, and some signal `sig ∈ DBCMessage.signals msg`
-- has `DBCSignal.name sig ≡ RawValueDesc.signalName rvd`.  Delegates to
-- `resolvesᵇ-msgs` (defined in `TextParser.ValueDescriptions`); kept here
-- as a thin wrapper so the abstraction "validator operates on `DBC`"
-- holds at the API surface.
resolvesᵇ : RawValueDesc → DBC → Bool
resolvesᵇ rvd d = resolvesᵇ-msgs rvd (DBC.messages d)


-- ============================================================================
-- SET-LIFTED PREDICATE
-- ============================================================================

ValueDescResolves : RawValueDesc → DBC → Set
ValueDescResolves rvd d = T (resolvesᵇ rvd d)
