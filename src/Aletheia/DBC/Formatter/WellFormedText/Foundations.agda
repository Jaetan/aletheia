-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Master-coherence predicate for the text round-trip (the closure-light subset
-- of `Aletheia.DBC.Formatter.WellFormedText`, which re-exports it).
--
-- Lives in its own child module so the runtime checker
-- (`Aletheia.DBC.TextParser.WellFormedCheck`) can decide `MasterCoherent`
-- without pulling the parent module's proof-carrying dependencies
-- (`WellFormedMessageRT` and its lemma imports) into the `libaletheia-ffi.so`
-- closure.
module Aletheia.DBC.Formatter.WellFormedText.Foundations where

open import Data.Char using (Char)
open import Data.List using (List)
open import Data.List.Membership.Propositional using (_∈_)
import Data.List.NonEmpty as List⁺
open import Data.List.Relation.Unary.All using (All)
open import Data.Maybe using (just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Aletheia.DBC.Identifier using (Identifier)
open import Aletheia.DBC.Types using (DBCSignal; Always; When)
open import Aletheia.DBC.TextFormatter.Topology using (findMuxMaster)

-- `MasterCoherent sigs`: either there is no mux in the message
-- (`findMuxMaster sigs ≡ nothing`, i.e. every signal has presence
-- `Always`), or there is a master with all the coherence constraints:
--
--   * `findMuxMaster sigs ≡ just masterName` (some `When` slave exists,
--     and `masterName` is its master's identifier name);
--   * a signal with name matching `masterName` exists in `sigs`, has
--     `presence = Always`, and appears (somewhere) — its position
--     relative to slaves is enforced separately by the parser-side
--     `findMuxName` returning the first `IsMux` marker (which the
--     master is, post-emit);
--   * every `When` slave in `sigs` references the same `masterName`.
--
-- Master *position* (must come before slaves) is currently NOT in the
-- WF — `findMuxMaster` and `findMuxName` both return the first match,
-- so as long as exactly one master exists, the position constraint is
-- automatic.  Multi-master messages are forbidden by point 3 below.

data MasterCoherent : List DBCSignal → Set where
  -- No-mux case: no signal in the list has `When _ _` presence.
  mc-no-mux : ∀ {sigs}
            → findMuxMaster sigs ≡ nothing
            → MasterCoherent sigs

  -- Mux case: one master, every When slave references it.  The master
  -- signal record `masterSig` is exhibited by `Σ`-style witness fields.
  -- `findMuxMaster` returns `Maybe (List Char)`
  -- (matching `Identifier.name : List Char`).
  mc-mux : ∀ {sigs}
         → (masterName : List Char)
         → findMuxMaster sigs ≡ just masterName
         -- Master existence (some signal in sigs has name = masterName
         -- and presence = Always).  We carry the full signal record so
         -- downstream proofs can refer to it by name; the `∈` witness
         -- locates it in `sigs` (needed for the parser-side
         -- `findMuxName` resolution proof).
         → (masterSig : DBCSignal)
         → masterSig ∈ sigs
         → Identifier.name (DBCSignal.name masterSig) ≡ masterName
         → DBCSignal.presence masterSig ≡ Always
         -- Every When-clause references masterName.
         → All (λ s → (m : Identifier) (vs : List⁺.List⁺ _)
                    → DBCSignal.presence s ≡ When m vs
                    → Identifier.name m ≡ masterName)
               sigs
         → MasterCoherent sigs
