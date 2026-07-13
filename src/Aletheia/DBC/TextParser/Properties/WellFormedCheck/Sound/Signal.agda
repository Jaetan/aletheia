-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Signal-leaf soundness + completeness for the E.2 route (b) runtime checker
-- (`Aletheia.DBC.TextParser.WellFormedCheck`).  Each lemma bridges a checker
-- leaf's "issues ≡ []" verdict to the matching `Formatter.WellFormed` /
-- `.WellFormedText` predicate (soundness), and back (completeness).  Part of
-- slice 1's soundness tree (E2_ROUTE_B.md §5.1); reached by the `Sound.agda`
-- facade, which is added to `proofModules` at S1.6.
--
-- Built in sub-chunks, each type-checked standalone:
--   S1.3a  bounds     — `signalBounds-sound` / `-complete`  (this file, first)
--   S1.3b  presence   — `pGo-sound` / `-complete`
--   S1.3c  phys-valid — `pvGo-sound` / `-complete`
module Aletheia.DBC.TextParser.Properties.WellFormedCheck.Sound.Signal where

open import Data.List using (List; []; _∷_)
open import Data.List.NonEmpty using () renaming (_∷_ to _∷⁺_)
open import Data.Nat using (ℕ; suc; _≤_; _<_; _+_; _*_; _∸_)
open import Data.Nat.Properties using (_<?_; _≤?_)
open import Data.Product using (proj₁; proj₂)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import Aletheia.CAN.Constants using (max-physical-bits)
open import Aletheia.CAN.Endianness using (ByteOrder; LittleEndian; BigEndian)
open import Aletheia.CAN.Signal using (SignalDef)
open import Aletheia.DBC.Types using (DBCSignal; SignalPresence; Always; When)
open import Aletheia.DBC.Formatter.WellFormed using
  (WellFormedSignal; WellFormedSignalDef; PhysicallyValid; pv-LE; pv-BE)
open import Aletheia.DBC.Formatter.WellFormedText using
  (WellFormedTextPresence; wftp-always; wftp-when-single)
open import Aletheia.DBC.Validity.Combinators using
  (requireDec-sound; requireDec-complete)
open import Aletheia.DBC.Validity.ListLemmas using
  (++-≡[]-split; ++-≡[]-combine)
open import Aletheia.DBC.TextParser.WellFormedCheck using (checkSignalBounds; pGo; pvGo)

-- ── bounds (WF field `wf-sigs` = WellFormedSignal, via WellFormedSignalDef) ──
--
-- `checkSignalBounds s = requireDec (startBit <? max-physical-bits) …  ++ₗ
--  requireDec (bitLength <? suc max-physical-bits) …`, and `WellFormedSignalDef`
-- carries EXACTLY those two propositions (WellFormed.agda:41-44; `< suc n` is the
-- record's bitLength-bound form directly — no ≤/< conversion).  So the bridge is
-- a single `++-≡[]-split` + two `requireDec-sound`, assembling the nested record.

signalBounds-sound : ∀ (s : DBCSignal) → checkSignalBounds s ≡ [] → WellFormedSignal s
signalBounds-sound s eq = record
  { def-wf = record
      { startBit-bound  =
          requireDec-sound (SignalDef.startBit  (DBCSignal.signalDef s) <? max-physical-bits)
                           _ (proj₁ (++-≡[]-split eq))
      ; bitLength-bound =
          requireDec-sound (SignalDef.bitLength (DBCSignal.signalDef s) <? suc max-physical-bits)
                           _ (proj₂ (++-≡[]-split eq)) } }

signalBounds-complete : ∀ (s : DBCSignal) → WellFormedSignal s → checkSignalBounds s ≡ []
signalBounds-complete s wf = ++-≡[]-combine
  (requireDec-complete (SignalDef.startBit  (DBCSignal.signalDef s) <? max-physical-bits)
                       _ (WellFormedSignalDef.startBit-bound  (WellFormedSignal.def-wf wf)))
  (requireDec-complete (SignalDef.bitLength (DBCSignal.signalDef s) <? suc max-physical-bits)
                       _ (WellFormedSignalDef.bitLength-bound (WellFormedSignal.def-wf wf)))

-- ── presence (WF field `wfps` = WellFormedTextPresence) ──────────────────────
--
-- `pGo` (WellFormedCheck) already exposes the `SignalPresence` scrutinee, so the
-- bridge is a direct 3-way match with NO `requireDec` and NO `with`.  The text
-- form emits at most the FIRST mux-selector value, so a multi-value `When`
-- selector is lossy — `pGo` emits `MultiValueMuxSelector` there, which the
-- soundness `≡ []` premise refutes by `()`.  `WellFormedTextPresence`
-- (WellFormedText.agda:88-90) has exactly the two round-tripping shapes.

pGo-sound : ∀ (p : SignalPresence) (nm : String) → pGo p nm ≡ [] → WellFormedTextPresence p
pGo-sound Always                  _ _  = wftp-always
pGo-sound (When _ (_ ∷⁺ []))      _ _  = wftp-when-single
pGo-sound (When _ (_ ∷⁺ (_ ∷ _))) _ ()

pGo-complete : ∀ (p : SignalPresence) (nm : String) → WellFormedTextPresence p → pGo p nm ≡ []
pGo-complete Always             _ wftp-always      = refl
pGo-complete (When _ (_ ∷⁺ [])) _ wftp-when-single = refl

-- ── physical validity (WF field `pvs` = PhysicallyValid) — byteOrder-split ───
--
-- EXPOSED SCRUTINEE: `pvGo` takes the `ByteOrder` as an explicit arg, so this
-- lemma is proven over an ABSTRACT `bo`, and the Sound.agda caller (S1.6) does
-- `with DBCSignal.byteOrder s in eq` EXTERNALLY (proof-side with-in-eq is fine;
-- the checker side is already exposed).  The `bo-eq` reflection feeds `pv-{LE,BE}`'s
-- first arg directly; each requireDec fact (stated over `sd`) is `subst`-transported
-- through `sd-eq : signalDef s ≡ sd` into the `signalDef s` form the ctor needs.
-- NO `rewrite` over a parser goal (there is none — pvGo is pure arithmetic).

pvGo-sound : ∀ (bo : ByteOrder) (fb : ℕ) (sd : SignalDef) (nm : String) (s : DBCSignal)
  → DBCSignal.byteOrder s ≡ bo → DBCSignal.signalDef s ≡ sd
  → pvGo bo fb sd nm ≡ [] → PhysicallyValid fb s
pvGo-sound LittleEndian fb sd nm s bo-eq sd-eq eq =
  pv-LE bo-eq
    (subst (λ z → 1 ≤ SignalDef.bitLength z) (sym sd-eq)
      (requireDec-sound (1 ≤? SignalDef.bitLength sd) _ eq))
pvGo-sound BigEndian fb sd nm s bo-eq sd-eq eq =
  pv-BE bo-eq
    (subst (λ z → 1 ≤ SignalDef.bitLength z) (sym sd-eq)
      (requireDec-sound (1 ≤? SignalDef.bitLength sd) _ (proj₁ split1)))
    (subst (λ z → SignalDef.startBit z + SignalDef.bitLength z ∸ 1 < fb * 8) (sym sd-eq)
      (requireDec-sound (SignalDef.startBit sd + SignalDef.bitLength sd ∸ 1 <? fb * 8)
                        _ (proj₁ split2)))
    (subst (λ z → SignalDef.bitLength z ∸ 1 ≤ SignalDef.startBit z) (sym sd-eq)
      (requireDec-sound (SignalDef.bitLength sd ∸ 1 ≤? SignalDef.startBit sd)
                        _ (proj₂ split2)))
  where
    split1 = ++-≡[]-split eq
    split2 = ++-≡[]-split (proj₂ split1)

pvGo-complete : ∀ (fb : ℕ) (nm : String) (s : DBCSignal)
  → PhysicallyValid fb s
  → pvGo (DBCSignal.byteOrder s) fb (DBCSignal.signalDef s) nm ≡ []
pvGo-complete fb nm s (pv-LE bo-eq len-pos) rewrite bo-eq =
  requireDec-complete (1 ≤? SignalDef.bitLength (DBCSignal.signalDef s)) _ len-pos
pvGo-complete fb nm s (pv-BE bo-eq len-pos fits msb) rewrite bo-eq =
  ++-≡[]-combine
    (requireDec-complete (1 ≤? SignalDef.bitLength (DBCSignal.signalDef s)) _ len-pos)
    (++-≡[]-combine
      (requireDec-complete
        (SignalDef.startBit (DBCSignal.signalDef s) + SignalDef.bitLength (DBCSignal.signalDef s) ∸ 1
           <? fb * 8) _ fits)
      (requireDec-complete
        (SignalDef.bitLength (DBCSignal.signalDef s) ∸ 1 ≤? SignalDef.startBit (DBCSignal.signalDef s))
        _ msb))
