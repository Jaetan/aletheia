-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Signal-leaf soundness + completeness for the runtime checker
-- (`Aletheia.DBC.TextParser.WellFormedCheck`).  Each lemma bridges a checker
-- leaf's "issues ≡ []" verdict to the matching `Formatter.WellFormed` /
-- `.WellFormedText` predicate (soundness), and back (completeness).  Reached by
-- the `Sound.agda` facade.
--
-- The geometry leaves decide the shared frame-capacity deciders
-- (`DBC.Decidable.SignalGeometry`), so:
--   • `checkSignalBounds fb s ≡ []` yields the capacity bounds directly
--     (`signalBounds-caps`) and lifts to the type-level `WellFormedSignal`
--     ceiling under `fb ≤ 64` (`signalBounds-sound`);
--   • completeness runs from `PhysicallyValid` (whose conjuncts ARE the
--     capacity forms) rather than from the weaker ceiling record;
--   • `pvGo-sound` takes the two capacity bounds as premises on the LE arm
--     (they are decided by `checkSignalBounds`, not re-decided by `pvGo` —
--     one emission per condition).
module Aletheia.DBC.TextParser.Properties.WellFormedCheck.Sound.Signal where

open import Data.List using (List; []; _∷_)
open import Data.List.NonEmpty using () renaming (_∷_ to _∷⁺_)
open import Data.Nat using (ℕ; s≤s; _≤_; _<_; _+_; _*_)
open import Data.Nat.Properties using (≤-trans; <-≤-trans; *-monoˡ-≤; m<m+n)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import Aletheia.CAN.Endianness using (ByteOrder; LittleEndian; BigEndian)
open import Aletheia.CAN.Endianness.Properties using (fits⇒bl≤cap)
open import Aletheia.CAN.Signal using (SignalDef)
open import Aletheia.DBC.Types using (DBCSignal; SignalPresence; Always; When)
open import Aletheia.DBC.Decidable.SignalGeometry using
  (startBitInFrame?; bitLengthInFrame?; bitLengthPositive?; signalFitsFrame?)
open import Aletheia.DBC.Formatter.WellFormed using
  (WellFormedSignal; WellFormedSignalDef; PhysicallyValid; pv-LE; pv-BE)
open import Aletheia.DBC.Formatter.WellFormedText using
  (WellFormedTextPresence; wftp-always; wftp-when-single)
open import Aletheia.DBC.Validity.Combinators using
  (requireDec-sound; requireDec-complete)
open import Aletheia.DBC.Validity.ListLemmas using
  (++-≡[]-split; ++-≡[]-combine)
open import Aletheia.DBC.TextParser.WellFormedCheck using (checkSignalBounds; pGo; pvGo)

-- ── bounds (frame-capacity forms; WF field `wf-sigs` via the ceiling) ────────

signalBounds-caps : ∀ (fb : ℕ) (s : DBCSignal) → checkSignalBounds fb s ≡ []
  → (SignalDef.startBit (DBCSignal.signalDef s) < fb * 8)
    × (SignalDef.bitLength (DBCSignal.signalDef s) ≤ fb * 8)
signalBounds-caps fb s eq =
  requireDec-sound (startBitInFrame? fb (SignalDef.startBit (DBCSignal.signalDef s)))
                   _ (proj₁ (++-≡[]-split eq)) ,
  requireDec-sound (bitLengthInFrame? fb (SignalDef.bitLength (DBCSignal.signalDef s)))
                   _ (proj₂ (++-≡[]-split eq))

-- Ceiling lift: dlcBytes ≤ 64 turns both capacity bounds into the
-- `WellFormedSignalDef` record (64 * 8 reduces to max-physical-bits).
signalBounds-sound : ∀ (fb : ℕ) (s : DBCSignal) → fb ≤ 64
  → checkSignalBounds fb s ≡ [] → WellFormedSignal s
signalBounds-sound fb s fb≤64 eq = record
  { def-wf = record
      { startBit-bound  = <-≤-trans (proj₁ caps) (*-monoˡ-≤ 8 fb≤64)
      ; bitLength-bound = s≤s (≤-trans (proj₂ caps) (*-monoˡ-≤ 8 fb≤64))
      } }
  where caps = signalBounds-caps fb s eq

-- Completeness runs from PhysicallyValid: its LE conjuncts are the two
-- capacity forms verbatim; the BE fits conjunct implies both.
signalBounds-complete : ∀ (fb : ℕ) (s : DBCSignal)
  → PhysicallyValid fb s → checkSignalBounds fb s ≡ []
signalBounds-complete fb s (pv-LE _ _ sbF blF) = ++-≡[]-combine
  (requireDec-complete (startBitInFrame? fb (SignalDef.startBit (DBCSignal.signalDef s))) _ sbF)
  (requireDec-complete (bitLengthInFrame? fb (SignalDef.bitLength (DBCSignal.signalDef s))) _ blF)
signalBounds-complete fb s (pv-BE _ lp fits) = ++-≡[]-combine
  (requireDec-complete (startBitInFrame? fb (SignalDef.startBit (DBCSignal.signalDef s))) _
    (<-≤-trans (m<m+n (SignalDef.startBit (DBCSignal.signalDef s)) lp) fits))
  (requireDec-complete (bitLengthInFrame? fb (SignalDef.bitLength (DBCSignal.signalDef s))) _
    (fits⇒bl≤cap fb (SignalDef.startBit (DBCSignal.signalDef s))
       (SignalDef.bitLength (DBCSignal.signalDef s)) fits))

-- ── presence (WF field `wfps` = WellFormedTextPresence) ──────────────────────
--
-- `pGo` (WellFormedCheck) already exposes the `SignalPresence` scrutinee, so the
-- bridge is a direct 3-way match with NO `requireDec` and NO `with`.  The text
-- form emits at most the FIRST mux-selector value, so a multi-value `When`
-- selector is lossy — `pGo` emits `MultiValueMuxSelector` there, which the
-- soundness `≡ []` premise refutes by `()`.  `WellFormedTextPresence`
-- (Formatter/WellFormedText.agda, `WellFormedTextPresence`) has exactly the two
-- round-tripping shapes.

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
-- lemma is proven over an ABSTRACT `bo` with `bo-eq : DBCSignal.byteOrder s ≡ bo`
-- as an explicit premise, so the caller instantiates `bo := DBCSignal.byteOrder s`
-- and discharges it with `refl` — no `with`-abstraction on either side.  The
-- `bo-eq` reflection feeds `pv-{LE,BE}`'s first arg directly; each requireDec
-- fact (stated over `sd`) is `subst`-transported
-- through `sd-eq : signalDef s ≡ sd` into the `signalDef s` form the ctor needs.
-- The LE arm's capacity conjuncts arrive as premises (from
-- `signalBounds-caps` — decided by `checkSignalBounds`, not re-decided here).

pvGo-sound : ∀ (bo : ByteOrder) (fb : ℕ) (sd : SignalDef) (nm : String) (s : DBCSignal)
  → DBCSignal.byteOrder s ≡ bo → DBCSignal.signalDef s ≡ sd
  → SignalDef.startBit sd < fb * 8
  → SignalDef.bitLength sd ≤ fb * 8
  → pvGo bo fb sd nm ≡ [] → PhysicallyValid fb s
pvGo-sound LittleEndian fb sd nm s bo-eq sd-eq sbF blF eq =
  pv-LE bo-eq
    (subst (λ z → 1 ≤ SignalDef.bitLength z) (sym sd-eq)
      (requireDec-sound (bitLengthPositive? (SignalDef.bitLength sd)) _ eq))
    (subst (λ z → SignalDef.startBit z < fb * 8) (sym sd-eq) sbF)
    (subst (λ z → SignalDef.bitLength z ≤ fb * 8) (sym sd-eq) blF)
pvGo-sound BigEndian fb sd nm s bo-eq sd-eq _ _ eq =
  pv-BE bo-eq
    (subst (λ z → 1 ≤ SignalDef.bitLength z) (sym sd-eq)
      (requireDec-sound (bitLengthPositive? (SignalDef.bitLength sd)) _ (proj₁ split1)))
    (subst (λ z → SignalDef.startBit z + SignalDef.bitLength z ≤ fb * 8) (sym sd-eq)
      (requireDec-sound (signalFitsFrame? fb (SignalDef.startBit sd) (SignalDef.bitLength sd))
                        _ (proj₂ split1)))
  where
    split1 = ++-≡[]-split eq

pvGo-complete : ∀ (fb : ℕ) (nm : String) (s : DBCSignal)
  → PhysicallyValid fb s
  → pvGo (DBCSignal.byteOrder s) fb (DBCSignal.signalDef s) nm ≡ []
pvGo-complete fb nm s (pv-LE bo-eq len-pos _ _) rewrite bo-eq =
  requireDec-complete (bitLengthPositive? (SignalDef.bitLength (DBCSignal.signalDef s))) _ len-pos
pvGo-complete fb nm s (pv-BE bo-eq len-pos fits) rewrite bo-eq =
  ++-≡[]-combine
    (requireDec-complete (bitLengthPositive? (SignalDef.bitLength (DBCSignal.signalDef s))) _ len-pos)
    (requireDec-complete
      (signalFitsFrame? fb (SignalDef.startBit (DBCSignal.signalDef s))
        (SignalDef.bitLength (DBCSignal.signalDef s))) _ fits)
