-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- `resolveSignalList`-roundtrip.
--
-- Proves that on the formatter-emitted RawSignal list, `resolveSignalList`
-- recovers the original `List DBCSignal` exactly.  The conversion has two
-- substeps inside `resolveSignalList`:
--
--   1. Compute `findMuxName raws` (the parser-side master discovery).
--   2. Walk the list, calling `buildSignal fb (findMuxName raws) raw_i`
--      for each signal; combine into `Maybe (List DBCSignal)`.
--
-- For the roundtrip to close we need:
--   * `findMuxName (map (expectedRawOfDBC master fb) sigs) ≡ <master Id>`
--     under `MasterCoherent sigs` (case-split on `mc-no-mux`/`mc-mux`).
--   * `buildSignal fb m (expectedRawOfDBC master fb sig) ≡ just sig` for
--     each signal, under `WellFormedSignal` + `PhysicallyValid` (for
--     startBit/bitLength) + `WellFormedTextPresence` (for resolvePresence)
--     + master-Identifier coherence (for When-presence sigs only).
--
-- Composition: induct over the signal list with the master fixed at the
-- top.  Each step calls `buildSignal-roundtrip` then recurses.  Empty
-- list closes via `just []`.
--
-- A later composer combines this with `parseSignalLines-roundtrip` and a
-- BO_-header `messageHeaderFmt` to close `parseMessage-roundtrip`.
module Aletheia.DBC.TextParser.Properties.Topology.Resolve where

open import Data.Bool using (true; false)
open import Data.Bool.Properties using (T-irrelevant)
open import Data.Char using (Char) renaming (_≟_ to _≟ᶜ_)
import Data.List.Properties as ListProps
open import Data.List using (List; []; _∷_; map)
  renaming ()
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.NonEmpty as List⁺ using (List⁺; _∷_)
open import Data.List.Relation.Unary.All as All using (All)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _≤_)
open import Data.Product using (_×_; _,_; Σ)
open import Data.Sum using (inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import Aletheia.DBC.Identifier using (Identifier; mkIdent)
open import Aletheia.DBC.Types using
  (DBCSignal; SignalPresence; Always; When; clearVds)

open import Aletheia.CAN.Endianness using
  (BigEndian; convertStartBit; unconvertStartBit)
open import Aletheia.CAN.Endianness.Properties.StartBit using
  (unconvertStartBit-roundtrip; fits⇒∸<; fits⇒1≤n; fits⇒bl≤cap;
   unconvertSB-BE-inFrame; unconvertSB-BE-noWrap)
open import Aletheia.CAN.Signal using (SignalDef)
open import Aletheia.DBC.Decidable.SignalGeometry using (geometryRefusal)
open import Aletheia.DBC.Decidable.SignalGeometry.Properties using
  (geometryRefusal-accept-LE; geometryRefusal-accept-BE)

open import Aletheia.DBC.Formatter.WellFormed using
  (WellFormedSignal;
   PhysicallyValid; pv-LE; pv-BE)
open import Aletheia.DBC.Formatter.WellFormedText using
  (WellFormedTextPresence; wftp-always; wftp-when-single;
   MasterCoherent; mc-no-mux; mc-mux)
open import Aletheia.DBC.TextFormatter.Topology using
  (findMuxMaster)

open import Aletheia.DBC.TextParser.Topology.Foundations using
  (IsMux)
open import Aletheia.DBC.TextParser.Topology using
  (findMuxName; buildSignal; buildAllRaw;
   resolveSignalList; finishSignalGate)
open import Aletheia.DBC.TextParser.Properties.Topology.SignalList using
  (expectedMux; expectedRawOfDBC)


-- ============================================================================
-- IDENTIFIER EQUALITY FROM NAME EQUALITY
-- ============================================================================

-- Two Identifiers with equal `name` fields are propositionally equal: the
-- only other field is `valid : T (validIdentifierᵇ name)`, which is
-- T-irrelevant once the names match.  Mirrors `_≟ᴵ_`'s `yes refl` arm.
ident-eq-from-name : ∀ (i j : Identifier)
  → Identifier.name i ≡ Identifier.name j
  → i ≡ j
ident-eq-from-name (mkIdent cs₁ v₁) (mkIdent .cs₁ v₂) refl =
  cong (mkIdent cs₁) (T-irrelevant v₁ v₂)


-- ============================================================================
-- GATE ACCEPTANCE + CONVERT ∘ UNCONVERT ≡ id (abstract byte order)
-- ============================================================================

-- Both helpers keep the signal's byte order ABSTRACT in their statements
-- (so the field-recovery rewrite below never rewrites `byteOrder sig`
-- inside the record, preserving record-η against `clearVds sig`) and
-- dispatch on the PhysicallyValid constructor internally.

-- The formatter-emitted raw geometry passes the shared entry gate.
gate-accepts : ∀ (sig : DBCSignal) (fb : ℕ)
  → PhysicallyValid fb sig
  → geometryRefusal fb (DBCSignal.byteOrder sig)
      (unconvertStartBit fb (DBCSignal.byteOrder sig)
        (SignalDef.startBit (DBCSignal.signalDef sig))
        (SignalDef.bitLength (DBCSignal.signalDef sig)))
      (SignalDef.bitLength (DBCSignal.signalDef sig))
    ≡ nothing
gate-accepts sig fb (pv-LE bo-eq lp sbF blF) rewrite bo-eq =
  geometryRefusal-accept-LE fb
    (SignalDef.startBit (DBCSignal.signalDef sig))
    (SignalDef.bitLength (DBCSignal.signalDef sig)) lp sbF blF
gate-accepts sig fb (pv-BE bo-eq lp fits) rewrite bo-eq =
  geometryRefusal-accept-BE fb
    (unconvertStartBit fb BigEndian
      (SignalDef.startBit (DBCSignal.signalDef sig))
      (SignalDef.bitLength (DBCSignal.signalDef sig)))
    (SignalDef.bitLength (DBCSignal.signalDef sig))
    lp
    (unconvertSB-BE-inFrame fb
      (SignalDef.startBit (DBCSignal.signalDef sig))
      (SignalDef.bitLength (DBCSignal.signalDef sig))
      (fits⇒1≤n fb (SignalDef.startBit (DBCSignal.signalDef sig))
        (SignalDef.bitLength (DBCSignal.signalDef sig)) lp fits))
    (fits⇒bl≤cap fb (SignalDef.startBit (DBCSignal.signalDef sig))
      (SignalDef.bitLength (DBCSignal.signalDef sig)) fits)
    (unconvertSB-BE-noWrap fb
      (SignalDef.startBit (DBCSignal.signalDef sig))
      (SignalDef.bitLength (DBCSignal.signalDef sig)) lp fits)

-- Closing the start-bit roundtrip: LE is identity on both sides; BE
-- delegates to `unconvertStartBit-roundtrip` with the strict in-frame
-- form derived from the fits conjunct.
convert-unconvert-id :
    ∀ (sig : DBCSignal) (fb : ℕ)
  → PhysicallyValid fb sig
  → convertStartBit fb (DBCSignal.byteOrder sig)
      (unconvertStartBit fb (DBCSignal.byteOrder sig)
        (SignalDef.startBit (DBCSignal.signalDef sig))
        (SignalDef.bitLength (DBCSignal.signalDef sig)))
      (SignalDef.bitLength (DBCSignal.signalDef sig))
    ≡ SignalDef.startBit (DBCSignal.signalDef sig)
convert-unconvert-id sig fb (pv-LE bo-eq _ _ _) rewrite bo-eq = refl
convert-unconvert-id sig fb (pv-BE bo-eq lp fits) rewrite bo-eq =
  unconvertStartBit-roundtrip fb
    (SignalDef.startBit (DBCSignal.signalDef sig))
    (SignalDef.bitLength (DBCSignal.signalDef sig))
    lp
    (fits⇒∸< fb (SignalDef.startBit (DBCSignal.signalDef sig))
      (SignalDef.bitLength (DBCSignal.signalDef sig)) lp fits)

-- ============================================================================
-- BUILDSIGNAL OUTPUT RECORD ≡ sig — the unifying field-recovery lemma
-- ============================================================================

-- Given that resolvePresence delivers a presence equal to `sig.presence`,
-- the buildSignal output — the shared geometry gate applied to the
-- formatter-emitted raw geometry, wrapping the reassembled record —
-- equals `just (inj₂ (clearVds sig))`.  Closes by:
--   1. `gate-accepts` rewrites the gate verdict to `nothing`.
--   2. `convert-unconvert-id` collapses the convertStartBit ∘
--      unconvertStartBit composition.
--   3. `presence-eq` substitutes presence-result for sig.presence;
--      record-η closes the equation.
-- buildSignal hardcodes `valueDescriptions = []`, so the recovered
-- record matches `clearVds sig` (sig modulo the cleared VAL_ field).  The
-- Universal at the top-level layer threads `attachValueDescs ∘
-- collectFromMessages ≡ id` on the cleared form (Refine bridge)
-- post-buildSignal.
buildSignal-fields-recover :
    ∀ (sig : DBCSignal) (fb : ℕ) (presence-result : SignalPresence)
  → PhysicallyValid fb sig
  → presence-result ≡ DBCSignal.presence sig
  → just (finishSignalGate
       (geometryRefusal fb (DBCSignal.byteOrder sig)
          (unconvertStartBit fb (DBCSignal.byteOrder sig)
             (SignalDef.startBit (DBCSignal.signalDef sig))
             (SignalDef.bitLength (DBCSignal.signalDef sig)))
          (SignalDef.bitLength (DBCSignal.signalDef sig)))
       (DBCSignal.name sig)
       (record
         { name      = DBCSignal.name sig
         ; signalDef = record
             { startBit  = convertStartBit fb (DBCSignal.byteOrder sig)
                             (unconvertStartBit fb (DBCSignal.byteOrder sig)
                                (SignalDef.startBit (DBCSignal.signalDef sig))
                                (SignalDef.bitLength (DBCSignal.signalDef sig)))
                             (SignalDef.bitLength (DBCSignal.signalDef sig))
             ; bitLength = SignalDef.bitLength (DBCSignal.signalDef sig)
             ; isSigned  = SignalDef.isSigned (DBCSignal.signalDef sig)
             ; factor    = SignalDef.factor (DBCSignal.signalDef sig)
             ; offset    = SignalDef.offset (DBCSignal.signalDef sig)
             ; minimum   = SignalDef.minimum (DBCSignal.signalDef sig)
             ; maximum   = SignalDef.maximum (DBCSignal.signalDef sig)
             }
         ; byteOrder = DBCSignal.byteOrder sig
         ; unit      = DBCSignal.unit sig
         ; presence  = presence-result
         ; receivers = DBCSignal.receivers sig
         ; valueDescriptions = []
         }))
    ≡ just (inj₂ (clearVds sig))
buildSignal-fields-recover sig fb presence-result pv presence-eq
  rewrite gate-accepts sig fb pv
        | convert-unconvert-id sig fb pv
        | presence-eq = refl


-- ============================================================================
-- BUILDSIGNAL-ROUNDTRIP — per-presence-shape lemmas
-- ============================================================================

-- Always case: buildSignal succeeds for ANY master `m`, regardless of
-- whether master is nothing or just _ — the muxMarker chosen by
-- expectedMux is NotMux (master /= name OR master = nothing) or IsMux
-- (master = name), and `resolvePresence m _ = just Always` for both
-- markers (resolvePresence's first three pattern-matches all yield
-- `just Always`).  Hence we case-split on (master, name-match) but
-- collapse all branches to the same fields-recover application.
--
-- The result is `just (inj₂ (clearVds sig))` (buildSignal hardcodes
-- vds = []); the Universal threads `attachValueDescs ∘ collectFromMessages
-- ≡ id` post-buildSignal to recover the original.
buildSignal-roundtrip-Always :
    ∀ (master : Maybe (List Char)) (fb : ℕ) (sig : DBCSignal)
      (m : Maybe Identifier)
  → DBCSignal.presence sig ≡ Always
  → PhysicallyValid fb sig
  → buildSignal fb m (expectedRawOfDBC master fb sig)
    ≡ just (inj₂ (clearVds sig))
buildSignal-roundtrip-Always master fb sig m presence-eq pv
  rewrite presence-eq with master
... | nothing =
  buildSignal-fields-recover sig fb Always pv (sym presence-eq)
... | just mName with ⌊ ListProps.≡-dec _≟ᶜ_
                       (Identifier.name (DBCSignal.name sig)) mName ⌋
...   | true =
  buildSignal-fields-recover sig fb Always pv (sym presence-eq)
...   | false =
  buildSignal-fields-recover sig fb Always pv (sym presence-eq)

-- When case (singleton via WellFormedTextPresence): buildSignal succeeds
-- ONLY when `m = just <Identifier with name = sig-master's name>` —
-- otherwise resolvePresence fails (m=nothing) or builds the wrong
-- presence (wrong identifier).  Take m = just sig-master directly via
-- the `m-eq` hypothesis (the caller derives this from MasterCoherent
-- + findMuxName-result).
buildSignal-roundtrip-When :
    ∀ (master : Maybe (List Char)) (fb : ℕ) (sig : DBCSignal)
      (m sig-master : Identifier) (v : ℕ)
  → DBCSignal.presence sig ≡ When sig-master (v ∷ [])
  → m ≡ sig-master
  → PhysicallyValid fb sig
  → buildSignal fb (just m) (expectedRawOfDBC master fb sig)
    ≡ just (inj₂ (clearVds sig))
buildSignal-roundtrip-When master fb sig m sig-master v presence-eq m-eq pv
  rewrite presence-eq | m-eq =
  buildSignal-fields-recover sig fb (When sig-master (v ∷ []))
                              pv (sym presence-eq)


-- ============================================================================
-- findMuxMaster ≡ nothing  ⇒  all signals are `Always`
-- ============================================================================

-- `findMuxMaster` returns `nothing` iff no signal has `When _ _` presence.
-- The forward direction: if findMuxMaster returns nothing, every signal
-- is `Always`.  Used to discharge mc-no-mux's signals-side WF.
findMuxMaster-nothing→all-Always :
    ∀ (sigs : List DBCSignal)
  → findMuxMaster sigs ≡ nothing
  → All (λ s → DBCSignal.presence s ≡ Always) sigs
findMuxMaster-nothing→all-Always [] _ = All.[]
findMuxMaster-nothing→all-Always (s ∷ rest) eq
  with DBCSignal.presence s in p-eq
... | Always   = p-eq All.∷ findMuxMaster-nothing→all-Always rest eq


-- ============================================================================
-- findMuxName UNDER mc-no-mux  ⇒  nothing
-- ============================================================================

-- All-Always implies all expectedMux are NotMux (under master=nothing,
-- expectedMux = NotMux for Always; under master=just _, expectedMux is
-- IsMux/NotMux depending on name match — but in mc-no-mux, master =
-- findMuxMaster sigs = nothing).  Hence findMuxName recurses through
-- the entire list and returns nothing.
findMuxName-on-no-mux :
    ∀ (fb : ℕ) (sigs : List DBCSignal)
  → All (λ s → DBCSignal.presence s ≡ Always) sigs
  → findMuxName (map (expectedRawOfDBC nothing fb) sigs) ≡ nothing
findMuxName-on-no-mux fb [] _ = refl
findMuxName-on-no-mux fb (s ∷ rest) (p-eq All.∷ rest-eqs)
  rewrite p-eq = findMuxName-on-no-mux fb rest rest-eqs


-- ============================================================================
-- expectedMux IsMux ⇒ presence Always + name match
-- ============================================================================

-- The IsMux clause of `expectedMuxFor` only fires when (master = just m,
-- presence = Always, nameEq? name m = true).  Inverting: if expectedMux
-- (just m) sig ≡ IsMux, then sig.presence = Always and the nameEq?
-- decides equal — i.e. sig's name equals m.
private
  -- `nameEq? a b ≡ true` implies `a ≡ b` via the `⌊_⌋ ∘ ≡-dec _≟ᶜ_` chain.
  nameEq?-true→eq : ∀ (a b : List Char) → ⌊ ListProps.≡-dec _≟ᶜ_ a b ⌋ ≡ true → a ≡ b
  nameEq?-true→eq a b eq with ListProps.≡-dec _≟ᶜ_ a b
  ... | yes p = p

-- Inversion: under `expectedMux (just m) sig ≡ IsMux`, derive the two
-- preconditions: sig.presence = Always and sig.name's name = m.
expectedMux-IsMux-inv :
    ∀ (m : List Char) (sig : DBCSignal)
  → expectedMux (just m) sig ≡ IsMux
  → DBCSignal.presence sig ≡ Always
    × Identifier.name (DBCSignal.name sig) ≡ m
expectedMux-IsMux-inv m sig eq with DBCSignal.presence sig
expectedMux-IsMux-inv m sig eq | Always
  with ListProps.≡-dec _≟ᶜ_ (Identifier.name (DBCSignal.name sig)) m
... | yes name-eq = refl , name-eq


-- ============================================================================
-- findMuxName UNDER mc-mux  ⇒  just <id> with name ≡ masterName
-- ============================================================================

-- Locate masterSig in sigs (via `_∈_`) and prove findMuxName returns
-- just an Identifier with the correct name.  Inducts on the membership
-- witness.
--
-- Two cases per recursion step: either the head's expectedMux is IsMux
-- (findMuxName stops here, regardless of whether head is masterSig or
-- a duplicate; the IsMux-inv lemma extracts name = masterName), or the
-- head is NotMux/SelBy (findMuxName recurses; the membership witness
-- must be `there w-rest` because `here _` would force IsMux via
-- expectedMux's clause structure).
findMuxName-finds-master :
    ∀ (fb : ℕ) (sigs : List DBCSignal) (masterName : List Char)
      (masterSig : DBCSignal)
  → masterSig ∈ sigs
  → DBCSignal.presence masterSig ≡ Always
  → Identifier.name (DBCSignal.name masterSig) ≡ masterName
  → Σ Identifier (λ id →
       Identifier.name id ≡ masterName ×
       findMuxName (map (expectedRawOfDBC (just masterName) fb) sigs)
         ≡ just id)
-- Case `here refl`: masterSig is the head (i.e. s ≡ masterSig); both
-- preconditions transfer to s, so expectedMux (just masterName) s
-- reduces to IsMux via the head-Always + name-match clause.  Find-
-- MuxName then returns just (DBCSignal.name s).
--
-- Case `there w`: case-split on (sig.presence, name-match) — the same
-- structure as expectedMuxFor's clauses — to determine whether
-- findMuxName stops at the head (s.presence=Always + s.name=masterName
-- ⇒ IsMux) or recurses (other shapes).  This pattern avoids the
-- BothMux case entirely (expectedMux never produces it).
findMuxName-finds-master fb (s ∷ rest) masterName .s
                         (here refl) pres-eq name-eq
  rewrite pres-eq
  with ListProps.≡-dec _≟ᶜ_ (Identifier.name (DBCSignal.name s)) masterName
... | yes _   = DBCSignal.name s , name-eq , refl
... | no  ¬eq = ⊥-elim (¬eq name-eq)
  where open import Data.Empty using (⊥-elim)
findMuxName-finds-master fb (s ∷ rest) masterName masterSig
                         (there w) pres-eq name-eq
  with DBCSignal.presence s in head-pres-eq
-- s.presence = When _ _: expectedMux = SelBy v; findMuxName recurses
-- (the catch-all clause `_` of `findMuxName`).
... | When _ (v ∷ _) =
  findMuxName-finds-master fb rest masterName masterSig w pres-eq name-eq
-- s.presence = Always: dispatch on name-match.
... | Always
  with ListProps.≡-dec _≟ᶜ_ (Identifier.name (DBCSignal.name s)) masterName
... | yes head-name-eq =
  -- expectedMux = IsMux; findMuxName stops here.
  DBCSignal.name s , head-name-eq , refl
... | no _ =
  -- expectedMux = NotMux; findMuxName recurses on rest.
  findMuxName-finds-master fb rest masterName masterSig w pres-eq name-eq


-- ============================================================================
-- PER-SIGNAL `SigOK` PREDICATE
-- ============================================================================

-- Bundles the per-signal preconditions buildSignal needs at a given
-- (m, fb).  Exists in two shapes per `SignalPresence` — the buildSignal
-- target reconstruction has different m-requirements for Always vs When.
data SigOK (m : Maybe Identifier) (fb : ℕ) : DBCSignal → Set where
  sigok-always : ∀ {sig}
               → DBCSignal.presence sig ≡ Always
               → PhysicallyValid fb sig
               → SigOK m fb sig
  sigok-when   : ∀ {sig sig-master v}
               → DBCSignal.presence sig ≡ When sig-master (v ∷ [])
               → m ≡ just sig-master
               → PhysicallyValid fb sig
               → SigOK m fb sig


-- ============================================================================
-- buildAll-roundtrip — list-level induction
-- ============================================================================

-- Inducts on `All (SigOK m fb) sigs`.  Each step calls buildSignal-
-- roundtrip (Always or When branch per the SigOK constructor) and
-- recurses on the tail.
--
-- The result is `just (inj₂ (map clearVds sigs))` (not `just sigs`); the
-- per-message buildMessage-roundtrip then bridges via the
-- attachValueDescs-on-collected lemma at the Universal layer.
buildAllRaw-roundtrip :
    ∀ (master : Maybe (List Char)) (fb : ℕ) (m : Maybe Identifier)
      (sigs : List DBCSignal)
  → All (SigOK m fb) sigs
  → buildAllRaw fb m (map (expectedRawOfDBC master fb) sigs)
    ≡ just (inj₂ (map clearVds sigs))
buildAllRaw-roundtrip _ _ _ [] All.[] = refl
buildAllRaw-roundtrip master fb m (sig ∷ rest)
                      (sigok All.∷ rest-oks) =
  go sigok
  where
    rec : buildAllRaw fb m (map (expectedRawOfDBC master fb) rest)
        ≡ just (inj₂ (map clearVds rest))
    rec = buildAllRaw-roundtrip master fb m rest rest-oks

    go : SigOK m fb sig
       → buildAllRaw fb m (map (expectedRawOfDBC master fb) (sig ∷ rest))
         ≡ just (inj₂ (clearVds sig ∷ map clearVds rest))
    go (sigok-always pres-eq pv)
      rewrite buildSignal-roundtrip-Always master fb sig m pres-eq pv
            | rec = refl
    go (sigok-when {sig-master = sig-master} {v = v}
                   pres-eq refl pv)
      rewrite buildSignal-roundtrip-When master fb sig sig-master
                                          sig-master v pres-eq refl pv
            | rec = refl


-- ============================================================================
-- DERIVING `All (SigOK m fb) sigs` from MasterCoherent + per-signal WF
-- ============================================================================

-- mc-no-mux case: every sig is `Always` (via findMuxMaster-nothing→all-
-- Always); each `SigOK` is sigok-always; m can be anything.
all-sigOK-no-mux :
    ∀ (fb : ℕ) (m : Maybe Identifier) (sigs : List DBCSignal)
  → All (PhysicallyValid fb) sigs
  → All (λ s → DBCSignal.presence s ≡ Always) sigs
  → All (SigOK m fb) sigs
all-sigOK-no-mux _  _ [] _ _ = All.[]
all-sigOK-no-mux fb m (sig ∷ rest)
                 (pv All.∷ rest-pvs)
                 (pres-eq All.∷ rest-pres-eqs) =
  sigok-always pres-eq pv All.∷
    all-sigOK-no-mux fb m rest rest-pvs rest-pres-eqs

-- mc-mux case: each sig's SigOK comes from per-signal WFTP — Always
-- gives sigok-always (m-irrelevant); When gives sigok-when with the
-- m ≡ just sig-master witness derived from MasterCoherent's coh-list +
-- name equality + ident-eq-from-name.
all-sigOK-mc-mux :
    ∀ (fb : ℕ) (sigs : List DBCSignal) (id : Identifier)
      (masterName : List Char)
  → Identifier.name id ≡ masterName
  → All (PhysicallyValid fb) sigs
  → All (λ s → WellFormedTextPresence (DBCSignal.presence s)) sigs
  → All (λ s → (m : Identifier) (vs : List⁺ ℕ)
             → DBCSignal.presence s ≡ When m vs
             → Identifier.name m ≡ masterName)
        sigs
  → All (SigOK (just id) fb) sigs
all-sigOK-mc-mux _ [] _ _ _ _ _ _ = All.[]
all-sigOK-mc-mux fb (sig ∷ rest) id masterName id-name-eq
                 (pv All.∷ rest-pvs)
                 (wfp All.∷ rest-wfps)
                 (coh All.∷ rest-cohs) =
  sigOK-from-wfp fb sig id masterName id-name-eq pv wfp coh
    All.∷
    all-sigOK-mc-mux fb rest id masterName id-name-eq
                     rest-pvs rest-wfps rest-cohs
  where
    -- Per-signal SigOK derivation under WellFormedTextPresence + the
    -- coh-clause from MasterCoherent.  Cases on (presence, wfp)
    -- simultaneously.  Always: sigok-always.  When sm (v ∷ []): use the
    -- coh-clause to extract sm.name = masterName; then by name-eq on
    -- both sides + ident-eq-from-name, id ≡ sm; cong just gives the
    -- m-eq witness for sigok-when.
    sigOK-from-wfp : ∀ (fb : ℕ) (sig : DBCSignal) (id : Identifier)
                       (masterName : List Char)
      → Identifier.name id ≡ masterName
      → PhysicallyValid fb sig
      → WellFormedTextPresence (DBCSignal.presence sig)
      → ((m : Identifier) (vs : List⁺ ℕ)
           → DBCSignal.presence sig ≡ When m vs
           → Identifier.name m ≡ masterName)
      → SigOK (just id) fb sig
    sigOK-from-wfp fb sig id masterName id-name-eq pv wfp coh =
      helper (DBCSignal.presence sig) refl wfp
      where
        helper : ∀ (p : SignalPresence)
               → DBCSignal.presence sig ≡ p
               → WellFormedTextPresence p
               → SigOK (just id) fb sig
        helper Always              p-eq wftp-always       =
          sigok-always p-eq pv
        helper (When sm (v ∷ [])) p-eq wftp-when-single =
          sigok-when p-eq (cong just id-eq-sm) pv
          where
            sm-name-eq : Identifier.name sm ≡ masterName
            sm-name-eq = coh sm (v List⁺.∷ []) p-eq

            id-eq-sm : id ≡ sm
            id-eq-sm = ident-eq-from-name id sm
                         (trans id-name-eq (sym sm-name-eq))


-- ============================================================================
-- TOP-LEVEL: resolveSignalList-roundtrip
-- ============================================================================

-- Composes all the sub-lemmas: case-split on MasterCoherent to determine
-- the master's identity (or absence), use findMuxName-on-no-mux /
-- findMuxName-finds-master to compute findMuxName, derive the per-signal
-- All (SigOK m fb) sigs, then apply buildAllRaw-roundtrip.
--
-- Frame `master = findMuxMaster sigs` baked into the goal: the formatter
-- uses `master = findMuxMaster sigs`, so the parser-side roundtrip
-- closes directly on this expression.
--
-- The result is `just (inj₂ (map clearVds sigs))` (not `just sigs`); the
-- per-message and Universal layers thread `attachValueDescs` to bridge
-- the cleared form back to the original.
-- The WellFormedSignal and `fb ≤ 64` hypotheses are retained for the
-- established call shape (buildMessage-roundtrip supplies them from
-- MessageWF); the proof itself runs on the PhysicallyValid capacity
-- conjuncts alone.
resolveSignalList-roundtrip :
    ∀ (fb : ℕ) (sigs : List DBCSignal)
  → fb ≤ 64
  → All WellFormedSignal sigs
  → All (PhysicallyValid fb) sigs
  → All (λ s → WellFormedTextPresence (DBCSignal.presence s)) sigs
  → MasterCoherent sigs
  → resolveSignalList fb
       (map (expectedRawOfDBC (findMuxMaster sigs) fb) sigs)
    ≡ just (inj₂ (map clearVds sigs))
resolveSignalList-roundtrip fb sigs _ _ pvs wfps mc =
  go mc
  where
    -- Inside `resolveSignalList`, the call is `buildAllRaw fb (findMuxName
    -- raws) raws` where `raws = map (expectedRawOfDBC master fb) sigs`.
    -- We first compute `findMuxName raws`, then apply `buildAllRaw-
    -- roundtrip` with the appropriate SigOK list.
    go : MasterCoherent sigs
       → resolveSignalList fb
            (map (expectedRawOfDBC (findMuxMaster sigs) fb) sigs)
         ≡ just (inj₂ (map clearVds sigs))
    go (mc-no-mux nothing-eq)
      rewrite nothing-eq =
      let all-always = findMuxMaster-nothing→all-Always sigs nothing-eq
          all-ok     = all-sigOK-no-mux fb nothing sigs pvs all-always
          fmn-eq     = findMuxName-on-no-mux fb sigs all-always
          rec        = buildAllRaw-roundtrip nothing fb nothing sigs all-ok
       in trans (cong (λ m → buildAllRaw fb m
                              (map (expectedRawOfDBC nothing fb) sigs))
                       fmn-eq)
                rec
    go (mc-mux masterName master-eq masterSig mem name-eq pres-eq coh-list)
      rewrite master-eq =
      let fmn-result = findMuxName-finds-master fb sigs masterName masterSig
                         mem pres-eq name-eq
          id         = Data.Product.proj₁ fmn-result
          id-name-eq = Data.Product.proj₁ (Data.Product.proj₂ fmn-result)
          fmn-eq     = Data.Product.proj₂ (Data.Product.proj₂ fmn-result)
          all-ok     = all-sigOK-mc-mux fb sigs id masterName id-name-eq
                         pvs wfps coh-list
          rec        = buildAllRaw-roundtrip (just masterName) fb (just id)
                                              sigs all-ok
       in trans (cong (λ m → buildAllRaw fb m
                              (map (expectedRawOfDBC (just masterName) fb)
                                   sigs))
                       fmn-eq)
                rec
      where import Data.Product
