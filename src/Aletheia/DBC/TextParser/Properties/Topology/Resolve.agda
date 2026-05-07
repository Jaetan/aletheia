{-# OPTIONS --safe --without-K #-}

-- B.3.d Layer 3 3d.7 — `resolveSignalList`-roundtrip.
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
-- 3d.8 will combine this with `parseSignalLines-roundtrip` (3d.6) and a
-- BO_-header `messageHeaderFmt` to close `parseMessage-roundtrip`.
module Aletheia.DBC.TextParser.Properties.Topology.Resolve where

open import Data.Bool using (Bool; true; false; T)
open import Data.Bool.Properties using (T-irrelevant)
open import Data.Char using (Char) renaming (_≟_ to _≟ᶜ_)
import Data.List.Properties as ListProps
open import Data.List using (List; []; _∷_; map; length)
  renaming (_++_ to _++ₗ_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.NonEmpty as List⁺ using (List⁺; _∷_)
open import Data.List.Relation.Unary.All as All using (All)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; _+_; _∸_; _*_; s≤s; z≤n; _%_)
open import Data.Nat.DivMod using (m<n⇒m%n≡m)
open import Data.Nat.Properties using (≤-trans; <⇒≤; +-comm)
open import Data.Product using (_×_; _,_; Σ; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import Aletheia.DBC.Identifier using (Identifier; mkIdent; validIdentifierᵇ)
open import Aletheia.DBC.CanonicalReceivers using (CanonicalReceivers)
open import Aletheia.DBC.Types using
  (DBCSignal; SignalPresence; Always; When; clearVds)

open import Aletheia.CAN.Endianness using
  (ByteOrder; LittleEndian; BigEndian;
   convertStartBit; unconvertStartBit)
open import Aletheia.CAN.Endianness.Properties.StartBit using
  (unconvertStartBit-roundtrip)
open import Aletheia.CAN.Signal using (SignalDef)
open import Aletheia.CAN.Constants using
  (max-physical-bits)

open import Aletheia.DBC.Formatter.WellFormed using
  (WellFormedSignal; WellFormedSignalDef;
   PhysicallyValid; pv-LE; pv-BE;
   unconvertSB-bound; unconvertSB-bound-BE)
open import Aletheia.DBC.Formatter.WellFormedText using
  (WellFormedTextPresence; wftp-always; wftp-when-single;
   WellFormedTextSignal; MasterCoherent; mc-no-mux; mc-mux)
open import Aletheia.DBC.TextFormatter.Topology using
  (findMuxMaster)

open import Aletheia.DBC.TextParser.Topology.Foundations using
  (RawSignal; mkRawSignal;
   MuxMarker; NotMux; IsMux; SelBy; BothMux)
open import Aletheia.DBC.TextParser.Topology using
  (findMuxName; resolvePresence; buildSignal; buildAllRaw;
   resolveSignalList)
open import Aletheia.DBC.TextParser.Properties.Topology.Signal using
  (expectedRaw)
open import Aletheia.DBC.TextParser.Properties.Topology.SignalList using
  (expectedMux; expectedMuxFor; expectedRawOfDBC)


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
-- BITLENGTH / STARTBIT MOD IDENTITIES
-- ============================================================================

-- `bitLength % (1 + max-physical-bits) ≡ bitLength` under the
-- `bitLength < suc max-physical-bits` bound from `WellFormedSignalDef`.
bitLength-mod-id : ∀ (sd : SignalDef)
  → WellFormedSignalDef sd
  → SignalDef.bitLength sd % (1 + max-physical-bits) ≡ SignalDef.bitLength sd
bitLength-mod-id sd wf-sd =
  m<n⇒m%n≡m (WellFormedSignalDef.bitLength-bound wf-sd)

-- `unconvertStartBit fb bo s l < max-physical-bits` (the bound used to
-- collapse `% max-physical-bits` to identity).  Dispatches on byteOrder:
-- LE returns `s` directly (bound from `WellFormedSignalDef.startBit-bound`);
-- BE goes through `unconvertSB-bound-BE` (needs `fb ≤ 64`).
unconvertSB-bounded :
    ∀ (sig : DBCSignal) (fb : ℕ)
  → fb ≤ 64
  → WellFormedSignalDef (DBCSignal.signalDef sig)
  → unconvertStartBit fb (DBCSignal.byteOrder sig)
                         (SignalDef.startBit (DBCSignal.signalDef sig))
                         (SignalDef.bitLength (DBCSignal.signalDef sig))
    < max-physical-bits
unconvertSB-bounded sig fb fb≤64 wf-sd with DBCSignal.byteOrder sig
... | LittleEndian =
  unconvertSB-bound fb (SignalDef.startBit (DBCSignal.signalDef sig))
                       (SignalDef.bitLength (DBCSignal.signalDef sig))
                       fb≤64 (WellFormedSignalDef.startBit-bound wf-sd)
... | BigEndian =
  unconvertSB-bound-BE fb (SignalDef.startBit (DBCSignal.signalDef sig))
                          (SignalDef.bitLength (DBCSignal.signalDef sig))
                          fb≤64

-- `unconvertStartBit … % max-physical-bits ≡ unconvertStartBit …`.
unconvertSB-mod-id :
    ∀ (sig : DBCSignal) (fb : ℕ)
  → fb ≤ 64
  → WellFormedSignalDef (DBCSignal.signalDef sig)
  → unconvertStartBit fb (DBCSignal.byteOrder sig)
                         (SignalDef.startBit (DBCSignal.signalDef sig))
                         (SignalDef.bitLength (DBCSignal.signalDef sig))
    % max-physical-bits
    ≡ unconvertStartBit fb (DBCSignal.byteOrder sig)
                            (SignalDef.startBit (DBCSignal.signalDef sig))
                            (SignalDef.bitLength (DBCSignal.signalDef sig))
unconvertSB-mod-id sig fb fb≤64 wf-sd =
  m<n⇒m%n≡m (unconvertSB-bounded sig fb fb≤64 wf-sd)


-- ============================================================================
-- CONVERT ∘ UNCONVERT ≡ id
-- ============================================================================

-- Closing the start-bit roundtrip: `convertStartBit fb bo (unconvertStartBit
-- fb bo s l) l ≡ s` under WF.  LE: both functions are identity on `s`.  BE:
-- delegates to `unconvertStartBit-roundtrip` from `Endianness/Properties/
-- StartBit`, with the three pv-BE constraints.
convert-unconvert-id :
    ∀ (sig : DBCSignal) (fb : ℕ)
  → PhysicallyValid fb sig
  → convertStartBit fb (DBCSignal.byteOrder sig)
      (unconvertStartBit fb (DBCSignal.byteOrder sig)
        (SignalDef.startBit (DBCSignal.signalDef sig))
        (SignalDef.bitLength (DBCSignal.signalDef sig)))
      (SignalDef.bitLength (DBCSignal.signalDef sig))
    ≡ SignalDef.startBit (DBCSignal.signalDef sig)
convert-unconvert-id sig fb (pv-LE bo-eq) rewrite bo-eq = refl
convert-unconvert-id sig fb (pv-BE bo-eq len-pos fits msb-ge-len)
  rewrite bo-eq =
  unconvertStartBit-roundtrip fb _ _ len-pos fits msb-ge-len


-- ============================================================================
-- SIGNAL DEF RECOVERY — start bit + bit length both round-trip
-- ============================================================================

-- Combined startBit roundtrip including the `% max-physical-bits` /
-- `% (1 + max-physical-bits)` collapse: the buildSignal output's
-- startBit equals the original sig's startBit.
startBit-recovers : ∀ (sig : DBCSignal) (fb : ℕ)
  → fb ≤ 64
  → WellFormedSignalDef (DBCSignal.signalDef sig)
  → PhysicallyValid fb sig
  → convertStartBit fb (DBCSignal.byteOrder sig)
      (unconvertStartBit fb (DBCSignal.byteOrder sig)
        (SignalDef.startBit (DBCSignal.signalDef sig))
        (SignalDef.bitLength (DBCSignal.signalDef sig))
       % max-physical-bits)
      (SignalDef.bitLength (DBCSignal.signalDef sig)
       % (1 + max-physical-bits))
    ≡ SignalDef.startBit (DBCSignal.signalDef sig)
startBit-recovers sig fb fb≤64 wf-sd pv
  rewrite unconvertSB-mod-id sig fb fb≤64 wf-sd
        | bitLength-mod-id (DBCSignal.signalDef sig) wf-sd =
  convert-unconvert-id sig fb pv


-- ============================================================================
-- BUILDSIGNAL OUTPUT RECORD ≡ sig — the unifying field-recovery lemma
-- ============================================================================

-- Given that resolvePresence delivers a presence equal to `sig.presence`,
-- the buildSignal output's record equals `clearVds sig` (E.9a:
-- buildSignal hardcodes `valueDescriptions = []`, so the recovered
-- record matches `sig` modulo the cleared VAL_ field).  The Universal at
-- the top-level layer threads `attachValueDescs ∘ collectFromMessages ≡
-- id` on the cleared form (Refine bridge) post-buildSignal.  Composes
-- startBit-recovers + bitLength-mod-id.
buildSignal-fields-recover :
    ∀ (sig : DBCSignal) (fb : ℕ) (presence-result : SignalPresence)
  → fb ≤ 64
  → WellFormedSignal sig
  → PhysicallyValid fb sig
  → presence-result ≡ DBCSignal.presence sig
  → record
      { name      = DBCSignal.name sig
      ; signalDef = record
          { startBit  = convertStartBit fb (DBCSignal.byteOrder sig)
                          (unconvertStartBit fb (DBCSignal.byteOrder sig)
                             (SignalDef.startBit (DBCSignal.signalDef sig))
                             (SignalDef.bitLength (DBCSignal.signalDef sig))
                           % max-physical-bits)
                          (SignalDef.bitLength (DBCSignal.signalDef sig)
                           % (1 + max-physical-bits))
          ; bitLength = SignalDef.bitLength (DBCSignal.signalDef sig)
                        % (1 + max-physical-bits)
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
      }
    ≡ clearVds sig
buildSignal-fields-recover sig fb presence-result fb≤64 wf-sig pv presence-eq
  rewrite startBit-recovers sig fb fb≤64
            (WellFormedSignal.def-wf wf-sig) pv
        | bitLength-mod-id (DBCSignal.signalDef sig)
            (WellFormedSignal.def-wf wf-sig)
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
-- E.9a: result is `just (clearVds sig)` (buildSignal hardcodes vds = []);
-- the Universal threads `attachValueDescs ∘ collectFromMessages ≡ id`
-- post-buildSignal to recover the original.
buildSignal-roundtrip-Always :
    ∀ (master : Maybe (List Char)) (fb : ℕ) (sig : DBCSignal)
      (m : Maybe Identifier)
  → DBCSignal.presence sig ≡ Always
  → fb ≤ 64
  → WellFormedSignal sig
  → PhysicallyValid fb sig
  → buildSignal fb m (expectedRawOfDBC master fb sig) ≡ just (clearVds sig)
buildSignal-roundtrip-Always master fb sig m presence-eq fb≤64 wf-sig pv
  rewrite presence-eq with master
... | nothing =
  cong just (buildSignal-fields-recover sig fb Always fb≤64 wf-sig pv
                                        (sym presence-eq))
... | just mName with ⌊ ListProps.≡-dec _≟ᶜ_
                       (Identifier.name (DBCSignal.name sig)) mName ⌋
...   | true =
  cong just (buildSignal-fields-recover sig fb Always fb≤64 wf-sig pv
                                        (sym presence-eq))
...   | false =
  cong just (buildSignal-fields-recover sig fb Always fb≤64 wf-sig pv
                                        (sym presence-eq))

-- When case (singleton via WellFormedTextPresence): buildSignal succeeds
-- ONLY when `m = just <Identifier with name = sig-master's name>` —
-- otherwise resolvePresence fails (m=nothing) or builds the wrong
-- presence (wrong identifier).  Take m = just sig-master directly via
-- the `m-eq` hypothesis (3d.7 caller derives this from MasterCoherent
-- + findMuxName-result).
buildSignal-roundtrip-When :
    ∀ (master : Maybe (List Char)) (fb : ℕ) (sig : DBCSignal)
      (m sig-master : Identifier) (v : ℕ)
  → DBCSignal.presence sig ≡ When sig-master (v ∷ [])
  → m ≡ sig-master
  → fb ≤ 64
  → WellFormedSignal sig
  → PhysicallyValid fb sig
  → buildSignal fb (just m) (expectedRawOfDBC master fb sig) ≡ just (clearVds sig)
buildSignal-roundtrip-When master fb sig m sig-master v presence-eq m-eq
                           fb≤64 wf-sig pv
  rewrite presence-eq | m-eq =
  cong just (buildSignal-fields-recover sig fb (When sig-master (v ∷ []))
                                        fb≤64 wf-sig pv (sym presence-eq))


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
               → WellFormedSignal sig
               → PhysicallyValid fb sig
               → SigOK m fb sig
  sigok-when   : ∀ {sig sig-master v}
               → DBCSignal.presence sig ≡ When sig-master (v ∷ [])
               → m ≡ just sig-master
               → WellFormedSignal sig
               → PhysicallyValid fb sig
               → SigOK m fb sig


-- ============================================================================
-- buildAll-roundtrip — list-level induction
-- ============================================================================

-- Inducts on `All (SigOK m fb) sigs`.  Each step calls buildSignal-
-- roundtrip (Always or When branch per the SigOK constructor) and
-- recurses on the tail.
--
-- E.9a: result is `just (map clearVds sigs)` (not `just sigs`); the
-- per-message buildMessage-roundtrip then bridges via E.6's
-- attachValueDescs-on-collected at the Universal layer.
buildAllRaw-roundtrip :
    ∀ (master : Maybe (List Char)) (fb : ℕ) (m : Maybe Identifier)
      (sigs : List DBCSignal)
  → fb ≤ 64
  → All (SigOK m fb) sigs
  → buildAllRaw fb m (map (expectedRawOfDBC master fb) sigs)
    ≡ just (map clearVds sigs)
buildAllRaw-roundtrip _ _ _ [] _ All.[] = refl
buildAllRaw-roundtrip master fb m (sig ∷ rest)
                      fb≤64 (sigok All.∷ rest-wfs) =
  go sigok
  where
    rec : buildAllRaw fb m (map (expectedRawOfDBC master fb) rest)
        ≡ just (map clearVds rest)
    rec = buildAllRaw-roundtrip master fb m rest fb≤64 rest-wfs

    go : SigOK m fb sig
       → buildAllRaw fb m (map (expectedRawOfDBC master fb) (sig ∷ rest))
         ≡ just (clearVds sig ∷ map clearVds rest)
    go (sigok-always pres-eq wf-sig pv)
      rewrite buildSignal-roundtrip-Always master fb sig m pres-eq
                                            fb≤64 wf-sig pv
            | rec = refl
    go (sigok-when {sig-master = sig-master} {v = v}
                   pres-eq refl wf-sig pv)
      rewrite buildSignal-roundtrip-When master fb sig sig-master
                                          sig-master v pres-eq refl
                                          fb≤64 wf-sig pv
            | rec = refl


-- ============================================================================
-- DERIVING `All (SigOK m fb) sigs` from MasterCoherent + per-signal WF
-- ============================================================================

-- mc-no-mux case: every sig is `Always` (via findMuxMaster-nothing→all-
-- Always); each `SigOK` is sigok-always; m can be anything.
all-sigOK-no-mux :
    ∀ (fb : ℕ) (m : Maybe Identifier) (sigs : List DBCSignal)
  → All WellFormedSignal sigs
  → All (PhysicallyValid fb) sigs
  → All (λ s → DBCSignal.presence s ≡ Always) sigs
  → All (SigOK m fb) sigs
all-sigOK-no-mux _  _ [] _ _ _ = All.[]
all-sigOK-no-mux fb m (sig ∷ rest)
                 (wf-sig All.∷ rest-wfs)
                 (pv All.∷ rest-pvs)
                 (pres-eq All.∷ rest-pres-eqs) =
  sigok-always pres-eq wf-sig pv All.∷
    all-sigOK-no-mux fb m rest rest-wfs rest-pvs rest-pres-eqs

-- mc-mux case: each sig's SigOK comes from per-signal WFTP — Always
-- gives sigok-always (m-irrelevant); When gives sigok-when with the
-- m ≡ just sig-master witness derived from MasterCoherent's coh-list +
-- name equality + ident-eq-from-name.
all-sigOK-mc-mux :
    ∀ (fb : ℕ) (sigs : List DBCSignal) (id : Identifier)
      (masterName : List Char)
  → Identifier.name id ≡ masterName
  → All WellFormedSignal sigs
  → All (PhysicallyValid fb) sigs
  → All (λ s → WellFormedTextPresence (DBCSignal.presence s)) sigs
  → All (λ s → (m : Identifier) (vs : List⁺ ℕ)
             → DBCSignal.presence s ≡ When m vs
             → Identifier.name m ≡ masterName)
        sigs
  → All (SigOK (just id) fb) sigs
all-sigOK-mc-mux _ [] _ _ _ _ _ _ _ = All.[]
all-sigOK-mc-mux fb (sig ∷ rest) id masterName id-name-eq
                 (wf-sig All.∷ rest-wfs)
                 (pv All.∷ rest-pvs)
                 (wfp All.∷ rest-wfps)
                 (coh All.∷ rest-cohs) =
  sigOK-from-wfp fb sig id masterName id-name-eq wf-sig pv wfp coh
    All.∷
    all-sigOK-mc-mux fb rest id masterName id-name-eq
                     rest-wfs rest-pvs rest-wfps rest-cohs
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
      → WellFormedSignal sig
      → PhysicallyValid fb sig
      → WellFormedTextPresence (DBCSignal.presence sig)
      → ((m : Identifier) (vs : List⁺ ℕ)
           → DBCSignal.presence sig ≡ When m vs
           → Identifier.name m ≡ masterName)
      → SigOK (just id) fb sig
    sigOK-from-wfp fb sig id masterName id-name-eq wf-sig pv wfp coh =
      helper (DBCSignal.presence sig) refl wfp
      where
        helper : ∀ (p : SignalPresence)
               → DBCSignal.presence sig ≡ p
               → WellFormedTextPresence p
               → SigOK (just id) fb sig
        helper Always              p-eq wftp-always       =
          sigok-always p-eq wf-sig pv
        helper (When sm (v ∷ [])) p-eq wftp-when-single =
          sigok-when p-eq (cong just id-eq-sm) wf-sig pv
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
-- E.9a: result is `just (map clearVds sigs)` (not `just sigs`); the
-- per-message and Universal layers thread `attachValueDescs` to bridge
-- the cleared form back to the original.
resolveSignalList-roundtrip :
    ∀ (fb : ℕ) (sigs : List DBCSignal)
  → fb ≤ 64
  → All WellFormedSignal sigs
  → All (PhysicallyValid fb) sigs
  → All (λ s → WellFormedTextPresence (DBCSignal.presence s)) sigs
  → MasterCoherent sigs
  → resolveSignalList fb
       (map (expectedRawOfDBC (findMuxMaster sigs) fb) sigs)
    ≡ just (map clearVds sigs)
resolveSignalList-roundtrip fb sigs fb≤64 wf-sigs pvs wfps mc =
  go mc
  where
    -- Inside `resolveSignalList`, the call is `buildAllRaw fb (findMuxName
    -- raws) raws` where `raws = map (expectedRawOfDBC master fb) sigs`.
    -- We first compute `findMuxName raws`, then apply `buildAllRaw-
    -- roundtrip` with the appropriate SigOK list.
    go : MasterCoherent sigs
       → resolveSignalList fb
            (map (expectedRawOfDBC (findMuxMaster sigs) fb) sigs)
         ≡ just (map clearVds sigs)
    go (mc-no-mux nothing-eq)
      rewrite nothing-eq =
      let all-always = findMuxMaster-nothing→all-Always sigs nothing-eq
          all-ok     = all-sigOK-no-mux fb nothing sigs wf-sigs pvs all-always
          fmn-eq     = findMuxName-on-no-mux fb sigs all-always
          rec        = buildAllRaw-roundtrip nothing fb nothing sigs
                                              fb≤64 all-ok
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
                         wf-sigs pvs wfps coh-list
          rec        = buildAllRaw-roundtrip (just masterName) fb (just id)
                                              sigs fb≤64 all-ok
       in trans (cong (λ m → buildAllRaw fb m
                              (map (expectedRawOfDBC (just masterName) fb)
                                   sigs))
                       fmn-eq)
                rec
      where import Data.Product
