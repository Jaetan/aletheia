{-# OPTIONS --safe --without-K #-}

-- Capstone theorem and representability.
--
-- Purpose: Bridge from ValidDBC to batch roundtrip correctness.
--   ValidDBC provides AllPairsDisjoint and AllSignalsFit; Representable
--   provides AllRoundtrip; composing these yields the capstone:
--   validDBC-roundtrip.
-- Key results: validDBC-roundtrip, representable?, allRepresentable→allRoundtrip.
module Aletheia.CAN.Batch.Properties.Capstone where

open import Aletheia.CAN.Batch.Properties.Roundtrip using (
  DisjointFromAll; dfa-nil; dfa-cons;
  AllPairsDisjoint; apd-nil; apd-cons;
  AllSignalsFit; asf-nil; asf-cons;
  signalFits;
  InjectRoundtrips;
  AllRoundtrip; ar-nil; ar-cons;
  injectAll-preserves-disjoint; injectAll-roundtrip;
  roundtrip-unsigned→IR; roundtrip-signed→IR)

open import Aletheia.CAN.Frame using (CANFrame)
open import Aletheia.CAN.Signal using (SignalDef)
open import Aletheia.CAN.Encoding using (extractSignal; injectSignal)
open import Aletheia.CAN.Encoding.Properties using (
  signalValue;
  SignedFits;
  removeScaling-applyScaling-exact; removeScaling-nothing⇒zero)
open import Aletheia.CAN.Encoding.Arithmetic using (inBounds; removeScaling)
open import Aletheia.CAN.BatchFrameBuilding using (injectAll)
open import Aletheia.CAN.DLC using (dlcBytes)
open import Aletheia.DBC.Types using (DBC; DBCMessage; DBCSignal; SignalPresence; Always; When)
open import Aletheia.DBC.Properties using (
  PhysicallyDisjoint;
  SignalPairValid; signalPairValid-sym;
  extractDisjointness; CanCoexist; both-always;
  _≟-DBCSignal_)
open import Aletheia.DBC.Validity using (ValidDBC; nonZeroFactor→factor≢0; BitsInFrame)

open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat using (ℕ; _+_; _*_; _<_; _≤_; _^_; _>_; _∸_; suc; _<?_; _≤?_)
open import Data.Rational using (ℚ; 0ℚ) renaming (_≟_ to _≟ᵣ_)
open import Data.Integer using (ℤ; +_; -[1+_])
open import Data.Bool using (true; false)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe.Properties using (just-injective)
import Data.List.Relation.Unary.All as StdAll
import Data.List.Relation.Unary.AllPairs as StdAP
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; subst; cong; trans)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Function using (case_of_)

-- ============================================================================
-- PREDICATES FOR CAPSTONE PRECONDITIONS
-- ============================================================================

-- All signals in the list are always-present (not multiplexed)
data AllAlwaysPresent : List (DBCSignal × ℚ) → Set where
  aap-nil  : AllAlwaysPresent []
  aap-cons : ∀ {s v rest}
    → DBCSignal.presence s ≡ Always
    → AllAlwaysPresent rest
    → AllAlwaysPresent ((s , v) ∷ rest)

-- All signals come from a specific message
data AllFromMessage : List (DBCSignal × ℚ) → DBCMessage → Set where
  afm-nil  : ∀ {msg} → AllFromMessage [] msg
  afm-cons : ∀ {s v rest msg}
    → s ∈ DBCMessage.signals msg
    → AllFromMessage rest msg
    → AllFromMessage ((s , v) ∷ rest) msg

-- Signals in the list are pairwise distinct (as DBCSignal values)
data DistinctFromAll (s : DBCSignal) : List (DBCSignal × ℚ) → Set where
  dist-nil  : DistinctFromAll s []
  dist-cons : ∀ {s' v rest}
    → s ≢ s'
    → DistinctFromAll s rest
    → DistinctFromAll s ((s' , v) ∷ rest)

data PairsDistinct : List (DBCSignal × ℚ) → Set where
  pd-nil  : PairsDistinct []
  pd-cons : ∀ {s v rest}
    → DistinctFromAll s rest
    → PairsDistinct rest
    → PairsDistinct ((s , v) ∷ rest)

-- ============================================================================
-- DECIDABLE CHECKERS FOR CAPSTONE PRECONDITIONS
-- ============================================================================

private
  isAlways? : (p : SignalPresence) → Dec (p ≡ Always)
  isAlways? Always     = yes refl
  isAlways? (When _ _) = no (λ ())

allAlwaysPresent? : (pairs : List (DBCSignal × ℚ)) → Dec (AllAlwaysPresent pairs)
allAlwaysPresent? [] = yes aap-nil
allAlwaysPresent? ((s , v) ∷ rest) with isAlways? (DBCSignal.presence s)
... | no ¬a = no λ { (aap-cons eq _) → ¬a eq }
... | yes a with allAlwaysPresent? rest
...   | no ¬ar = no λ { (aap-cons _ ar) → ¬ar ar }
...   | yes ar = yes (aap-cons a ar)

open import Data.List.Membership.DecPropositional {A = DBCSignal} _≟-DBCSignal_ using (_∈?_)

allFromMessage? : (pairs : List (DBCSignal × ℚ)) → (msg : DBCMessage)
                → Dec (AllFromMessage pairs msg)
allFromMessage? [] msg = yes afm-nil
allFromMessage? ((s , v) ∷ rest) msg with s ∈? DBCMessage.signals msg
... | no ¬s∈ = no λ { (afm-cons s∈ _) → ¬s∈ s∈ }
... | yes s∈ with allFromMessage? rest msg
...   | no ¬ar = no λ { (afm-cons _ ar) → ¬ar ar }
...   | yes ar = yes (afm-cons s∈ ar)

private
  distinctFromAll? : (s : DBCSignal) → (rest : List (DBCSignal × ℚ))
                   → Dec (DistinctFromAll s rest)
  distinctFromAll? s [] = yes dist-nil
  distinctFromAll? s ((s' , v) ∷ rest) with s ≟-DBCSignal s'
  ... | yes eq = no λ { (dist-cons s≢ _) → s≢ eq }
  ... | no s≢ with distinctFromAll? s rest
  ...   | no ¬dr = no λ { (dist-cons _ dr) → ¬dr dr }
  ...   | yes dr = yes (dist-cons s≢ dr)

pairsDistinct? : (pairs : List (DBCSignal × ℚ)) → Dec (PairsDistinct pairs)
pairsDistinct? [] = yes pd-nil
pairsDistinct? ((s , v) ∷ rest) with distinctFromAll? s rest
... | no ¬da = no λ { (pd-cons da _) → ¬da da }
... | yes da with pairsDistinct? rest
...   | no ¬pr = no λ { (pd-cons _ pr) → ¬pr pr }
...   | yes pr = yes (pd-cons da pr)

-- ============================================================================
-- GAP 1: ValidDBC → AllPairsDisjoint
-- ============================================================================

private
  allPairs-lookup : ∀ {n sig₁ sig₂ sigs}
    → StdAP.AllPairs (SignalPairValid n) sigs
    → sig₁ ∈ sigs → sig₂ ∈ sigs → sig₁ ≢ sig₂
    → SignalPairValid n sig₁ sig₂
  allPairs-lookup (hd StdAP.∷ _) (here refl) (there sig₂∈) _ =
    StdAll.lookup hd sig₂∈
  allPairs-lookup (hd StdAP.∷ _) (there sig₁∈) (here refl) _ =
    signalPairValid-sym (StdAll.lookup hd sig₁∈)
  allPairs-lookup (_ StdAP.∷ rest) (there sig₁∈) (there sig₂∈) sig≢ =
    allPairs-lookup rest sig₁∈ sig₂∈ sig≢
  allPairs-lookup _ (here refl) (here refl) sig≢ = ⊥-elim (sig≢ refl)

  buildDFA : ∀ {n msg} (s : DBCSignal) (rest : List (DBCSignal × ℚ))
    → StdAP.AllPairs (SignalPairValid n) (DBCMessage.signals msg)
    → s ∈ DBCMessage.signals msg
    → DBCSignal.presence s ≡ Always
    → AllFromMessage rest msg
    → AllAlwaysPresent rest
    → DistinctFromAll s rest
    → DisjointFromAll n s rest
  buildDFA _ [] _ _ _ _ _ _ = dfa-nil
  buildDFA s ((s' , _) ∷ rest) ap s∈ refl
      (afm-cons s'∈ afm-rest) (aap-cons refl aap-rest) (dist-cons s≢s' dist-rest) =
    dfa-cons
      (extractDisjointness (allPairs-lookup ap s∈ s'∈ s≢s') both-always)
      (buildDFA s rest ap s∈ refl afm-rest aap-rest dist-rest)

validDBC→allPairsDisjoint : ∀ {dbc msg} (pairs : List (DBCSignal × ℚ))
  → ValidDBC dbc
  → msg ∈ DBC.messages dbc
  → AllAlwaysPresent pairs
  → AllFromMessage pairs msg
  → PairsDistinct pairs
  → AllPairsDisjoint (dlcBytes (DBCMessage.dlc msg)) pairs
validDBC→allPairsDisjoint [] _ _ _ _ _ = apd-nil
validDBC→allPairsDisjoint ((s , v) ∷ rest) vdbc msg∈
    (aap-cons ps aap-rest) (afm-cons s∈ afm-rest) (pd-cons dist pd-rest) =
  apd-cons
    (buildDFA s rest ap s∈ ps afm-rest aap-rest dist)
    (validDBC→allPairsDisjoint rest vdbc msg∈ aap-rest afm-rest pd-rest)
  where
    ap = StdAll.lookup (ValidDBC.sigPairsValid vdbc) msg∈

-- ============================================================================
-- GAP 2: ValidDBC → AllSignalsFit
-- ============================================================================

private
  buildASF : ∀ {msg} (pairs : List (DBCSignal × ℚ))
    → StdAll.All (BitsInFrame (dlcBytes (DBCMessage.dlc msg))) (DBCMessage.signals msg)
    → AllFromMessage pairs msg
    → AllSignalsFit (dlcBytes (DBCMessage.dlc msg)) pairs
  buildASF [] _ _ = asf-nil
  buildASF ((s , _) ∷ rest) bifs (afm-cons s∈ afm-rest) =
    asf-cons
      (StdAll.lookup bifs s∈)
      (buildASF rest bifs afm-rest)

validDBC→allSignalsFit : ∀ {dbc msg} (pairs : List (DBCSignal × ℚ))
  → ValidDBC dbc
  → msg ∈ DBC.messages dbc
  → AllFromMessage pairs msg
  → AllSignalsFit (dlcBytes (DBCMessage.dlc msg)) pairs
validDBC→allSignalsFit pairs vdbc msg∈ afm =
  buildASF pairs
    (StdAll.lookup (ValidDBC.bitsInFrame vdbc) msg∈)
    afm

-- ============================================================================
-- CAPSTONE THEOREM
-- ============================================================================

validDBC-roundtrip :
  ∀ {dbc msg} (pairs : List (DBCSignal × ℚ))
    (frame frame' : CANFrame (dlcBytes (DBCMessage.dlc msg)))
  → ValidDBC dbc
  → msg ∈ DBC.messages dbc
  → AllAlwaysPresent pairs
  → AllFromMessage pairs msg
  → PairsDistinct pairs
  → AllRoundtrip (dlcBytes (DBCMessage.dlc msg)) pairs
  → injectAll frame pairs ≡ inj₂ frame'
  → ∀ {s v} → (s , v) ∈ pairs
  → extractSignal frame' (DBCSignal.signalDef s) (DBCSignal.byteOrder s) ≡ just v
validDBC-roundtrip pairs frame frame' vdbc msg∈ aap afm pd ar eq mem =
  injectAll-roundtrip pairs frame frame'
    (validDBC→allPairsDisjoint pairs vdbc msg∈ aap afm pd)
    (validDBC→allSignalsFit pairs vdbc msg∈ afm)
    ar eq mem

-- ============================================================================
-- REPRESENTABLE: decidable value representability for capstone theorem
-- ============================================================================

data Representable (sig : DBCSignal) (v : ℚ) : Set where
  repr-unsigned : (n : ℕ)
    → v ≡ signalValue (+ n) (DBCSignal.signalDef sig)
    → inBounds v (SignalDef.minimum (DBCSignal.signalDef sig))
                  (SignalDef.maximum (DBCSignal.signalDef sig)) ≡ true
    → SignalDef.isSigned (DBCSignal.signalDef sig) ≡ false
    → n < 2 ^ SignalDef.bitLength (DBCSignal.signalDef sig)
    → Representable sig v
  repr-signed : (z : ℤ)
    → v ≡ signalValue z (DBCSignal.signalDef sig)
    → inBounds v (SignalDef.minimum (DBCSignal.signalDef sig))
                  (SignalDef.maximum (DBCSignal.signalDef sig)) ≡ true
    → SignalDef.isSigned (DBCSignal.signalDef sig) ≡ true
    → SignalDef.bitLength (DBCSignal.signalDef sig) > 0
    → SignedFits z (SignalDef.bitLength (DBCSignal.signalDef sig))
    → Representable sig v

representable? : (sig : DBCSignal) (v : ℚ)
  → SignalDef.factor (DBCSignal.signalDef sig) ≢ 0ℚ
  → Dec (Representable sig v)
representable? sig v factor≢0 = go (removeScaling v factor offset) refl
  where
    sd = DBCSignal.signalDef sig
    open SignalDef sd

    +-inj : ∀ {m n : ℕ} → (+ m) ≡ (+ n) → m ≡ n
    +-inj refl = refl

    raw≡z : ∀ {raw z} → removeScaling v factor offset ≡ just z
          → v ≡ signalValue raw sd → raw ≡ z
    raw≡z {raw} remEq v≡ = just-injective
      (trans (sym (removeScaling-applyScaling-exact raw factor offset factor≢0))
             (trans (cong (λ x → removeScaling x factor offset) (sym v≡)) remEq))

    goSF : ∀ z → removeScaling v factor offset ≡ just z → signalValue z sd ≡ v
         → inBounds v minimum maximum ≡ true → isSigned ≡ true
         → bitLength > 0 → Dec (Representable sig v)
    goSF (+ n) remEq sv≡v bEq isEq bl>0 with n <? 2 ^ (bitLength ∸ 1)
    ... | yes n< = yes (repr-signed (+ n) (sym sv≡v) bEq isEq bl>0 n<)
    ... | no ¬n< = no λ where
          (repr-unsigned _ _ _ u _) → case trans (sym isEq) u of λ ()
          (repr-signed z' v≡ _ _ _ sf) →
            ¬n< (subst (λ r → SignedFits r bitLength) (raw≡z {z'} remEq v≡) sf)
    goSF -[1+ n ] remEq sv≡v bEq isEq bl>0 with suc n ≤? 2 ^ (bitLength ∸ 1)
    ... | yes sn≤ = yes (repr-signed -[1+ n ] (sym sv≡v) bEq isEq bl>0 sn≤)
    ... | no ¬sn≤ = no λ where
          (repr-unsigned _ _ _ u _) → case trans (sym isEq) u of λ ()
          (repr-signed z' v≡ _ _ _ sf) →
            ¬sn≤ (subst (λ r → SignedFits r bitLength) (raw≡z {z'} remEq v≡) sf)

    goIS : ∀ b → isSigned ≡ b → ∀ z → removeScaling v factor offset ≡ just z
         → signalValue z sd ≡ v → inBounds v minimum maximum ≡ true
         → Dec (Representable sig v)
    goIS false isEq (+ n) remEq sv≡v bEq with n <? 2 ^ bitLength
    ... | yes n< = yes (repr-unsigned n (sym sv≡v) bEq isEq n<)
    ... | no ¬n< = no λ where
          (repr-unsigned n' v≡ _ _ n'<) →
            ¬n< (subst (_< 2 ^ bitLength) (+-inj (raw≡z {+ n'} remEq v≡)) n'<)
          (repr-signed _ _ _ s _ _) → case trans (sym isEq) s of λ ()
    goIS false isEq -[1+ _ ] remEq _ _ = no λ where
        (repr-unsigned n v≡ _ _ _) → case raw≡z {+ n} remEq v≡ of λ ()
        (repr-signed _ _ _ s _ _) → case trans (sym isEq) s of λ ()
    goIS true isEq z remEq sv≡v bEq with 0 <? bitLength
    ... | no ¬bl>0 = no λ where
          (repr-unsigned _ _ _ u _) → case trans (sym isEq) u of λ ()
          (repr-signed _ _ _ _ bl>0 _) → ¬bl>0 bl>0
    ... | yes bl>0 = goSF z remEq sv≡v bEq isEq bl>0

    go : (r : Maybe ℤ) → removeScaling v factor offset ≡ r → Dec (Representable sig v)
    go nothing remEq = ⊥-elim (factor≢0 (removeScaling-nothing⇒zero v factor offset remEq))
    go (just z) remEq with signalValue z sd ≟ᵣ v
    ... | no sv≢v = no λ where
          (repr-unsigned n v≡ _ _ _) →
            sv≢v (subst (λ r → signalValue r sd ≡ v) (raw≡z {+ n} remEq v≡) (sym v≡))
          (repr-signed z' v≡ _ _ _ _) →
            sv≢v (subst (λ r → signalValue r sd ≡ v) (raw≡z {z'} remEq v≡) (sym v≡))
    ... | yes sv≡v with inBounds v minimum maximum in bEq
    ...   | false = no λ where
            (repr-unsigned _ _ b _ _) → case trans (sym bEq) b of λ ()
            (repr-signed _ _ b _ _ _) → case trans (sym bEq) b of λ ()
    ...   | true = goIS isSigned refl z remEq sv≡v bEq

-- Bridge: Representable → InjectRoundtrips
representable→roundtrips : ∀ {m sig v}
  → Representable sig v
  → SignalDef.factor (DBCSignal.signalDef sig) ≢ 0ℚ
  → signalFits m (DBCSignal.signalDef sig)
  → InjectRoundtrips m sig v
representable→roundtrips {_} {sig} (repr-unsigned n v≡ bounds-ok unsigned n<) factor≢0 fits =
  subst (InjectRoundtrips _ sig) (sym v≡)
    (roundtrip-unsigned→IR n sig
      (subst (λ x → inBounds x (SignalDef.minimum sd) (SignalDef.maximum sd) ≡ true) v≡ bounds-ok)
      factor≢0 unsigned fits n<)
  where sd = DBCSignal.signalDef sig
representable→roundtrips {_} {sig} (repr-signed z v≡ bounds-ok signed bl>0 sf) factor≢0 fits =
  subst (InjectRoundtrips _ sig) (sym v≡)
    (roundtrip-signed→IR z sig
      (subst (λ x → inBounds x (SignalDef.minimum sd) (SignalDef.maximum sd) ≡ true) v≡ bounds-ok)
      factor≢0 signed bl>0 sf fits)
  where sd = DBCSignal.signalDef sig

-- All signals in a list are representable
data AllRepresentable : List (DBCSignal × ℚ) → Set where
  arep-nil  : AllRepresentable []
  arep-cons : ∀ {s v rest}
    → Representable s v → AllRepresentable rest
    → AllRepresentable ((s , v) ∷ rest)

allRepresentable? : (pairs : List (DBCSignal × ℚ))
  → StdAll.All (λ { (s , _) → SignalDef.factor (DBCSignal.signalDef s) ≢ 0ℚ }) pairs
  → Dec (AllRepresentable pairs)
allRepresentable? [] _ = yes arep-nil
allRepresentable? ((s , v) ∷ rest) (f≢0 StdAll.∷ fs) with representable? s v f≢0
... | no ¬r = no λ { (arep-cons r _) → ¬r r }
... | yes r with allRepresentable? rest fs
...   | no ¬ar = no λ { (arep-cons _ ar) → ¬ar ar }
...   | yes ar = yes (arep-cons r ar)

-- Bridge: AllRepresentable → AllRoundtrip (given ValidDBC context)
allRepresentable→allRoundtrip : ∀ {dbc msg} (pairs : List (DBCSignal × ℚ))
  → ValidDBC dbc
  → msg ∈ DBC.messages dbc
  → AllFromMessage pairs msg
  → AllRepresentable pairs
  → AllRoundtrip (dlcBytes (DBCMessage.dlc msg)) pairs
allRepresentable→allRoundtrip [] _ _ _ _ = ar-nil
allRepresentable→allRoundtrip ((s , v) ∷ rest) vdbc msg∈
    (afm-cons s∈ afm-rest) (arep-cons rep arep-rest) =
  ar-cons
    (representable→roundtrips rep
      (nonZeroFactor→factor≢0 {s} (StdAll.lookup nzfs s∈))
      (StdAll.lookup bifs s∈))
    (allRepresentable→allRoundtrip rest vdbc msg∈ afm-rest arep-rest)
  where
    nzfs = StdAll.lookup (ValidDBC.nonZeroFactors vdbc) msg∈
    bifs = StdAll.lookup (ValidDBC.bitsInFrame vdbc) msg∈
