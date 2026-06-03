-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- E.8 / E.9a — `unresolvedRVDs ∘ collectFromMessages ≡ []` inverse-bridge,
-- on the raw and the cleared (`map clearVdsMsg`) forms.
--
-- Extracted from `Properties/Aggregator/Refine/ValueDescriptions.agda`
-- (R22 continuation of R21 cluster 9 AGDA-D-15.1) — the parent was 976
-- LOC; lifting E.8 (lines 697-899, ~203 LOC) + E.9a (lines 900-976, ~77
-- LOC) brings it under the 800-LOC trigger.
--
-- Dependency direction: this module imports `⌊≟-CANId⌋-refl` /
-- `⌊≟ᴵ⌋-refl` etc. from the parent.  The parent does NOT import back —
-- the external consumer (`Aggregator/Universal.agda`) imports the
-- final theorem `unresolvedRVDs-on-clearVdsMsgs-collectFromMessages`
-- directly from THIS module (one-way `Universal → UnresolvedRVDs →
-- ValueDescriptions`).  This avoids the
-- `ValueDescriptions → UnresolvedRVDs → ValueDescriptions` cycle that
-- would result from a `public` re-export at the parent.
module Aletheia.DBC.TextParser.Properties.Aggregator.Refine.ValueDescriptions.UnresolvedRVDs where

open import Data.Bool using (true; false; _∨_; _∧_)
open import Data.Bool.Properties using (∨-zeroʳ)
open import Data.Bool.ListAction using (any)
open import Data.Char using (Char)
open import Data.List using (List; []; _∷_; map) renaming (_++_ to _++ₗ_)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; cong)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import Aletheia.CAN.DBCHelpers using (_≟-CANId_)
open import Aletheia.DBC.Types using (DBCSignal; DBCMessage; clearVds; clearVdsMsg)
open import Aletheia.DBC.TextParser.ValueTables using
  (RawValueDesc; mkRawValueDesc)
open import Aletheia.DBC.TextParser.ValueDescriptions using
  ( collectFromSignals; collectFromMessage; collectFromMessages
  ; matchesSigᵇ; matchesMsgᵇ; resolvesᵇ-msgs; unresolvedRVDs
  )
open import Aletheia.DBC.TextParser.Properties.Aggregator.Refine.ValueDescriptions using
  (⌊≟-CANId⌋-refl; ⌊≟ᴵ⌋-refl)



-- ----------------------------------------------------------------------------
-- 1. resolvesᵇ-msgs cons monotonicity
-- ----------------------------------------------------------------------------

resolvesᵇ-msgs-cons-mono :
    ∀ (rvd : RawValueDesc) (m : DBCMessage) (ms : List DBCMessage)
  → resolvesᵇ-msgs rvd ms ≡ true
  → resolvesᵇ-msgs rvd (m ∷ ms) ≡ true
resolvesᵇ-msgs-cons-mono rvd m ms eq
  rewrite eq
  = ∨-zeroʳ (matchesMsgᵇ rvd m)


-- ----------------------------------------------------------------------------
-- 2. matchesSigᵇ self
-- ----------------------------------------------------------------------------

matchesSigᵇ-self :
    ∀ (rvd : RawValueDesc) (s : DBCSignal)
  → DBCSignal.name s ≡ RawValueDesc.signalName rvd
  → matchesSigᵇ rvd s ≡ true
matchesSigᵇ-self rvd s eq
  rewrite eq
  = ⌊≟ᴵ⌋-refl (RawValueDesc.signalName rvd)


-- ----------------------------------------------------------------------------
-- 3. any matchesSigᵇ from membership
-- ----------------------------------------------------------------------------

any-matchesSigᵇ-from-∈ :
    ∀ (rvd : RawValueDesc) (s : DBCSignal) (sigs : List DBCSignal)
  → s ∈ sigs
  → DBCSignal.name s ≡ RawValueDesc.signalName rvd
  → any (matchesSigᵇ rvd) sigs ≡ true
any-matchesSigᵇ-from-∈ rvd s (s ∷ rest) (here refl) name-eq
  rewrite matchesSigᵇ-self rvd s name-eq
  = refl
any-matchesSigᵇ-from-∈ rvd s (s' ∷ rest) (there s∈rest) name-eq
  rewrite any-matchesSigᵇ-from-∈ rvd s rest s∈rest name-eq
  = ∨-zeroʳ (matchesSigᵇ rvd s')


-- ----------------------------------------------------------------------------
-- 4. matchesMsgᵇ on a freshly-constructed rvd whose source signal is in msg
-- ----------------------------------------------------------------------------

matchesMsgᵇ-mkRawValueDesc :
    ∀ (msg : DBCMessage) (s : DBCSignal) (vds : List (ℕ × List Char))
  → s ∈ DBCMessage.signals msg
  → matchesMsgᵇ (mkRawValueDesc (DBCMessage.id msg) (DBCSignal.name s) vds) msg
    ≡ true
matchesMsgᵇ-mkRawValueDesc msg s vds s∈
  rewrite ⌊≟-CANId⌋-refl (DBCMessage.id msg)
  = any-matchesSigᵇ-from-∈
      (mkRawValueDesc (DBCMessage.id msg) (DBCSignal.name s) vds)
      s
      (DBCMessage.signals msg)
      s∈
      refl


-- ----------------------------------------------------------------------------
-- 5. collectFromSignals matches msgᵇ
-- ----------------------------------------------------------------------------

collectFromSignals-matchesMsgᵇ :
    ∀ (msg : DBCMessage) (sigs : List DBCSignal)
  → All (λ s → s ∈ DBCMessage.signals msg) sigs
  → All (λ rvd → matchesMsgᵇ rvd msg ≡ true)
        (collectFromSignals (DBCMessage.id msg) sigs)
collectFromSignals-matchesMsgᵇ msg [] [] = []
collectFromSignals-matchesMsgᵇ msg (s ∷ ss) (s∈ ∷ ss⊆)
  with DBCSignal.valueDescriptions s
... | []        = collectFromSignals-matchesMsgᵇ msg ss ss⊆
... | (x ∷ vds) = matchesMsgᵇ-mkRawValueDesc msg s (x ∷ vds) s∈
                ∷ collectFromSignals-matchesMsgᵇ msg ss ss⊆


-- ----------------------------------------------------------------------------
-- 6. matchesMsgᵇ cons-here lift to resolvesᵇ-msgs
-- ----------------------------------------------------------------------------

matchesMsgᵇ-cons-here :
    ∀ (rvd : RawValueDesc) (m : DBCMessage) (ms : List DBCMessage)
  → matchesMsgᵇ rvd m ≡ true
  → resolvesᵇ-msgs rvd (m ∷ ms) ≡ true
matchesMsgᵇ-cons-here rvd m ms eq rewrite eq = refl


-- ----------------------------------------------------------------------------
-- Helpers: All-self-membership, All-map-cons-mono, All-++
-- ----------------------------------------------------------------------------

private
  all-self-∈ : (xs : List DBCSignal) → All (λ x → x ∈ xs) xs
  all-self-∈ []       = []
  all-self-∈ (x ∷ xs) = here refl ∷ All.map there (all-self-∈ xs)

  all-resolvesᵇ-msgs-cons-mono :
      ∀ (rvds : List RawValueDesc) (m : DBCMessage) (ms : List DBCMessage)
    → All (λ rvd → resolvesᵇ-msgs rvd ms ≡ true) rvds
    → All (λ rvd → resolvesᵇ-msgs rvd (m ∷ ms) ≡ true) rvds
  all-resolvesᵇ-msgs-cons-mono []         _ _  []         = []
  all-resolvesᵇ-msgs-cons-mono (rvd ∷ rs) m ms (eq ∷ rest) =
    resolvesᵇ-msgs-cons-mono rvd m ms eq
      ∷ all-resolvesᵇ-msgs-cons-mono rs m ms rest

  all-resolves-cons-here :
      ∀ (rvds : List RawValueDesc) (m : DBCMessage) (ms : List DBCMessage)
    → All (λ rvd → matchesMsgᵇ rvd m ≡ true) rvds
    → All (λ rvd → resolvesᵇ-msgs rvd (m ∷ ms) ≡ true) rvds
  all-resolves-cons-here []         _ _  []         = []
  all-resolves-cons-here (rvd ∷ rs) m ms (eq ∷ rest) =
    matchesMsgᵇ-cons-here rvd m ms eq
      ∷ all-resolves-cons-here rs m ms rest

  All-++ : ∀ {A : Set} {P : A → Set} (xs ys : List A)
    → All P xs → All P ys → All P (xs ++ₗ ys)
  All-++ []       _  []       py = py
  All-++ (x ∷ xs) ys (px ∷ p) py = px ∷ All-++ xs ys p py


-- ----------------------------------------------------------------------------
-- 7. collectFromMessages resolves all
-- ----------------------------------------------------------------------------

collectFromMessages-resolvesAll :
    ∀ (msgs : List DBCMessage)
  → All (λ rvd → resolvesᵇ-msgs rvd msgs ≡ true) (collectFromMessages msgs)
collectFromMessages-resolvesAll []        = []
collectFromMessages-resolvesAll (m ∷ ms)  =
  All-++ (collectFromMessage m) (collectFromMessages ms)
    (all-resolves-cons-here (collectFromMessage m) m ms
      (collectFromSignals-matchesMsgᵇ m (DBCMessage.signals m)
        (all-self-∈ (DBCMessage.signals m))))
    (all-resolvesᵇ-msgs-cons-mono (collectFromMessages ms) m ms
      (collectFromMessages-resolvesAll ms))


-- ----------------------------------------------------------------------------
-- 8. unresolvedRVDs respects All-resolves
-- ----------------------------------------------------------------------------

unresolvedRVDs-respects :
    ∀ (rvds : List RawValueDesc) (msgs : List DBCMessage)
  → All (λ rvd → resolvesᵇ-msgs rvd msgs ≡ true) rvds
  → unresolvedRVDs rvds msgs ≡ []
unresolvedRVDs-respects []         _    [] = refl
unresolvedRVDs-respects (rvd ∷ rs) msgs (resolves ∷ rest)
  rewrite resolves
  = unresolvedRVDs-respects rs msgs rest


-- ----------------------------------------------------------------------------
-- 9. The final inverse-bridge: unresolvedRVDs (collectFromMessages msgs) msgs ≡ []
-- ----------------------------------------------------------------------------

unresolvedRVDs-on-collectFromMessages :
    ∀ (msgs : List DBCMessage)
  → unresolvedRVDs (collectFromMessages msgs) msgs ≡ []
unresolvedRVDs-on-collectFromMessages msgs =
  unresolvedRVDs-respects
    (collectFromMessages msgs) msgs
    (collectFromMessages-resolvesAll msgs)

-- ============================================================================
-- E.9a — `unresolvedRVDs ∘ collectFromMessages ≡ []` on the cleared form
-- ============================================================================
--
-- The Universal layer (post-E.9a) sees `CollectedTop.messages = map
-- clearVdsMsg d.messages`, so `buildDBC` computes `unresolvedRVDs
-- (collectFromMessages d.messages) (map clearVdsMsg d.messages)`.
-- `clearVdsMsg` preserves `DBCMessage.id` and per-signal `DBCSignal.name`
-- (the only fields `resolvesᵇ-msgs` reads), so the cleared form
-- resolves identically to the original.

private
  -- Per-signal: matchesSigᵇ on a cleared signal equals matchesSigᵇ
  -- on the original (matchesSigᵇ only reads `DBCSignal.name`, which
  -- `clearVds` preserves).  Definitional.
  matchesSigᵇ-clearVds :
      ∀ (rvd : RawValueDesc) (s : DBCSignal)
    → matchesSigᵇ rvd (clearVds s) ≡ matchesSigᵇ rvd s
  matchesSigᵇ-clearVds _ _ = refl

  -- `any (matchesSigᵇ rvd) (map clearVds sigs) ≡ any (matchesSigᵇ rvd) sigs`.
  -- By induction on `sigs`; each cons step rewrites the head via the
  -- per-signal lemma (`refl`), then recurses.
  any-matchesSigᵇ-map-clearVds :
      ∀ (rvd : RawValueDesc) (sigs : List DBCSignal)
    → any (matchesSigᵇ rvd) (map clearVds sigs)
      ≡ any (matchesSigᵇ rvd) sigs
  any-matchesSigᵇ-map-clearVds _   []       = refl
  any-matchesSigᵇ-map-clearVds rvd (s ∷ ss) =
    cong (matchesSigᵇ rvd s ∨_)
         (any-matchesSigᵇ-map-clearVds rvd ss)

  -- Per-message: matchesMsgᵇ on the cleared form equals the original.
  matchesMsgᵇ-clearVdsMsg :
      ∀ (rvd : RawValueDesc) (msg : DBCMessage)
    → matchesMsgᵇ rvd (clearVdsMsg msg) ≡ matchesMsgᵇ rvd msg
  matchesMsgᵇ-clearVdsMsg rvd msg =
    cong (⌊ RawValueDesc.canId rvd ≟-CANId DBCMessage.id msg ⌋ ∧_)
         (any-matchesSigᵇ-map-clearVds rvd (DBCMessage.signals msg))

  -- List-level: `resolvesᵇ-msgs` on the cleared message list equals
  -- the original.  By induction on `msgs`.
  resolvesᵇ-msgs-clearVdsMsg :
      ∀ (rvd : RawValueDesc) (msgs : List DBCMessage)
    → resolvesᵇ-msgs rvd (map clearVdsMsg msgs)
      ≡ resolvesᵇ-msgs rvd msgs
  resolvesᵇ-msgs-clearVdsMsg _   []       = refl
  resolvesᵇ-msgs-clearVdsMsg rvd (m ∷ ms) =
    cong₂ _∨_
      (matchesMsgᵇ-clearVdsMsg rvd m)
      (resolvesᵇ-msgs-clearVdsMsg rvd ms)
    where
      open import Relation.Binary.PropositionalEquality using (cong₂)

  -- `unresolvedRVDs` on the cleared form equals the original.  By
  -- induction on `rvds`; each cons step uses the resolves-equality
  -- to rewrite the if-condition.
  unresolvedRVDs-clearVdsMsg-eq :
      ∀ (rvds : List RawValueDesc) (msgs : List DBCMessage)
    → unresolvedRVDs rvds (map clearVdsMsg msgs)
      ≡ unresolvedRVDs rvds msgs
  unresolvedRVDs-clearVdsMsg-eq []         _    = refl
  unresolvedRVDs-clearVdsMsg-eq (rvd ∷ rs) msgs
    rewrite resolvesᵇ-msgs-clearVdsMsg rvd msgs
    with resolvesᵇ-msgs rvd msgs
  ... | true  = unresolvedRVDs-clearVdsMsg-eq rs msgs
  ... | false = cong (rvd ∷_) (unresolvedRVDs-clearVdsMsg-eq rs msgs)

-- The Universal layer's target form: `unresolvedRVDs (collectFromMessages
-- d.messages) (map clearVdsMsg d.messages) ≡ []`.
unresolvedRVDs-on-clearVdsMsgs-collectFromMessages :
    ∀ (msgs : List DBCMessage)
  → unresolvedRVDs (collectFromMessages msgs) (map clearVdsMsg msgs) ≡ []
unresolvedRVDs-on-clearVdsMsgs-collectFromMessages msgs =
  trans
    (unresolvedRVDs-clearVdsMsg-eq (collectFromMessages msgs) msgs)
    (unresolvedRVDs-on-collectFromMessages msgs)
