-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- A.2 — BO_TX_BU_ inverse-bridge proof.
--
-- Closes the base inverse-bridge:
--
--   ∀ (msgs : List DBCMessage)
--   → AllPairs _≢_ (map DBCMessage.id msgs)
--   → attachSenders (collectSenders msgs) msgs ≡ msgs
--
-- The message-level analogue of the VAL_ proof
-- (`Properties.Aggregator.Refine.ValueDescriptions`), materially simpler:
--
--   * No per-signal layer.  `senders` lives on the message, so there is a
--     SINGLE uniqueness precondition (`AllPairs _≢_ (map DBCMessage.id msgs)`)
--     — no `MessageWF` / `sig-names-unique` dimension, no Layer A.
--
--   * `collectSenders` emits at most one entry per message, so its recursion
--     is a direct cons-list (no `++`).  VAL_'s append-splitting prefix lemmas
--     (`lookup-vd-just-prefix` / `lookup-vd-nothing-prefix` / `all-++-canId-≢`)
--     collapse into two small `prependSenders` lemmas here.
--
-- Layered structure (mirrors the VAL_ proof, message granularity):
--   1. ∈-map / AllPairs-head shape bridges.
--   2. canId-≢ propagation through `collectSenders`.
--   3. Layer 1 — `lookup-senders-on-collected`: cross-message lookup under
--      msg-id uniqueness.  The crux.
--   4. Layer 2/3 — `attachToMessageSenders-on-collected`: per-message attach.
--   5. Layer 4 — `attachSenders-on-collectSenders`: list-level base bridge.
--
-- The lifted form for the universal aggregator
-- (`attachSenders (collectSenders msgs) (map clearSendersMsg msgs) ≡ msgs`)
-- is a subsequent file addition (the A.2 E.9a analogue).
module Aletheia.DBC.TextParser.Properties.Aggregator.Refine.Senders where

open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂)
open import Relation.Nullary using (yes; no)

open import Aletheia.CAN.Frame using (CANId)
open import Aletheia.CAN.DBCHelpers using (_≟-CANId_)
open import Aletheia.DBC.Identifier using (Identifier)
open import Aletheia.DBC.Types using (DBCMessage)
open import Aletheia.DBC.TextParser.Senders using
  ( RawMsgSenders; mkRawMsgSenders
  ; lookup-senders; attachWithMaybeSenders; attachToMessageSenders; attachSenders
  ; prependSenders; collectSenders
  )

-- ============================================================================
-- COLLECT-SINGLETON — the per-message lookup result shape
-- ============================================================================
--
-- `collectSenders` emits `mkRawMsgSenders m.id m.senders` only for non-empty
-- senders, so a lookup for `m.id` returns `just m.senders` (non-empty) or
-- `nothing` (empty).  `singletonFromSenders` names that target shape.

singletonFromSenders : List Identifier → Maybe (List Identifier)
singletonFromSenders []       = nothing
singletonFromSenders (x ∷ xs) = just (x ∷ xs)

-- ============================================================================
-- ∈-map and AllPairs-head shape bridges
-- ============================================================================

∈-map-DBCMessage-id :
    ∀ {m : DBCMessage} {ms : List DBCMessage}
  → m ∈ ms
  → DBCMessage.id m ∈ map DBCMessage.id ms
∈-map-DBCMessage-id (here refl)  = here refl
∈-map-DBCMessage-id (there m∈ms) = there (∈-map-DBCMessage-id m∈ms)

-- The AllPairs head gives `All (target ≢_) (map .id msgs)`.  Convert to
-- per-message shape `All (λ m' → m'.id ≢ target) msgs` (flips ≢, unmaps).
all-id-≢-from-allpairs-head :
    ∀ {target : CANId} (msgs : List DBCMessage)
  → All (target ≢_) (map DBCMessage.id msgs)
  → All (λ m' → DBCMessage.id m' ≢ target) msgs
all-id-≢-from-allpairs-head []       []         = []
all-id-≢-from-allpairs-head (m ∷ ms) (px ∷ pxs) =
  (λ eq → px (sym eq)) ∷ all-id-≢-from-allpairs-head ms pxs

-- ============================================================================
-- canId-≢ PROPAGATION through collectSenders
-- ============================================================================

-- The new head (cons branch) carries `cid₀`; under `cid₀ ≢ target` it
-- satisfies the predicate.  The `[]` branch passes `rest` through unchanged.
prependSenders-canId-≢ :
    ∀ (target cid₀ : CANId) (snds : List Identifier) (rest : List RawMsgSenders)
  → cid₀ ≢ target
  → All (λ r → RawMsgSenders.canId r ≢ target) rest
  → All (λ r → RawMsgSenders.canId r ≢ target) (prependSenders cid₀ snds rest)
prependSenders-canId-≢ _ _ []      _    _   pred = pred
prependSenders-canId-≢ _ _ (_ ∷ _) _    neq pred = neq ∷ pred

collectSenders-canId-≢ :
    ∀ (cid : CANId) (msgs : List DBCMessage)
  → All (λ m → DBCMessage.id m ≢ cid) msgs
  → All (λ r → RawMsgSenders.canId r ≢ cid) (collectSenders msgs)
collectSenders-canId-≢ _   []       []          = []
collectSenders-canId-≢ cid (m ∷ ms) (m≢ ∷ ms-≢) =
  prependSenders-canId-≢ cid (DBCMessage.id m) (DBCMessage.senders m)
    (collectSenders ms) m≢
    (collectSenders-canId-≢ cid ms ms-≢)

-- ============================================================================
-- LOOKUP DISCIPLINE — nothing on no-match, target-match, and skip
-- ============================================================================

-- All entries fail the canId match ⇒ lookup falls through to `nothing`.
lookup-senders-on-all-canId-≢ :
    ∀ (cid : CANId) (rms : List RawMsgSenders)
  → All (λ r → RawMsgSenders.canId r ≢ cid) rms
  → lookup-senders cid rms ≡ nothing
lookup-senders-on-all-canId-≢ _   []                               []          = refl
lookup-senders-on-all-canId-≢ cid (mkRawMsgSenders rcid _ ∷ rs) (r≢ ∷ rs-≢)
  with cid ≟-CANId rcid
... | yes eq = ⊥-elim (r≢ (sym eq))
... | no  _  = lookup-senders-on-all-canId-≢ cid rs rs-≢

-- The prepended head (own cid) is the match; under `lookup rest ≡ nothing`
-- the lookup recovers `singletonFromSenders snds`.
lookup-senders-on-prependSenders-eq :
    ∀ (cid : CANId) (snds : List Identifier) (rest : List RawMsgSenders)
  → lookup-senders cid rest ≡ nothing
  → lookup-senders cid (prependSenders cid snds rest) ≡ singletonFromSenders snds
lookup-senders-on-prependSenders-eq _   []        _    tail-nothing = tail-nothing
lookup-senders-on-prependSenders-eq cid (_ ∷ _)   _    _            with cid ≟-CANId cid
... | yes _    = refl
... | no  cid≢ = ⊥-elim (cid≢ refl)

-- A prepend whose head cid ≢ target is a no-op for a target lookup.
lookup-senders-on-prependSenders-skip :
    ∀ (target cid₀ : CANId) (snds : List Identifier) (rest : List RawMsgSenders)
  → cid₀ ≢ target
  → lookup-senders target (prependSenders cid₀ snds rest)
    ≡ lookup-senders target rest
lookup-senders-on-prependSenders-skip _      _    []      _    _   = refl
lookup-senders-on-prependSenders-skip target cid₀ (_ ∷ _) _    neq with target ≟-CANId cid₀
... | yes eq = ⊥-elim (neq (sym eq))
... | no  _  = refl

-- ============================================================================
-- LAYER 1 — cross-message lookup-on-collected
-- ============================================================================

lookup-senders-on-collected :
    ∀ (msgs : List DBCMessage) (m : DBCMessage)
  → m ∈ msgs
  → AllPairs _≢_ (map DBCMessage.id msgs)
  → lookup-senders (DBCMessage.id m) (collectSenders msgs)
    ≡ singletonFromSenders (DBCMessage.senders m)
-- m at head: the prepended head matches by its own cid; the tail returns
-- nothing (no message in rest shares m's id, by cross-message uniqueness).
lookup-senders-on-collected (.m ∷ rest) m (here refl) (m-id≢-all ∷ _) =
  lookup-senders-on-prependSenders-eq (DBCMessage.id m) (DBCMessage.senders m)
    (collectSenders rest)
    (lookup-senders-on-all-canId-≢ (DBCMessage.id m) (collectSenders rest)
      (collectSenders-canId-≢ (DBCMessage.id m) rest
        (all-id-≢-from-allpairs-head rest m-id≢-all)))
-- m later: head m₀.id ≢ m.id by uniqueness; the head prepend is a skip;
-- recurse on rest.
lookup-senders-on-collected (m₀ ∷ rest) m (there m∈rest) (m₀-≢-all ∷ rest-uniq) =
  trans
    (lookup-senders-on-prependSenders-skip (DBCMessage.id m) (DBCMessage.id m₀)
       (DBCMessage.senders m₀) (collectSenders rest)
       (All.lookup m₀-≢-all (∈-map-DBCMessage-id m∈rest)))
    (lookup-senders-on-collected rest m m∈rest rest-uniq)

-- ============================================================================
-- LAYER 2/3 — per-message attach
-- ============================================================================

-- attachWithMaybeSenders against the singletonFromSenders output recovers `m`.
-- empty senders → nothing branch (m pass-through); cons senders → record-η
-- under the senders equation.
attachWithMaybeSenders-on-singletonFromSenders :
    ∀ (m : DBCMessage) (snds : List Identifier)
  → DBCMessage.senders m ≡ snds
  → attachWithMaybeSenders m (singletonFromSenders snds) ≡ m
attachWithMaybeSenders-on-singletonFromSenders _ []       _  = refl
attachWithMaybeSenders-on-singletonFromSenders m (x ∷ snds) eq =
  trans (cong (λ z → record m { senders = z }) (sym eq)) record-η-senders
  where
    -- η-rule for DBCMessage records: definitional under `--without-K`
    -- because DBCMessage has no explicit `constructor` declaration.
    record-η-senders : record m { senders = DBCMessage.senders m } ≡ m
    record-η-senders = refl

attachToMessageSenders-on-collected :
    ∀ (msgs : List DBCMessage) (m : DBCMessage)
  → m ∈ msgs
  → AllPairs _≢_ (map DBCMessage.id msgs)
  → attachToMessageSenders (collectSenders msgs) m ≡ m
attachToMessageSenders-on-collected msgs m m∈ msg-uniq =
  trans
    (cong (attachWithMaybeSenders m)
      (lookup-senders-on-collected msgs m m∈ msg-uniq))
    (attachWithMaybeSenders-on-singletonFromSenders m (DBCMessage.senders m) refl)

-- ============================================================================
-- map-≡-id helper — pointwise identity over `map`
-- ============================================================================

map-≡-id :
    ∀ {A : Set} (xs : List A) (f : A → A)
  → (∀ x → x ∈ xs → f x ≡ x)
  → map f xs ≡ xs
map-≡-id []       _ _ = refl
map-≡-id (x ∷ xs) f p =
  cong₂ _∷_
    (p x (here refl))
    (map-≡-id xs f (λ x' x'∈ → p x' (there x'∈)))

-- ============================================================================
-- LAYER 4 — list-level inverse-bridge (the base target)
-- ============================================================================

attachSenders-on-collectSenders :
    ∀ (msgs : List DBCMessage)
  → AllPairs _≢_ (map DBCMessage.id msgs)
  → attachSenders (collectSenders msgs) msgs ≡ msgs
attachSenders-on-collectSenders msgs msg-uniq =
  map-≡-id msgs
    (attachToMessageSenders (collectSenders msgs))
    (λ m m∈ → attachToMessageSenders-on-collected msgs m m∈ msg-uniq)
