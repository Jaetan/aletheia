{-# OPTIONS --safe --without-K #-}

-- Track E.6 — VAL_ inverse-bridge proof.
--
-- Closes:
--
--   ∀ (msgs : List DBCMessage)
--   → AllPairs _≢_ (map DBCMessage.id msgs)
--   → All MessageWF msgs
--   → attachValueDescs (collectFromMessages msgs) msgs ≡ msgs
--
-- Layered structure (advisor-locked plan):
--
--   1. Helpers: prependVdsRvd-* family + ⌊≟⌋ collapse + ∈-map bridges +
--      AllPairs-head shape converters.
--   2. Layer A — `lookup-vd-on-collectFromSignals-found`: within one
--      message's signal list (under name uniqueness).
--   3. Layer 1 — `lookup-on-collected`: cross-message (under msg-id +
--      within-msg-name uniqueness).  The crux of E.6.
--   4. Layer 2-4 — per-signal / per-message / list-level (subsequent
--      file additions).
module Aletheia.DBC.TextParser.Properties.Aggregator.Refine.ValueDescriptions where

open import Data.Bool using (Bool; true; false; if_then_else_; _∧_)
open import Data.Char using (Char)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; map)
  renaming (_++_ to _++ₗ_)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import Aletheia.CAN.Frame using (CANId)
open import Aletheia.CAN.DBCHelpers using (_≟-CANId_)
open import Aletheia.DBC.Identifier using (Identifier; _≟ᴵ_)
open import Aletheia.DBC.Types using (DBCSignal; DBCMessage; clearVds; clearVdsMsg)
open import Aletheia.DBC.TextParser.ValueTables using
  (RawValueDesc; mkRawValueDesc)
open import Aletheia.DBC.TextParser.ValueDescriptions using
  ( lookup-vd
  ; attachWithMaybe; attachToSignal; attachToMessage; attachValueDescs
  ; prependVdsRvd
  ; collectFromSignals; collectFromMessage; collectFromMessages
  ; matchesSigᵇ; matchesMsgᵇ; resolvesᵇ-msgs; unresolvedRVDs
  )
open import Aletheia.DBC.TextParser.Properties.Topology.Message using
  (MessageWF)
open import Aletheia.DBC.TextParser.Properties.ValueTables.ValueDesc using
  (RawValueDescStop)
open import Aletheia.DBC.TextParser.Format.ValueDescription using
  (RawValueDescNameStop)
open import Aletheia.DBC.TextParser.Properties.Aggregator.Dispatcher.Attribute.Foundations using
  (identifier-name-stop)
open import Aletheia.DBC.TextParser.Properties.Attributes.Assign using
  (IdentNameStop)

-- ============================================================================
-- DECIDABLE-EQUALITY MICRO-LEMMAS
-- ============================================================================

⌊≟-CANId⌋-refl : ∀ (cid : CANId) → ⌊ cid ≟-CANId cid ⌋ ≡ true
⌊≟-CANId⌋-refl cid with cid ≟-CANId cid
... | yes _    = refl
... | no  cid≢ = ⊥-elim (cid≢ refl)

⌊≟ᴵ⌋-refl : ∀ (i : Identifier) → ⌊ i ≟ᴵ i ⌋ ≡ true
⌊≟ᴵ⌋-refl i with i ≟ᴵ i
... | yes _    = refl
... | no  i≢   = ⊥-elim (i≢ refl)

⌊≟-CANId⌋-≢ : ∀ (cid₁ cid₂ : CANId) → cid₁ ≢ cid₂ → ⌊ cid₁ ≟-CANId cid₂ ⌋ ≡ false
⌊≟-CANId⌋-≢ cid₁ cid₂ neq with cid₁ ≟-CANId cid₂
... | yes eq = ⊥-elim (neq eq)
... | no  _  = refl

⌊≟ᴵ⌋-≢ : ∀ (i j : Identifier) → i ≢ j → ⌊ i ≟ᴵ j ⌋ ≡ false
⌊≟ᴵ⌋-≢ i j neq with i ≟ᴵ j
... | yes eq = ⊥-elim (neq eq)
... | no  _  = refl

-- ============================================================================
-- COLLECT-FROM-SIGNAL-SINGLETON
-- ============================================================================

singletonFromVds : CANId → Identifier → List (ℕ × List Char) → Maybe RawValueDesc
singletonFromVds _   _    []        = nothing
singletonFromVds cid name (x ∷ vds) = just (mkRawValueDesc cid name (x ∷ vds))

collectFromSignal-singleton : CANId → DBCSignal → Maybe RawValueDesc
collectFromSignal-singleton cid s =
  singletonFromVds cid (DBCSignal.name s) (DBCSignal.valueDescriptions s)

-- ============================================================================
-- prependVdsRvd HELPERS — case-split on vds delegated to function-side
-- ============================================================================

-- The All-canId predicate propagates through prependVdsRvd: the new head
-- (in the cons branch) trivially has canId ≡ cid; the [] branch passes
-- the input All through unchanged.
prependVdsRvd-canId-all :
    ∀ (cid : CANId) (name : Identifier) (vds : List (ℕ × List Char))
      (rest : List RawValueDesc)
  → All (λ rvd → RawValueDesc.canId rvd ≡ cid) rest
  → All (λ rvd → RawValueDesc.canId rvd ≡ cid) (prependVdsRvd cid name vds rest)
prependVdsRvd-canId-all _   _    []        _    pred = pred
prependVdsRvd-canId-all _   _    (_ ∷ _)   _    pred = refl ∷ pred

-- A name-not-matching prepend is a no-op for lookup-vd's name match.
-- (The cid check passes — same cid both sides — but the name check fails
-- when name' ≢ name, sending the if-step to the else branch, and the
-- recursion lands on `rest`.)
lookup-vd-on-prependVdsRvd-name-≢-pass :
    ∀ (cid : CANId) (name name' : Identifier) (vds : List (ℕ × List Char))
      (rest : List RawValueDesc)
  → name' ≢ name
  → lookup-vd cid name (prependVdsRvd cid name' vds rest) ≡ lookup-vd cid name rest
lookup-vd-on-prependVdsRvd-name-≢-pass _   _    _     []        _    _    = refl
lookup-vd-on-prependVdsRvd-name-≢-pass cid name name' (_ ∷ _)   rest n'≢n
  rewrite ⌊≟-CANId⌋-refl cid
        | ⌊≟ᴵ⌋-≢ name name' (λ eq → n'≢n (sym eq))
  = refl

-- A name-matching prepend produces the singleton: cid matches (same cid),
-- name matches (same name), so lookup-vd's first step returns just the
-- new rvd.  In the [] branch, prepend is a no-op and we fall back on
-- `rest`'s lookup result — which the caller pre-establishes as `nothing`
-- (driven by within-message name uniqueness).
lookup-vd-on-prependVdsRvd-name-eq :
    ∀ (cid : CANId) (name : Identifier) (vds : List (ℕ × List Char))
      (rest : List RawValueDesc)
  → lookup-vd cid name rest ≡ nothing
  → lookup-vd cid name (prependVdsRvd cid name vds rest)
    ≡ singletonFromVds cid name vds
lookup-vd-on-prependVdsRvd-name-eq _   _    []      _    eq = eq
lookup-vd-on-prependVdsRvd-name-eq cid name (_ ∷ _) _    _
  rewrite ⌊≟-CANId⌋-refl cid
        | ⌊≟ᴵ⌋-refl name
  = refl

-- ============================================================================
-- HELPER 1 — collectFromMessage's rvds all carry that message's CAN ID
-- ============================================================================

collectFromSignals-canId-all :
    ∀ (cid : CANId) (sigs : List DBCSignal)
  → All (λ rvd → RawValueDesc.canId rvd ≡ cid) (collectFromSignals cid sigs)
collectFromSignals-canId-all cid []       = []
collectFromSignals-canId-all cid (s ∷ ss) =
  prependVdsRvd-canId-all cid (DBCSignal.name s) (DBCSignal.valueDescriptions s)
    (collectFromSignals cid ss)
    (collectFromSignals-canId-all cid ss)

collectFromMessage-canId-all :
    ∀ (m : DBCMessage)
  → All (λ rvd → RawValueDesc.canId rvd ≡ DBCMessage.id m) (collectFromMessage m)
collectFromMessage-canId-all m =
  collectFromSignals-canId-all (DBCMessage.id m) (DBCMessage.signals m)

-- ============================================================================
-- HELPER 2 — lookup-vd skips a non-matching prefix
-- ============================================================================

lookup-vd-skip-prefix :
    ∀ (cid : CANId) (name : Identifier)
      (prefix : List RawValueDesc) (rest : List RawValueDesc)
  → All (λ rvd → RawValueDesc.canId rvd ≢ cid) prefix
  → lookup-vd cid name (prefix ++ₗ rest) ≡ lookup-vd cid name rest
lookup-vd-skip-prefix cid name [] rest [] = refl
lookup-vd-skip-prefix cid name (mkRawValueDesc rcid rname _ ∷ rs) rest (rcid≢cid ∷ rest-all)
  rewrite ⌊≟-CANId⌋-≢ cid rcid (λ eq → rcid≢cid (sym eq))
  = lookup-vd-skip-prefix cid name rs rest rest-all

-- ============================================================================
-- HELPER 2b — lookup-vd returns nothing when every rvd has non-matching canId
-- ============================================================================
--
-- Specialisation of `lookup-vd-skip-prefix` with `rest = []` and
-- closed under `lookup-vd cid name [] = nothing`.

lookup-vd-on-all-canId-≢ :
    ∀ (cid : CANId) (name : Identifier) (rvds : List RawValueDesc)
  → All (λ rvd → RawValueDesc.canId rvd ≢ cid) rvds
  → lookup-vd cid name rvds ≡ nothing
lookup-vd-on-all-canId-≢ _   _    [] [] = refl
lookup-vd-on-all-canId-≢ cid name (mkRawValueDesc rcid rname _ ∷ rs) (rcid≢cid ∷ rest-all)
  rewrite ⌊≟-CANId⌋-≢ cid rcid (λ eq → rcid≢cid (sym eq))
  = lookup-vd-on-all-canId-≢ cid name rs rest-all

-- ============================================================================
-- HELPER 3 — lookup-vd returns nothing when no signal name matches
-- ============================================================================

lookup-vd-name-not-in-collectFromSignals :
    ∀ (cid : CANId) (name : Identifier) (sigs : List DBCSignal)
  → All (λ s' → DBCSignal.name s' ≢ name) sigs
  → lookup-vd cid name (collectFromSignals cid sigs) ≡ nothing
lookup-vd-name-not-in-collectFromSignals cid name [] [] = refl
lookup-vd-name-not-in-collectFromSignals cid name (s ∷ ss) (s≢ ∷ ss-≢) =
  trans
    (lookup-vd-on-prependVdsRvd-name-≢-pass cid name (DBCSignal.name s)
       (DBCSignal.valueDescriptions s) (collectFromSignals cid ss) s≢)
    (lookup-vd-name-not-in-collectFromSignals cid name ss ss-≢)

-- ============================================================================
-- HELPER 4 — first-match-wins discipline of lookup-vd
-- ============================================================================

lookup-vd-just-prefix :
    ∀ (cid : CANId) (name : Identifier)
      (prefix : List RawValueDesc) (rest : List RawValueDesc) (rvd : RawValueDesc)
  → lookup-vd cid name prefix ≡ just rvd
  → lookup-vd cid name (prefix ++ₗ rest) ≡ just rvd
lookup-vd-just-prefix cid name [] rest rvd ()
lookup-vd-just-prefix cid name (mkRawValueDesc rcid rname _ ∷ rs) rest rvd eq
  with cid ≟-CANId rcid | name ≟ᴵ rname
... | yes _ | yes _ = eq
... | yes _ | no  _ = lookup-vd-just-prefix cid name rs rest rvd eq
... | no  _ | yes _ = lookup-vd-just-prefix cid name rs rest rvd eq
... | no  _ | no  _ = lookup-vd-just-prefix cid name rs rest rvd eq

-- ============================================================================
-- HELPER 5 — fall-through when the prefix returns nothing
-- ============================================================================

lookup-vd-nothing-prefix :
    ∀ (cid : CANId) (name : Identifier)
      (prefix : List RawValueDesc) (rest : List RawValueDesc)
  → lookup-vd cid name prefix ≡ nothing
  → lookup-vd cid name (prefix ++ₗ rest) ≡ lookup-vd cid name rest
lookup-vd-nothing-prefix cid name [] rest _ = refl
lookup-vd-nothing-prefix cid name (mkRawValueDesc rcid rname _ ∷ rs) rest eq
  with cid ≟-CANId rcid | name ≟ᴵ rname
... | yes _ | yes _ = ⊥-elim (just≢nothing eq)
  where
    just≢nothing : ∀ {A : Set} {x : A} → just x ≡ nothing → ⊥
    just≢nothing ()
... | yes _ | no  _ = lookup-vd-nothing-prefix cid name rs rest eq
... | no  _ | yes _ = lookup-vd-nothing-prefix cid name rs rest eq
... | no  _ | no  _ = lookup-vd-nothing-prefix cid name rs rest eq

-- ============================================================================
-- ∈-map and AllPairs-head shape bridges
-- ============================================================================

∈-map-DBCSignal-name :
    ∀ {s : DBCSignal} {ss : List DBCSignal}
  → s ∈ ss
  → DBCSignal.name s ∈ map DBCSignal.name ss
∈-map-DBCSignal-name (here refl)  = here refl
∈-map-DBCSignal-name (there s∈ss) = there (∈-map-DBCSignal-name s∈ss)

∈-map-DBCMessage-id :
    ∀ {m : DBCMessage} {ms : List DBCMessage}
  → m ∈ ms
  → DBCMessage.id m ∈ map DBCMessage.id ms
∈-map-DBCMessage-id (here refl)  = here refl
∈-map-DBCMessage-id (there m∈ms) = there (∈-map-DBCMessage-id m∈ms)

-- The AllPairs head gives `All (target ≢_) (map .name sigs)`.  Convert
-- to per-signal shape: `All (λ s' → s'.name ≢ target) sigs`.  Flips ≢
-- direction and unmaps.
all-name-≢-from-allpairs-head :
    ∀ {target : Identifier} (sigs : List DBCSignal)
  → All (target ≢_) (map DBCSignal.name sigs)
  → All (λ s' → DBCSignal.name s' ≢ target) sigs
all-name-≢-from-allpairs-head []       []         = []
all-name-≢-from-allpairs-head (s ∷ ss) (px ∷ pxs) =
  (λ eq → px (sym eq)) ∷ all-name-≢-from-allpairs-head ss pxs

all-id-≢-from-allpairs-head :
    ∀ {target : CANId} (msgs : List DBCMessage)
  → All (target ≢_) (map DBCMessage.id msgs)
  → All (λ m' → DBCMessage.id m' ≢ target) msgs
all-id-≢-from-allpairs-head []       []         = []
all-id-≢-from-allpairs-head (m ∷ ms) (px ∷ pxs) =
  (λ eq → px (sym eq)) ∷ all-id-≢-from-allpairs-head ms pxs

-- ============================================================================
-- LAYER A — within-message lookup-on-collected
-- ============================================================================

lookup-vd-on-collectFromSignals-found :
    ∀ (cid : CANId) (sigs : List DBCSignal) (s : DBCSignal)
  → s ∈ sigs
  → AllPairs _≢_ (map DBCSignal.name sigs)
  → lookup-vd cid (DBCSignal.name s) (collectFromSignals cid sigs)
    ≡ collectFromSignal-singleton cid s
-- s at head: prepended rvd matches by both cid and name; rest yields nothing
-- (no signal in tail shares s's name, by within-message uniqueness).
lookup-vd-on-collectFromSignals-found cid (s ∷ ss) .s (here refl) (s≢-all ∷ rest-uniq) =
  lookup-vd-on-prependVdsRvd-name-eq cid (DBCSignal.name s)
    (DBCSignal.valueDescriptions s)
    (collectFromSignals cid ss)
    (lookup-vd-name-not-in-collectFromSignals cid (DBCSignal.name s) ss
      (all-name-≢-from-allpairs-head ss s≢-all))
-- s later: head s₀ ≠ s by uniqueness; head's prepend is a non-matching
-- pass-through; recurse on tail.
lookup-vd-on-collectFromSignals-found cid (s₀ ∷ ss) s (there s∈ss) (s₀≢-all ∷ rest-uniq) =
  trans
    (lookup-vd-on-prependVdsRvd-name-≢-pass cid (DBCSignal.name s) (DBCSignal.name s₀)
       (DBCSignal.valueDescriptions s₀) (collectFromSignals cid ss)
       (All.lookup s₀≢-all (∈-map-DBCSignal-name s∈ss)))
    (lookup-vd-on-collectFromSignals-found cid ss s s∈ss rest-uniq)

-- ============================================================================
-- HELPER 6 — collectFromMessages of all-different-id messages
-- ============================================================================

all-++-canId-≢ :
    ∀ (cid : CANId) (xs ys : List RawValueDesc)
  → All (λ rvd → RawValueDesc.canId rvd ≢ cid) xs
  → All (λ rvd → RawValueDesc.canId rvd ≢ cid) ys
  → All (λ rvd → RawValueDesc.canId rvd ≢ cid) (xs ++ₗ ys)
all-++-canId-≢ _   []       _ []          ays = ays
all-++-canId-≢ cid (_ ∷ xs) ys (px ∷ pxs) ays =
  px ∷ all-++-canId-≢ cid xs ys pxs ays

collectFromMessages-canId-≢ :
    ∀ (cid : CANId) (msgs : List DBCMessage)
  → All (λ m → DBCMessage.id m ≢ cid) msgs
  → All (λ rvd → RawValueDesc.canId rvd ≢ cid) (collectFromMessages msgs)
collectFromMessages-canId-≢ cid []        []          = []
collectFromMessages-canId-≢ cid (m ∷ ms)  (m≢ ∷ ms-≢) =
  all-++-canId-≢ cid (collectFromMessage m) (collectFromMessages ms)
    (All.map (λ {rvd} cid-eq → λ k → m≢ (trans (sym cid-eq) k))
             (collectFromMessage-canId-all m))
    (collectFromMessages-canId-≢ cid ms ms-≢)

-- ============================================================================
-- LAYER 1 — cross-message lookup-on-collected
-- ============================================================================

lookup-on-collected :
    ∀ (msgs : List DBCMessage) (m : DBCMessage) (s : DBCSignal)
  → m ∈ msgs
  → s ∈ DBCMessage.signals m
  → AllPairs _≢_ (map DBCMessage.id msgs)
  → AllPairs _≢_ (map DBCSignal.name (DBCMessage.signals m))
  → lookup-vd (DBCMessage.id m) (DBCSignal.name s) (collectFromMessages msgs)
    ≡ collectFromSignal-singleton (DBCMessage.id m) s
-- m at head of msgs: collectFromMessages = collectFromMessage m ++ collectFromMessages rest.
-- Layer A handles the prefix; case-split on the layer-A result drives the right composition.
lookup-on-collected (.m ∷ rest) m s (here refl) s∈sigs (m-id≢-all ∷ rest-id-uniq) sig-uniq
  with collectFromSignal-singleton (DBCMessage.id m) s
     | lookup-vd-on-collectFromSignals-found
         (DBCMessage.id m) (DBCMessage.signals m) s s∈sigs sig-uniq
... | nothing | within-eq =
  trans
    (lookup-vd-nothing-prefix (DBCMessage.id m) (DBCSignal.name s)
       (collectFromMessage m) (collectFromMessages rest)
       within-eq)
    (lookup-vd-on-all-canId-≢ (DBCMessage.id m) (DBCSignal.name s)
       (collectFromMessages rest)
       (collectFromMessages-canId-≢ (DBCMessage.id m) rest
         (all-id-≢-from-allpairs-head rest m-id≢-all)))
... | just rvd | within-eq =
  lookup-vd-just-prefix (DBCMessage.id m) (DBCSignal.name s)
    (collectFromMessage m) (collectFromMessages rest) rvd
    within-eq
-- m later in msgs: skip m₀'s contribution (m₀.id ≢ m.id), recurse on rest.
lookup-on-collected (m₀ ∷ rest) m s (there m∈rest) s∈sigs (m₀-≢-all ∷ rest-id-uniq) sig-uniq =
  trans
    (lookup-vd-skip-prefix (DBCMessage.id m) (DBCSignal.name s)
       (collectFromMessage m₀) (collectFromMessages rest)
       (All.map (λ {rvd} cid-eq → λ k → m₀≢m (trans (sym cid-eq) k))
                (collectFromMessage-canId-all m₀)))
    (lookup-on-collected rest m s m∈rest s∈sigs rest-id-uniq sig-uniq)
  where
    -- m₀.id ≢ m.id from AllPairs head + m∈rest membership.
    m₀≢m : DBCMessage.id m₀ ≢ DBCMessage.id m
    m₀≢m = All.lookup m₀-≢-all (∈-map-DBCMessage-id m∈rest)

-- ============================================================================
-- LAYER 2 — per-signal attach
-- ============================================================================
--
-- attachWithMaybe driver for the singletonFromVds output.  Two cases:
-- empty vds (matches the nothing case → s pass-through) and cons vds
-- (matches the just case → record-η under the s.vds equation).

attachWithMaybe-on-singletonFromVds :
    ∀ (cid : CANId) (s : DBCSignal) (vds : List (ℕ × List Char))
  → DBCSignal.valueDescriptions s ≡ vds
  → attachWithMaybe s (singletonFromVds cid (DBCSignal.name s) vds) ≡ s
attachWithMaybe-on-singletonFromVds _   _ []        _   = refl
attachWithMaybe-on-singletonFromVds cid s (x ∷ vds) eq  =
  trans (cong (λ z → record s { valueDescriptions = z }) (sym eq))
        record-η-vds
  where
    -- η-rule for DBCSignal records: `record s { f = s.f } ≡ s`.
    -- Definitional under `--without-K` because DBCSignal has no
    -- explicit `constructor` declaration.
    record-η-vds : record s { valueDescriptions = DBCSignal.valueDescriptions s } ≡ s
    record-η-vds = refl

attachToSignal-on-collected :
    ∀ (msgs : List DBCMessage) (m : DBCMessage) (s : DBCSignal)
  → m ∈ msgs
  → s ∈ DBCMessage.signals m
  → AllPairs _≢_ (map DBCMessage.id msgs)
  → AllPairs _≢_ (map DBCSignal.name (DBCMessage.signals m))
  → attachToSignal (collectFromMessages msgs) (DBCMessage.id m) s ≡ s
attachToSignal-on-collected msgs m s m∈ s∈sigs msg-uniq sig-uniq =
  trans
    (cong (attachWithMaybe s)
      (lookup-on-collected msgs m s m∈ s∈sigs msg-uniq sig-uniq))
    (attachWithMaybe-on-singletonFromVds (DBCMessage.id m) s
       (DBCSignal.valueDescriptions s) refl)

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
  where
    open import Relation.Binary.PropositionalEquality using (cong₂)

-- ============================================================================
-- LAYER 3 — per-message attach
-- ============================================================================
--
-- attachToMessage rvds m = record m { signals = map (attachToSignal rvds m.id) m.signals }.
-- Under L2 pointwise + record-η on signals, this collapses to m.

attachToMessage-on-collected :
    ∀ (msgs : List DBCMessage) (m : DBCMessage)
  → m ∈ msgs
  → AllPairs _≢_ (map DBCMessage.id msgs)
  → All MessageWF msgs
  → attachToMessage (collectFromMessages msgs) m ≡ m
attachToMessage-on-collected msgs m m∈ msg-uniq all-wfs =
  trans
    (cong (λ ss → record m { signals = ss })
      (map-≡-id (DBCMessage.signals m)
        (attachToSignal (collectFromMessages msgs) (DBCMessage.id m))
        (λ s s∈sigs →
          attachToSignal-on-collected msgs m s m∈ s∈sigs msg-uniq
            (MessageWF.sig-names-unique (All.lookup all-wfs m∈)))))
    record-η-signals
  where
    -- η-rule for DBCMessage records.
    record-η-signals : record m { signals = DBCMessage.signals m } ≡ m
    record-η-signals = refl

-- ============================================================================
-- LAYER 4 — list-level inverse-bridge (the universal target)
-- ============================================================================

attachValueDescs-on-collectFromMessages :
    ∀ (msgs : List DBCMessage)
  → AllPairs _≢_ (map DBCMessage.id msgs)
  → All MessageWF msgs
  → attachValueDescs (collectFromMessages msgs) msgs ≡ msgs
attachValueDescs-on-collectFromMessages msgs msg-uniq all-wfs =
  map-≡-id msgs
    (attachToMessage (collectFromMessages msgs))
    (λ m m∈ → attachToMessage-on-collected msgs m m∈ msg-uniq all-wfs)

-- ============================================================================
-- E.9a — clearVds bridge for non-vacuous tvd-WF coverage
-- ============================================================================
--
-- E.7's universal proof closed vacuously: `MessageWF.vds-empty` (an E.1
-- interim clause) forced `collectFromMessages msgs ≡ []`, so the TVD
-- chunk's `All RawValueDescStop` precondition was discharged via
-- `subst (All P) (sym (cong (map TVD) (collectFromMessages-vds-empty …))) []`.
--
-- E.9a lifts `vds-empty`.  Without it, `parseMessage`-produced messages
-- carry `vds = []` (because `buildSignal` hardcodes `valueDescriptions =
-- []` — VAL_ entries are scattered across the file and the parser only
-- sees per-line context).  The universal proof must therefore bridge
-- between the parsed shape (signals with `vds = []`) and `d.messages`
-- (signals with their original vds).  E.6 already proved
-- `attachValueDescs (collectFromMessages msgs) msgs ≡ msgs`; this section
-- proves the variant we need:
--
--   attachValueDescs (collectFromMessages msgs) (map clearVdsMsg msgs) ≡ msgs
--
-- under the same WF preconditions.  Composes with E.6 by establishing
-- per-signal: `attachToSignal (collectFromMessages msgs) m.id (clearVds s) ≡ s`
-- (whenever `m ∈ msgs`, `s ∈ m.signals`).
--
-- Reduction trick: under `lookup-on-collected`, the lookup result equals
-- `singletonFromVds m.id s.name s.vds`.  In the `nothing` (`s.vds = []`)
-- branch, `clearVds s ≡ s` definitionally because `s.vds` already is `[]`.
-- In the `just` branch, the double record-update
-- `record (record s { vds = [] }) { vds = (x ∷ vds) }` collapses to
-- `record s { vds = (x ∷ vds) }` via Agda's η-rule for records (no
-- explicit constructor on `DBCSignal`), then equals `s` via `s.vds ≡
-- (x ∷ vds)`.

-- `clearVds` / `clearVdsMsg` defined in `Aletheia.DBC.Types` so this
-- file and the cascade in Resolve / Message / Foundations / Dispatcher
-- can all reference the same definitions without inducing a cycle.

-- Per-signal: applying attachWithMaybe to (clearVds s) over the
-- singletonFromVds output recovers the original `s` under `s.vds ≡ vds`.
-- Mirrors `attachWithMaybe-on-singletonFromVds` (used by E.6's per-signal
-- proof), but with `clearVds s` substituted in attachWithMaybe's first
-- argument.  Both branches use the same `cong (sym eq) ; refl` chain
-- because the η-rule reduces both `record s { vds = [] }` (via eq : s.vds
-- ≡ []) and `record (clearVds s) { vds = (x ∷ vds) }` (via double-update
-- collapse, then eq : s.vds ≡ x ∷ vds) to `s`.
attachWithMaybe-clearVds-on-singletonFromVds :
    ∀ (cid : CANId) (s : DBCSignal) (vds : List (ℕ × List Char))
  → DBCSignal.valueDescriptions s ≡ vds
  → attachWithMaybe (clearVds s) (singletonFromVds cid (DBCSignal.name s) vds) ≡ s
attachWithMaybe-clearVds-on-singletonFromVds _   s [] eq =
  trans (cong (λ z → record s { valueDescriptions = z }) (sym eq))
        record-η-vds
  where
    record-η-vds : record s { valueDescriptions = DBCSignal.valueDescriptions s } ≡ s
    record-η-vds = refl
attachWithMaybe-clearVds-on-singletonFromVds cid s (x ∷ vds) eq =
  trans (cong (λ z → record s { valueDescriptions = z }) (sym eq))
        record-η-vds
  where
    record-η-vds : record s { valueDescriptions = DBCSignal.valueDescriptions s } ≡ s
    record-η-vds = refl

-- Per-signal bridge: composes `lookup-on-collected` with
-- `attachWithMaybe-clearVds-on-singletonFromVds` to prove that attaching
-- a cleared signal against the cross-message collection recovers the
-- original.  Mirrors E.6's `attachToSignal-on-collected`, but the input
-- signal is `clearVds s` instead of `s`.
attachToSignal-clearVds-on-collected :
    ∀ (msgs : List DBCMessage) (m : DBCMessage) (s : DBCSignal)
  → m ∈ msgs
  → s ∈ DBCMessage.signals m
  → AllPairs _≢_ (map DBCMessage.id msgs)
  → All MessageWF msgs
  → attachToSignal (collectFromMessages msgs) (DBCMessage.id m) (clearVds s) ≡ s
attachToSignal-clearVds-on-collected msgs m s m∈ s∈sigs msg-uniq all-wfs =
  trans
    (cong (attachWithMaybe (clearVds s))
      (lookup-on-collected msgs m s m∈ s∈sigs msg-uniq
        (MessageWF.sig-names-unique (All.lookup all-wfs m∈))))
    (attachWithMaybe-clearVds-on-singletonFromVds (DBCMessage.id m) s
       (DBCSignal.valueDescriptions s) refl)

-- Per-message bridge: applying attachToMessage to (clearVdsMsg m)
-- against the cross-message collection recovers the original `m`.
-- Same shape as E.6's `attachToMessage-on-collected`, with the input
-- message's signals cleared and `map-≡-id` operating over the cleared
-- signal list under a per-element lemma that collapses `clearVds s` back
-- to `s`.  Note: `clearVdsMsg m` only modifies the `signals` field, so
-- `(clearVdsMsg m).id ≡ m.id` definitionally.
attachToMessage-clearVdsMsg-on-collected :
    ∀ (msgs : List DBCMessage) (m : DBCMessage)
  → m ∈ msgs
  → AllPairs _≢_ (map DBCMessage.id msgs)
  → All MessageWF msgs
  → attachToMessage (collectFromMessages msgs) (clearVdsMsg m) ≡ m
attachToMessage-clearVdsMsg-on-collected msgs m m∈ msg-uniq all-wfs =
  trans
    (cong (λ ss → record m { signals = ss })
      (trans
        (map-map-fusion-clearVds (DBCMessage.signals m)
                                  (DBCMessage.id m)
                                  (collectFromMessages msgs))
        (map-≡-id (DBCMessage.signals m)
          (λ s → attachToSignal (collectFromMessages msgs) (DBCMessage.id m) (clearVds s))
          (λ s s∈sigs →
            attachToSignal-clearVds-on-collected msgs m s m∈ s∈sigs
              msg-uniq all-wfs))))
    record-η-signals
  where
    record-η-signals : record m { signals = DBCMessage.signals m } ≡ m
    record-η-signals = refl

    -- map (attachToSignal rvds m.id) (map clearVds sigs)
    -- ≡ map (λ s → attachToSignal rvds m.id (clearVds s)) sigs
    map-map-fusion-clearVds :
        ∀ (sigs : List DBCSignal) (cid : CANId) (rvds : List RawValueDesc)
      → map (attachToSignal rvds cid) (map clearVds sigs)
        ≡ map (λ s → attachToSignal rvds cid (clearVds s)) sigs
    map-map-fusion-clearVds []       _   _    = refl
    map-map-fusion-clearVds (s ∷ ss) cid rvds =
      cong (attachToSignal rvds cid (clearVds s) ∷_)
           (map-map-fusion-clearVds ss cid rvds)

-- List-level bridge — the universal target that Universal.agda calls.
-- Composes `attachToMessage-clearVdsMsg-on-collected` pointwise via
-- `map-≡-id`.  Mirrors E.6's `attachValueDescs-on-collectFromMessages`,
-- with the input messages-list cleared.
attachValueDescs-on-clearVdsMsgs-collectFromMessages :
    ∀ (msgs : List DBCMessage)
  → AllPairs _≢_ (map DBCMessage.id msgs)
  → All MessageWF msgs
  → attachValueDescs (collectFromMessages msgs) (map clearVdsMsg msgs) ≡ msgs
attachValueDescs-on-clearVdsMsgs-collectFromMessages msgs msg-uniq all-wfs =
  trans
    (map-map-fusion-clearVdsMsg msgs (collectFromMessages msgs))
    (map-≡-id msgs
      (λ m → attachToMessage (collectFromMessages msgs) (clearVdsMsg m))
      (λ m m∈ → attachToMessage-clearVdsMsg-on-collected msgs m m∈ msg-uniq all-wfs))
  where
    -- map (attachToMessage rvds) (map clearVdsMsg msgs)
    -- ≡ map (λ m → attachToMessage rvds (clearVdsMsg m)) msgs
    map-map-fusion-clearVdsMsg :
        ∀ (ms : List DBCMessage) (rvds : List RawValueDesc)
      → map (attachToMessage rvds) (map clearVdsMsg ms)
        ≡ map (λ m → attachToMessage rvds (clearVdsMsg m)) ms
    map-map-fusion-clearVdsMsg []       _    = refl
    map-map-fusion-clearVdsMsg (m ∷ ms) rvds =
      cong (attachToMessage rvds (clearVdsMsg m) ∷_)
           (map-map-fusion-clearVdsMsg ms rvds)

-- Unfolded form mirroring `map-attachToMessage-on-collected` (E.6)
-- — the goal in `Universal.finalizeParse-on-mkResult-clean` is in
-- this shape because `buildDBC` reduces `attachValueDescs` to `map`.
map-attachToMessage-on-clearVdsMsgs-collected :
    ∀ (msgs : List DBCMessage)
  → AllPairs _≢_ (map DBCMessage.id msgs)
  → All MessageWF msgs
  → map (attachToMessage (collectFromMessages msgs)) (map clearVdsMsg msgs) ≡ msgs
map-attachToMessage-on-clearVdsMsgs-collected =
  attachValueDescs-on-clearVdsMsgs-collectFromMessages

-- ============================================================================
-- E.9a — All RawValueDescStop (collectFromMessages msgs)
-- ============================================================================
--
-- Discharges the TVD chunk's `All RawValueDescStop` precondition without
-- requiring `vds-empty` (E.7's interim clause).  Every rvd in
-- `collectFromMessages msgs` has signalName equal to some `s.name` for
-- `s ∈ m.signals`, `m ∈ msgs`.  `Identifier.valid` provides
-- `T (validIdentifierᵇ name)` which decomposes via `T-∧→×` to a head
-- non-isHSpace witness — exactly `RawValueDescNameStop`.
--
-- Re-uses the existing `identifier-name-stop : ∀ (n : Identifier) →
-- IdentNameStop n` from `Aggregator.Dispatcher.Attribute.Foundations`.
-- `IdentNameStop` and `RawValueDescNameStop` reduce to the same Σ-type;
-- the coercion is `refl` at the value level (we just rename the carrier).

ident-name-as-vd-name-stop :
    ∀ (n : Identifier) → RawValueDescNameStop n
ident-name-as-vd-name-stop n = identifier-name-stop n

prependVdsRvd-stops :
    ∀ (cid : CANId) (name : Identifier) (vds : List (ℕ × List Char))
      (rest : List RawValueDesc)
  → All RawValueDescStop rest
  → All RawValueDescStop (prependVdsRvd cid name vds rest)
prependVdsRvd-stops _   _    []        _    rest-stops = rest-stops
prependVdsRvd-stops _   name (_ ∷ _)   _    rest-stops =
  ident-name-as-vd-name-stop name ∷ rest-stops

collectFromSignals-stops :
    ∀ (cid : CANId) (sigs : List DBCSignal)
  → All RawValueDescStop (collectFromSignals cid sigs)
collectFromSignals-stops _   []       = []
collectFromSignals-stops cid (s ∷ ss) =
  prependVdsRvd-stops cid (DBCSignal.name s) (DBCSignal.valueDescriptions s)
                      (collectFromSignals cid ss)
                      (collectFromSignals-stops cid ss)

-- All-++ for `RawValueDescStop`-shaped All.  Stdlib's `All-++` is
-- general but adds an import; this local form keeps the proof leaf-
-- close and reuses the existing all-++-canId-≢ pattern.
private
  All-stops-++ :
      ∀ (xs ys : List RawValueDesc)
    → All RawValueDescStop xs
    → All RawValueDescStop ys
    → All RawValueDescStop (xs ++ₗ ys)
  All-stops-++ []        ys []          ays = ays
  All-stops-++ (_  ∷ xs) ys (px ∷ pxs)  ays =
    px ∷ All-stops-++ xs ys pxs ays

collectFromMessages-stops :
    ∀ (msgs : List DBCMessage)
  → All RawValueDescStop (collectFromMessages msgs)
collectFromMessages-stops []       = []
collectFromMessages-stops (m ∷ ms) =
  All-stops-++ (collectFromMessage m) (collectFromMessages ms)
    (collectFromSignals-stops (DBCMessage.id m) (DBCMessage.signals m))
    (collectFromMessages-stops ms)


-- ============================================================================
-- E.8 (Plan B) — `unresolvedRVDs ∘ collectFromMessages ≡ []` inverse-bridge
-- ============================================================================
--
-- The structural sibling of `attachValueDescs-on-collectFromMessages`
-- (Layer 4 above): every entry in `collectFromMessages msgs` resolves
-- against `msgs` (because it was extracted from one of `msgs`), so
-- `unresolvedRVDs (collectFromMessages msgs) msgs ≡ []`.
--
-- Layered structure:
--   1. `resolvesᵇ-msgs-cons-mono` — `resolvesᵇ-msgs` is monotone
--      (cons-direction) in the messages list.
--   2. `matchesSigᵇ-self` — name match → `matchesSigᵇ` returns `true`.
--   3. `any-matchesSigᵇ-from-∈` — sig in sigs (with name match) → `any`
--      returns `true`.
--   4. `matchesMsgᵇ-mkRawValueDesc` — for an rvd built from `(msg.id,
--      s.name, vds)` with `s ∈ msg.signals`, `matchesMsgᵇ rvd msg ≡ true`.
--   5. `collectFromSignals-matchesMsgᵇ` — every rvd from `collectFromSignals
--      msg.id sigs` (with `sigs ⊆ msg.signals`) satisfies `matchesMsgᵇ rvd
--      msg ≡ true`.
--   6. `matchesMsgᵇ-cons-here` — `matchesMsgᵇ rvd m ≡ true` lifts to
--      `resolvesᵇ-msgs rvd (m ∷ ms) ≡ true`.
--   7. `collectFromMessages-resolvesAll` — every rvd in `collectFromMessages
--      msgs` satisfies `resolvesᵇ-msgs rvd msgs ≡ true`.
--   8. `unresolvedRVDs-respects` — `unresolvedRVDs` returns `[]` on
--      lists where every entry resolves.
--   9. `unresolvedRVDs-on-collectFromMessages` — combine.
--
-- No WF preconditions needed.  This holds for any `msgs`, including
-- non-unique cases — both attach and resolve operate via `lookup-vd`-style
-- first-match semantics, but the "did this rvd resolve at all" question
-- is monotone under duplicates.

open import Data.Bool using (_∨_; _∧_)
open import Data.Bool.Properties using (∨-zeroʳ)
open import Data.Bool.ListAction using (any)


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
