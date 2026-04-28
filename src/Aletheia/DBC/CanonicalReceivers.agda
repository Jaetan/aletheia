{-# OPTIONS --safe --without-K #-}

-- B.3.d Layer 3 3d.5.c-γ.1 — Canonical receivers refinement type.
--
-- The DBC SG_ line carries a `receivers` field — a comma-separated list
-- of identifiers naming the nodes that consume the signal.  Cantools
-- emits the magic placeholder `Vector__XXX` when no node is named, so
-- the wire format always has at least one identifier.  The AST
-- normalises this:
--   * empty AST `[]`        ⇔ wire `Vector__XXX`
--   * singleton AST `[r]`   ⇔ wire `r` (where r ≠ Vector__XXX)
--   * length≥2 AST verbatim ⇔ wire verbatim (Vector__XXX preserved if
--                                            non-singleton — rare)
--
-- This module hosts the refinement carrier (`CanonicalReceivers`) and
-- the Bool predicate (`isCanonicalReceiversᵇ`) that asserts the AST
-- never contains the singleton-Vector__XXX placeholder.  Lives upstream
-- of `Types.agda` so the AST can reference it; the format DSL extension
-- in `TextParser.Format.Receivers` imports it for the iso lift.
--
-- Replaces the historical 4-site `All (¬ Identifier.name r ≡ "Vector__XXX")
-- (DBCSignal.receivers sig)` precondition pattern (see
-- `Properties/Topology/Signal.agda` 553/1709/1975/2222 and
-- `Formatter/WellFormedText.agda` 77) with a single type-level invariant.
module Aletheia.DBC.CanonicalReceivers where

open import Data.Bool using (Bool; true; false; T; not)
open import Data.Bool.Properties using (T?; T-irrelevant)
open import Data.Char using (Char)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
import Data.List.Properties as ListProps
open import Data.String using (toList)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong)
open import Relation.Nullary using (Dec; yes; no; ¬_)

open import Aletheia.DBC.Identifier
  using (Identifier; mkIdent; validIdentifierᵇ; _≡csᵇ_; ≡csᵇ-refl-eq;
         _≟ᴵ_)

-- ============================================================================
-- VECTOR__XXX MAGIC IDENTIFIER
-- ============================================================================

-- DBC's cantools placeholder for "no named receivers".  The DBC text
-- grammar requires at least one identifier in the receivers field, so
-- this literal is the wire encoding of the empty AST list.

vectorXXX-name : List Char
vectorXXX-name = toList "Vector__XXX"

-- The validity witness reduces definitionally: every char in
-- "Vector__XXX" satisfies `isIdentCont`, the leading 'V' satisfies
-- `isIdentStart`, so `validIdentifierᵇ vectorXXX-name` reduces to
-- `true` and `T true = ⊤`.
vectorXXX-id : Identifier
vectorXXX-id = mkIdent vectorXXX-name tt

-- ============================================================================
-- CANONICAL PREDICATE
-- ============================================================================

-- Bool fast-path equality of an Identifier's name against "Vector__XXX".
-- Soundness/completeness available via `≡csᵇ-sound` / `≡csᵇ-complete` /
-- `≡csᵇ-refl-eq` from `Identifier`.
isVectorXXXᵇ : Identifier → Bool
isVectorXXXᵇ r = Identifier.name r ≡csᵇ vectorXXX-name

-- Canonical receivers predicate.  `true` iff the list is one of:
--   * empty (encoded as "Vector__XXX" on wire),
--   * a singleton whose element is not Vector__XXX, or
--   * length ≥ 2 (regardless of contents — third-party tooling may
--     emit Vector__XXX as one of multiple, preserved verbatim).
isCanonicalReceiversᵇ : List Identifier → Bool
isCanonicalReceiversᵇ []          = true
isCanonicalReceiversᵇ (r ∷ [])    = not (isVectorXXXᵇ r)
isCanonicalReceiversᵇ (_ ∷ _ ∷ _) = true

-- ============================================================================
-- CANONICAL RECEIVERS RECORD
-- ============================================================================

-- Refinement carrier.  Mirrors `IntDecRat`/`NatDecRat` from
-- `DBC.DecRat.Refinement`: the value paired with a `T (predicateᵇ value)`
-- witness, made proof-relevant under `--safe` so MAlonzo doesn't strip it.
record CanonicalReceivers : Set where
  constructor mkCanonical
  field
    list      : List Identifier
    canonical : T (isCanonicalReceiversᵇ list)

-- ============================================================================
-- T/not LEMMAS — exported so Format.Receivers's iso bijection can use them
-- ============================================================================

-- `¬ T b` ⇒ `T (not b)`.  By case on the implicit `b`: if `b = true`,
-- `¬ T true = ¬ ⊤` is empty, contradicting any inhabitant; if `b = false`,
-- `T (not false) = ⊤` and `tt` discharges.
¬T→T-not : ∀ {b : Bool} → ¬ T b → T (not b)
¬T→T-not {true}  ¬t = ⊥-elim (¬t tt)
¬T→T-not {false} _  = tt

-- `T (not b)` and `T b` are mutually exclusive.  `b = true` makes
-- `T (not true) = ⊥`; `b = false` makes `T b = ⊥`.  Either way the
-- absurd pattern `()` discharges.
T-not-and-T : ∀ {b : Bool} → T (not b) → T b → ⊥
T-not-and-T {true}  ()
T-not-and-T {false} _ ()

-- ============================================================================
-- SMART CONSTRUCTOR — strip-and-witness from a raw list
-- ============================================================================

-- Build a `CanonicalReceivers` from any `List Identifier` by stripping
-- the singleton-`Vector__XXX` placeholder and synthesising the canonical
-- witness.  Total — every input list maps to exactly one canonical
-- output.  Subsumes the pre-γ.2 `stripVectorPlaceholder` in
-- `TextParser.Topology` (which produced an unwitnessed `List Identifier`);
-- post-ε.3, the unwitnessed strip helper is gone entirely and the DSL
-- iso `fwd = mkCanonicalFromList` absorbs the strip into
-- `parseReceiverList` directly.  Used by `parseSignalLine` and
-- `parseSignalFields` to construct receivers from the parsed raw input.
mkCanonicalFromList : List Identifier → CanonicalReceivers
mkCanonicalFromList []           = mkCanonical [] tt
mkCanonicalFromList (r ∷ []) with T? (isVectorXXXᵇ r)
... | yes _   = mkCanonical [] tt
... | no  ¬p  = mkCanonical (r ∷ []) (¬T→T-not ¬p)
mkCanonicalFromList (h ∷ s ∷ rest) = mkCanonical (h ∷ s ∷ rest) tt

-- ============================================================================
-- IDEMPOTENCY: mkCanonicalFromList ∘ list ≡ id
-- ============================================================================

-- Wrapping a canonical AST's underlying list back into a CanonicalReceivers
-- is the identity (up to witness irrelevance).  Used by JSON roundtrip
-- proofs and the γ.2 cascade — the JSON parser path strips the
-- refinement (`receiverIds : List Identifier`), then `mkCanonicalFromList`
-- re-wraps; this lemma closes the resulting `mkCanonicalFromList (.list r)
-- ≡ r` obligation in roundtrip proofs.
mkCanonicalFromList-list : ∀ (cr : CanonicalReceivers)
  → mkCanonicalFromList (CanonicalReceivers.list cr) ≡ cr
mkCanonicalFromList-list (mkCanonical [] _) = refl
mkCanonicalFromList-list (mkCanonical (r ∷ []) wit) with T? (isVectorXXXᵇ r)
... | yes p   = ⊥-elim (T-not-and-T wit p)
... | no  ¬p  = cong (mkCanonical (r ∷ []))
                     (T-irrelevant (¬T→T-not ¬p) wit)
mkCanonicalFromList-list (mkCanonical (r ∷ s ∷ rest) _) = refl

-- ============================================================================
-- DECIDABLE EQUALITY
-- ============================================================================

-- Two `CanonicalReceivers` are propositionally equal iff their `list`
-- char-list-of-identifiers fields are equal.  `T-irrelevant` collapses
-- the canonical-witness slot.  Used by `Properties.Equality` for
-- DBCSignal DecEq under γ.2's retyping.
_≟ᶜʳ_ : (cr₁ cr₂ : CanonicalReceivers) → Dec (cr₁ ≡ cr₂)
mkCanonical xs w₁ ≟ᶜʳ mkCanonical ys w₂ with ListProps.≡-dec _≟ᴵ_ xs ys
... | yes refl = yes (cong (mkCanonical xs) (T-irrelevant w₁ w₂))
... | no  ¬eq  = no λ { refl → ¬eq refl }
