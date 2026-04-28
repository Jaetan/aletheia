{-# OPTIONS --safe --without-K #-}

-- DSL-emit ↔ existing-formatter bridge for the receivers chunk
-- (B.3.d Layer 3 Commit 3d.5.c-η).
--
-- Pre-ε.3 (3d.2): hosted a per-element induction (646 file-LOC /
-- 417 strict-code-LOC) directly verifying the receiver-list bind chain.
--
-- Post-ε.3 (3d.5.c-ε): `parseReceiverList` was a 3d.3-dispatcher-only
-- helper (`canonicalReceivers.list <$> parse canonicalReceiversFmt`)
-- with a slim flat `parseReceiverList-roundtrip` deriving from the
-- universal `Format.Receivers.Roundtrip.canonicalReceivers-roundtrip`.
--
-- Post-η (3d.5.c-η): the SG_ line is itself derived from
-- `Format.SignalLine.signalLineFmt`, so the dispatcher proofs use the
-- DSL emit directly.  `parseReceiverList` (and its roundtrip) are
-- gone; this module survives as the formatter-equivalence bridge.
--
-- Public exports:
--   * `emit-canonicalReceiversFmt-eq-emitReceivers` — DSL emit on an
--     arbitrary `CanonicalReceivers` ≡ `emitReceivers-chars` of its
--     `.list`.  Three shapes mirror `bwd`'s case-split.  No
--     no-Vector__XXX precondition needed (`bwd` does not case-split on
--     identifier shape).
--   * `isReceiverCont` (re-exported from
--     `Format.Receivers.Roundtrip`) — character predicate for the
--     receivers' SuffixStops precondition.
--
-- Private helpers (kept for the bridge):
--   * `emit-many-eq-foldr` — pointwise `concatMap`/`foldr` reconcile.
--   * `emit-eq-emitReceivers` (3d.2 carrier) — kept as a stepping
--     stone in case future Layer-4 message-level proofs want the
--     `mkCanonicalFromList rs` form.
--   * `mkCanonicalFromList-list-novecxxx` (3d.2 carrier) — same.
module Aletheia.DBC.TextParser.Properties.Topology.Receivers where

open import Data.Bool.Properties using (T?)
open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; foldr) renaming (_++_ to _++ₗ_)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong)
open import Relation.Nullary using (¬_; yes; no)

open import Aletheia.DBC.Identifier using
  (Identifier; ≡csᵇ-sound)
open import Aletheia.DBC.CanonicalReceivers
  using (CanonicalReceivers; mkCanonical;
         vectorXXX-name; isVectorXXXᵇ;
         mkCanonicalFromList)
open import Aletheia.DBC.TextFormatter.Topology using (emitReceivers-chars)
open import Aletheia.DBC.TextParser.Format
  using (emit; ident; many; withPrefix)
open import Aletheia.DBC.TextParser.Format.Receivers
  using (canonicalReceiversFmt)
open import Aletheia.DBC.TextParser.Format.Receivers.Roundtrip public
  using (isReceiverCont)

-- ============================================================================
-- DSL EMIT ≡ EXISTING FORMATTER (formatter-equivalence lemma)
-- ============================================================================

private
  -- Pointwise: the inner-many's emit on a list equals the formatter's
  -- foldr.  By induction on the list.
  emit-many-eq-foldr : ∀ (xs : List Identifier)
    → emit (many (withPrefix (',' ∷ []) ident)) xs
      ≡ foldr (λ x acc → ',' ∷ Identifier.name x ++ₗ acc) [] xs
  emit-many-eq-foldr []       = refl
  emit-many-eq-foldr (x ∷ xs) =
    cong (',' ∷_)
      (cong (Identifier.name x ++ₗ_) (emit-many-eq-foldr xs))

  -- The DSL's emit on `mkCanonicalFromList rs` produces the same chars as
  -- the existing `emitReceivers-chars rs`, under the no-Vector__XXX
  -- precondition.  Three shapes match the iso's `bwd`:
  --   * `[]`           — both sides emit "Vector__XXX".
  --   * `r ∷ []`       — under novecxxx, `T?` lands in `no`; emit reduces
  --                      to `name r`, formatter to `name r ++ []`.
  --   * `r ∷ s ∷ rest` — both sides flatten via the list-many fold.
  emit-eq-emitReceivers : ∀ (rs : List Identifier)
    → All (λ r → ¬ Identifier.name r ≡ vectorXXX-name) rs
    → emit canonicalReceiversFmt (mkCanonicalFromList rs)
      ≡ emitReceivers-chars rs
  emit-eq-emitReceivers []       _ = refl
  emit-eq-emitReceivers (r ∷ []) (¬eq ∷ _) with T? (isVectorXXXᵇ r)
  ... | yes p  = ⊥-elim (¬eq (≡csᵇ-sound (Identifier.name r) vectorXXX-name p))
  ... | no  _  = refl
  emit-eq-emitReceivers (r ∷ s ∷ rest) _ =
    cong (Identifier.name r ++ₗ_) (emit-many-eq-foldr (s ∷ rest))

-- ============================================================================
-- mkCanonicalFromList ON NO-VECTORXXX LISTS
-- ============================================================================

  -- Under novecxxx, `mkCanonicalFromList` is a section of `.list` —
  -- wrapping then projecting recovers the input.  Three shapes mirror
  -- the smart constructor's case structure.
  mkCanonicalFromList-list-novecxxx : ∀ (rs : List Identifier)
    → All (λ r → ¬ Identifier.name r ≡ vectorXXX-name) rs
    → CanonicalReceivers.list (mkCanonicalFromList rs) ≡ rs
  mkCanonicalFromList-list-novecxxx []       _ = refl
  mkCanonicalFromList-list-novecxxx (r ∷ []) (¬eq ∷ _) with T? (isVectorXXXᵇ r)
  ... | yes p = ⊥-elim (¬eq (≡csᵇ-sound (Identifier.name r) vectorXXX-name p))
  ... | no  _ = refl
  mkCanonicalFromList-list-novecxxx (_ ∷ _ ∷ _) _ = refl

-- ============================================================================
-- DSL EMIT ≡ EXISTING FORMATTER on arbitrary CanonicalReceivers
-- ============================================================================

-- Bridge feeding the signal-line formatter-equivalence proof.  Three
-- cases mirror `bwd`'s shape-based dispatch:
--   * `[]`         — emit prefixes `vectorXXX-id`'s name (= "Vector__XXX")
--                    then `concatMap _ []` reduces to `[]`; closes by
--                    definitional `_++_`-on-cons reduction of the
--                    11-char string against the empty tail.
--   * `r ∷ []`     — emit reduces to `name r ++ []`; formatter to
--                    `name r ++ foldr _ [] []` = `name r ++ []`.  refl.
--   * length≥2     — `cong` on `Identifier.name r ++_` + the inner
--                    `emit-many-eq-foldr` (private) pointwise reconciles
--                    `concatMap`/`foldr`.
--
-- No precondition needed: `bwd` does no case-split, so the equality is
-- unconditional (the receivers' canonical witness is unused on the
-- formatter side).
emit-canonicalReceiversFmt-eq-emitReceivers : ∀ (cr : CanonicalReceivers)
  → emit canonicalReceiversFmt cr
    ≡ emitReceivers-chars (CanonicalReceivers.list cr)
emit-canonicalReceiversFmt-eq-emitReceivers (mkCanonical [] _) = refl
emit-canonicalReceiversFmt-eq-emitReceivers (mkCanonical (r ∷ []) _) = refl
emit-canonicalReceiversFmt-eq-emitReceivers (mkCanonical (r ∷ s ∷ rest) _) =
  cong (Identifier.name r ++ₗ_) (emit-many-eq-foldr (s ∷ rest))

