{-# OPTIONS --safe --without-K #-}

-- `parseReceiverList-roundtrip` — flat composed theorem for the 3d.3
-- dispatcher (B.3.d Layer 3 Commit 3d.2, post-ε.3 slim bridge).
--
-- Pre-ε.3, this module hosted a per-element induction (646 file-LOC /
-- 417 strict-code-LOC) directly verifying the bind chain:
--
--   parseIdentifier >>= λ h →
--   many (char ',' *> parseIdentifier) >>= λ t →
--   pure (h ∷ t)
--
-- Post-ε.3, `Topology.SignalLine.parseReceiverList` is derived from the
-- Format DSL (`canonicalReceivers.list <$> parse canonicalReceiversFmt`),
-- the strip step in `parseSignalLine` is subsumed into the DSL iso, and
-- the existential `(parsedRs, parse-eq, strip-eq)` from the pre-ε API
-- collapses to a single flat equality.  This module is a slim bridge
-- that derives `parseReceiverList-roundtrip` from the universal
-- `Format.Receivers.Roundtrip.canonicalReceivers-roundtrip`.
--
-- Two compactness lemmas earn the LOC reduction:
--   * `emit-eq-emitReceivers` — DSL emit ≡ existing formatter (list
--     induction, three shapes).
--   * `mkCanonicalFromList-list-novecxxx` — under the no-Vector__XXX
--     precondition, `list (mkCanonicalFromList rs) ≡ rs`.
--
-- The composed theorem is then a one-shot rewrite chain.
module Aletheia.DBC.TextParser.Properties.Topology.Receivers where

open import Data.Bool.Properties using (T?)
open import Data.Char using (Char)
open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; foldr) renaming (_++_ to _++ₗ_)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.Maybe using (just)
open import Data.String using (toList)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong)
open import Relation.Nullary using (¬_; yes; no)

open import Aletheia.Parser.Combinators
  using (Position; mkResult; advancePositions)
open import Aletheia.DBC.Identifier using
  (Identifier; ≡csᵇ-sound)
open import Aletheia.DBC.CanonicalReceivers
  using (CanonicalReceivers;
         vectorXXX-name; isVectorXXXᵇ;
         mkCanonicalFromList)
open import Aletheia.DBC.TextParser.Topology using (parseReceiverList)
open import Aletheia.DBC.TextFormatter.Topology using (emitReceivers-chars)
open import Aletheia.DBC.TextParser.DecRatParse.Properties
  using (SuffixStops)
open import Aletheia.DBC.TextParser.Format
  using (emit; ident; many; withPrefix)
open import Aletheia.DBC.TextParser.Format.Receivers
  using (canonicalReceiversFmt)
open import Aletheia.DBC.TextParser.Format.Receivers.Roundtrip public
  using (isReceiverCont)

open import Aletheia.DBC.TextParser.Format.Receivers.Roundtrip
  using (canonicalReceivers-roundtrip)

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
-- COMPOSED THEOREM (for 3d.3 dispatcher)
-- ============================================================================

-- Post-ε.3 flat signature.  With `parseReceiverList = list <$> parse
-- canonicalReceiversFmt`, the parsed-back list equals the input `rs`
-- directly (under novecxxx) — no per-element induction, and the strip
-- step in `parseSignalLine` is now subsumed into the DSL iso.
parseReceiverList-roundtrip :
    ∀ (pos : Position) (rs : List Identifier) (suffix : List Char)
  → All (λ r → ¬ Identifier.name r ≡ toList "Vector__XXX") rs
  → SuffixStops isReceiverCont suffix
  → parseReceiverList pos (emitReceivers-chars rs ++ₗ suffix)
    ≡ just (mkResult rs
                     (advancePositions pos (emitReceivers-chars rs))
                     suffix)
parseReceiverList-roundtrip pos rs suffix novecxxx ss
  rewrite sym (emit-eq-emitReceivers rs novecxxx)
        | canonicalReceivers-roundtrip pos (mkCanonicalFromList rs) suffix ss
        | mkCanonicalFromList-list-novecxxx rs novecxxx = refl
