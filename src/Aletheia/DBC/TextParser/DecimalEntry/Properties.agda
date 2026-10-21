-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Correctness of `parseDecimal-chars`, the FFI's decimal→rational entry.
--
-- Soundness: a `WireRational` is answered only for a text the grammar
-- consumed whole, denoting a `DecRat` within the magnitude bound, and its
-- components are that `DecRat`'s numerator and denominator (which are the
-- components of the `ℚ` the kernel computes from it).  A failed parse, a
-- partial parse and a value past the bound each answer their typed error.
--
-- Completeness: the parser recovers every in-bound `DecRat` from the
-- kernel's own canonical decimal text, and every in-bound integer from its
-- plain printed form.  Both are corollaries of the suffix-aware roundtrips
-- in `…DecRatParse.Properties.Phase6Suffix` at `suffix ≡ []`.
--
-- The statements are at `List Char` level.  A `String`-level statement
-- would pull in the `toList∘fromList` substrate axiom (`Substrate.Unsafe`)
-- for no added assurance: `Data.String.toList` is total and `--safe`.
module Aletheia.DBC.TextParser.DecimalEntry.Properties where

open import Data.Bool using (true; false)
open import Data.Empty using (⊥-elim)
open import Data.Integer using (+_; -[1+_])
open import Data.Char using (Char)
open import Data.List using (List; []; _∷_)
open import Data.List.Properties using (++-identityʳ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _≤_; _≤ᵇ_; _*_; _^_)
open import Data.Nat.Properties using (≤ᵇ-reflects-≤; suc-pred)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Rational.Base using (ℚ)
open import Data.String using (String)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Reflects using (ofʸ; ofⁿ)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; sym; trans)

open import Aletheia.Parser.Combinators
  using (ParseResult; mkResult; value; position; remaining; runParserPartial; initialPosition)
open import Aletheia.Parser.Position using (Position; advancePositions)
open import Aletheia.Parser.Watermark using (Watermark; Refusal; mark; at)
open import Aletheia.DBC.TextParser.DecRatParse using (parseDecRat)
open import Aletheia.DBC.TextParser.DecRatParse.Properties.Phase2Many using ([]-stop)
open import Aletheia.DBC.TextParser.DecRatParse.Properties.Phase6Suffix using
  (parseDecRat-roundtrip-suffix; parseDecRat-bareInt-roundtrip-suffix)
open import Aletheia.DBC.TextFormatter.Emitter using (showDecRat-dec-chars; showInt-chars)
open import Aletheia.DBC.DecRat using (DecRat; mkDecRat; toℚ; fromℤ; 2^a·5^b-NonZero)
open import Aletheia.DBC.DecRat.Magnitude using (SmallDecRat; SmallInt; largerComponent; fromℤ-small)
open import Aletheia.DBC.Bounds using ([_]; bound)
open import Aletheia.Limits using
  (BoundKind; RationalComponentMagnitude; max-rational-component-magnitude)
open import Aletheia.Error using
  (Error; ParseFailure; TrailingInput; DBCTextParseErr; InputBoundExceededAt; InPart)
open import Aletheia.DBC.TextParser.Consumed using (consumed; refusalError)
open import Aletheia.DBC.TextParser.DecimalEntry using
  (WireRational; wireOf; fromChecked; decide; parseDecimal-chars)
open WireRational using (numerator; denominator)

-- ============================================================================
-- THE WHOLE-TEXT OUTCOME
-- ============================================================================

-- A failed parse with nothing refused is a failure at the watermark.
consumed-fail : ∀ {A : Set} (w : Position) → consumed {A} (at w) nothing ≡ inj₁ (DBCTextParseErr (ParseFailure w))
consumed-fail _ = refl

-- A stop with nothing refused is trailing input from the watermark.
consumed-trailing : ∀ {A : Set} (w : Position) (res : ParseResult A) {c cs} →
  remaining res ≡ c ∷ cs → consumed (at w) (just res) ≡ inj₁ (DBCTextParseErr (TrailingInput w (position res)))
consumed-trailing _ (mkResult _ _ (_ ∷ _)) refl = refl

-- A refusal on the watermark answers a failed run and a stopped one alike.
consumed-refused : ∀ {A : Set} (w : Position) (r : Refusal) (m : Maybe (ParseResult A)) →
  (∀ res → m ≡ just res → Σ[ c ∈ Char ] Σ[ cs ∈ List Char ] remaining res ≡ c ∷ cs) →
  consumed (mark w (just r)) m ≡ inj₁ (refusalError r)
consumed-refused _ _ nothing _ = refl
consumed-refused _ _ (just res@(mkResult _ _ (_ ∷ _))) _ = refl
consumed-refused _ _ (just res@(mkResult _ _ [])) stop with stop res refl
... | _ , _ , ()

consumed-whole : ∀ {A : Set} (w : Watermark) (res : ParseResult A) →
  remaining res ≡ [] → consumed w (just res) ≡ inj₂ res
consumed-whole _ (mkResult _ _ []) refl = refl

-- A consumed result is the parser's own, with nothing left.
consumed-inj₂ : ∀ {A : Set} (w : Watermark) (m : Maybe (ParseResult A)) (res : ParseResult A) →
  consumed w m ≡ inj₂ res → m ≡ just res × remaining res ≡ []
consumed-inj₂ _                 (just (mkResult _ _ []))      _ refl = refl , refl
consumed-inj₂ (mark _ nothing)  (just (mkResult _ _ (_ ∷ _))) _ ()
consumed-inj₂ (mark _ (just _)) (just (mkResult _ _ (_ ∷ _))) _ ()
consumed-inj₂ (mark _ nothing)  nothing                       _ ()
consumed-inj₂ (mark _ (just _)) nothing                       _ ()

-- ============================================================================
-- THE BOUND'S VERDICT
-- ============================================================================

bound-holds : ∀ (k : BoundKind) (tag : String) (n limit : ℕ) → n ≤ limit →
  Σ[ q ∈ n ≤ limit ] bound k tag n limit ≡ inj₂ [ q ]
bound-holds k tag n limit n≤limit with n ≤ᵇ limit | ≤ᵇ-reflects-≤ n limit
... | true  | ofʸ q  = q , refl
... | false | ofⁿ ¬q = ⊥-elim (¬q n≤limit)

bound-fails : ∀ (k : BoundKind) (tag : String) (n limit : ℕ) → ¬ (n ≤ limit) →
  bound k tag n limit ≡ inj₁ (InputBoundExceededAt (InPart tag) k n limit)
bound-fails k tag n limit ¬n≤limit with n ≤ᵇ limit | ≤ᵇ-reflects-≤ n limit
... | true  | ofʸ q = ⊥-elim (¬n≤limit q)
... | false | ofⁿ _ = refl

bound-inj₂ : ∀ (k : BoundKind) (tag : String) (n limit : ℕ) (x : _) →
  bound k tag n limit ≡ inj₂ x → n ≤ limit
bound-inj₂ k tag n limit x eq with n ≤ᵇ limit | ≤ᵇ-reflects-≤ n limit
... | true  | ofʸ q = q

-- The components `wireOf` writes.
Components : WireRational → DecRat → Set
Components w d =
  numerator w ≡ DecRat.numerator d × denominator w ≡ 2 ^ DecRat.twoExp d * 5 ^ DecRat.fiveExp d

-- Those components are the ones of the rational the kernel computes from
-- the DecRat: `toℚ` keeps the numerator and writes the denominator as a
-- predecessor, which `suc` undoes since 2^a·5^b is never zero.
toℚ-components : ∀ (d : DecRat) →
  ℚ.numerator (toℚ d) ≡ DecRat.numerator d
    × ℚ.denominatorℕ (toℚ d) ≡ 2 ^ DecRat.twoExp d * 5 ^ DecRat.fiveExp d
toℚ-components (mkDecRat num a b _) = refl , suc-pred (2 ^ a * 5 ^ b) ⦃ 2^a·5^b-NonZero a b ⦄

decide-small : ∀ (res : ParseResult DecRat) → SmallDecRat (value res) →
  Σ[ w ∈ WireRational ] (decide (inj₂ res) ≡ inj₂ w × Components w (value res))
decide-small res small with bound-holds RationalComponentMagnitude "decimal"
                                        (largerComponent (value res))
                                        max-rational-component-magnitude small
... | q , eq = wireOf (value res) q , cong (fromChecked (value res)) eq , refl , refl

decide-large : ∀ (res : ParseResult DecRat) → ¬ SmallDecRat (value res) →
  decide (inj₂ res) ≡ inj₁ (InputBoundExceededAt (InPart "decimal") RationalComponentMagnitude
                                                 (largerComponent (value res))
                                                 max-rational-component-magnitude)
decide-large res large =
  cong (fromChecked (value res))
       (bound-fails RationalComponentMagnitude "decimal" (largerComponent (value res))
                    max-rational-component-magnitude large)

decide-fail : ∀ (e : Error) → decide (inj₁ e) ≡ inj₁ e
decide-fail _ = refl

-- A `WireRational` is answered only for a consumed parse of an in-bound
-- `DecRat`, and carries that `DecRat`'s components.
decide-inj₂ : ∀ (o : Error ⊎ ParseResult DecRat) (w : WireRational) →
  decide o ≡ inj₂ w →
  Σ[ res ∈ ParseResult DecRat ] (o ≡ inj₂ res × SmallDecRat (value res) × Components w (value res))
decide-inj₂ (inj₂ res) w eq
  with bound RationalComponentMagnitude "decimal" (largerComponent (value res))
             max-rational-component-magnitude in beq
... | inj₂ [ _ ] with eq
...   | refl = res , refl
                  , bound-inj₂ RationalComponentMagnitude "decimal" (largerComponent (value res))
                               max-rational-component-magnitude _ beq
                  , refl , refl

-- ============================================================================
-- THE ENTRY, END TO END
-- ============================================================================

-- A `WireRational` answered for a text means the grammar consumed the
-- text whole into an in-bound `DecRat` with those components.
parseDecimal-chars-sound : ∀ cs (w : WireRational) → parseDecimal-chars cs ≡ inj₂ w →
  Σ[ res ∈ ParseResult DecRat ]
    ( proj₂ (runParserPartial parseDecRat cs) ≡ just res × remaining res ≡ []
    × SmallDecRat (value res) × Components w (value res) )
parseDecimal-chars-sound cs w eq
  with decide-inj₂ (consumed (proj₁ (runParserPartial parseDecRat cs))
                             (proj₂ (runParserPartial parseDecRat cs))) w eq
... | res , ceq , small , comps
  with consumed-inj₂ (proj₁ (runParserPartial parseDecRat cs))
                     (proj₂ (runParserPartial parseDecRat cs)) res ceq
...   | meq , rem = res , meq , rem , small , comps

-- The parser recovers every in-bound DecRat from its canonical decimal
-- text.
parseDecimal-chars-roundtrip : ∀ d → SmallDecRat d →
  Σ[ w ∈ WireRational ] (parseDecimal-chars (showDecRat-dec-chars d) ≡ inj₂ w × Components w d)
parseDecimal-chars-roundtrip d small
  with decide-small (mkResult d (advancePositions initialPosition (showDecRat-dec-chars d)) []) small
... | w , deq , comps =
  w , trans (cong (λ m → decide (consumed (proj₁ (runParserPartial parseDecRat (showDecRat-dec-chars d))) m))
                  parsed)
            deq
    , comps
  where
    parsed : proj₂ (runParserPartial parseDecRat (showDecRat-dec-chars d))
           ≡ just (mkResult d (advancePositions initialPosition (showDecRat-dec-chars d)) [])
    parsed = trans (cong (λ x → proj₂ (runParserPartial parseDecRat x))
                         (sym (++-identityʳ (showDecRat-dec-chars d))))
                   (parseDecRat-roundtrip-suffix d initialPosition [] small []-stop)

-- '.' ≢ '_' discharges the bare-int roundtrip's side condition at suffix ≡ []
-- (headOr [] '_' reduces to '_').
dot≢us : '.' ≢ '_'
dot≢us ()

fromℤ-numerator : ∀ z → DecRat.numerator (fromℤ z) ≡ z
fromℤ-numerator (+ zero)  = refl
fromℤ-numerator (+ suc _) = refl
fromℤ-numerator -[1+ _ ]  = refl

-- The parser also recovers an in-bound integer from its plain printed form,
-- the "42" a user types, which the DecRat emitter never produces ("42.0").
parseDecimal-chars-bareInt-roundtrip : ∀ z → SmallInt z →
  Σ[ w ∈ WireRational ]
    (parseDecimal-chars (showInt-chars z) ≡ inj₂ w × numerator w ≡ z × denominator w ≡ 1)
parseDecimal-chars-bareInt-roundtrip z small
  with decide-small (mkResult (fromℤ z) (advancePositions initialPosition (showInt-chars z)) [])
                    (fromℤ-small z small)
... | w , deq , num , den =
  w , trans (cong (λ m → decide (consumed (proj₁ (runParserPartial parseDecRat (showInt-chars z))) m))
                  parsed)
            deq
    , trans num (fromℤ-numerator z) , trans den (fromℤ-denominator z)
  where
    parsed : proj₂ (runParserPartial parseDecRat (showInt-chars z))
           ≡ just (mkResult (fromℤ z) (advancePositions initialPosition (showInt-chars z)) [])
    parsed = trans (cong (λ x → proj₂ (runParserPartial parseDecRat x))
                         (sym (++-identityʳ (showInt-chars z))))
                   (parseDecRat-bareInt-roundtrip-suffix z initialPosition [] small []-stop dot≢us)
    fromℤ-denominator : ∀ z → 2 ^ DecRat.twoExp (fromℤ z) * 5 ^ DecRat.fiveExp (fromℤ z) ≡ 1
    fromℤ-denominator (+ zero)  = refl
    fromℤ-denominator (+ suc _) = refl
    fromℤ-denominator -[1+ _ ]  = refl
