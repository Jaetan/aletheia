{-# OPTIONS --safe --without-K #-}

-- B.3.d Layer 3 — 3d.5.a — Format DSL framework — regression test bank.
--
-- L1-L9 below were hand-written first and used to derive the universal
-- `roundtrip`.  Now reproved as one-liners delegating to `roundtrip`;
-- if the universal's shape drifts (signature, EmitsOK structure,
-- position arithmetic), these will fail to type-check and pinpoint the
-- regression.  Per advisor: "the strongest signal that the universal
-- genuinely subsumes the concrete cases."
--
-- Extracted from `Format.agda` (R22 continuation of R21 AGDA-D-15.1
-- closure) — 109 LOC pulled out to bring `Format.agda` under the
-- 800-LOC trigger.  Reachable from check-properties as an explicit
-- walk root (registered in `Shakefile.hs`).  The dependency direction
-- is one-way `RegressionTests → Format`; adding a re-export back into
-- `Format.agda` would close a cycle.
module Aletheia.DBC.TextParser.Format.RegressionTests where

open import Data.Bool using (Bool; T)
open import Data.Char.Base using (isDigit)
open import Data.List using ([]; _∷_) renaming (_++_ to _++ₗ_)
open import Data.Maybe using (just)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Aletheia.Parser.Combinators
  using (mkResult; advancePositions)
open import Aletheia.DBC.Identifier using (Identifier; isIdentCont)
open import Aletheia.DBC.DecRat using (DecRat)
open import Aletheia.DBC.TextParser.Lexer using (isHSpace)
open import Aletheia.DBC.TextFormatter.Emitter
  using (showNat-chars; showDecRat-dec-chars)
open import Aletheia.DBC.TextParser.DecRatParse.Properties using (SuffixStops)

open import Aletheia.DBC.TextParser.Format
  using (parse; literal; ident; nat; pair; refined; decRat; wsOpt; ws; altSum;
         roundtrip)

-- L1: literal-only.  Witness: `tt : ⊤`.
roundtrip-literal : ∀ pos cs suffix
  → parse (literal cs) pos (cs ++ₗ suffix)
    ≡ just (mkResult tt (advancePositions pos cs) suffix)
roundtrip-literal pos cs suffix = roundtrip (literal cs) pos tt suffix tt

-- L2: pair of two literals.  Witness: `(tt , tt) : ⊤ × ⊤`.
roundtrip-pair-literal-literal : ∀ pos cs ds suffix
  → parse (pair (literal cs) (literal ds)) pos
      ((cs ++ₗ ds) ++ₗ suffix)
    ≡ just (mkResult (tt , tt) (advancePositions pos (cs ++ₗ ds)) suffix)
roundtrip-pair-literal-literal pos cs ds suffix =
  roundtrip (pair (literal cs) (literal ds)) pos (tt , tt) suffix (tt , tt)

-- L3: literal-then-ident.  Witness: `(tt , ss) : ⊤ × SuffixStops isIdentCont suffix`.
roundtrip-pair-literal-ident : ∀ pos cs i suffix
  → SuffixStops isIdentCont suffix
  → parse (pair (literal cs) ident) pos
      ((cs ++ₗ Identifier.name i) ++ₗ suffix)
    ≡ just (mkResult (tt , i)
             (advancePositions pos (cs ++ₗ Identifier.name i))
             suffix)
roundtrip-pair-literal-ident pos cs i suffix ss =
  roundtrip (pair (literal cs) ident) pos (tt , i) suffix (tt , ss)

-- L4: ident-then-literal.  Witness: `(ss , tt)` where `ss` carries the
-- compatibility hypothesis on the head of `ds ++ suffix` (this is the
-- shape that, recurring with L3's outer-SuffixStops, drove the
-- generalisation to `EmitsOK`).
roundtrip-pair-ident-literal : ∀ pos i ds suffix
  → SuffixStops isIdentCont (ds ++ₗ suffix)
  → parse (pair ident (literal ds)) pos
      ((Identifier.name i ++ₗ ds) ++ₗ suffix)
    ≡ just (mkResult (i , tt)
             (advancePositions pos (Identifier.name i ++ₗ ds))
             suffix)
roundtrip-pair-ident-literal pos i ds suffix ss =
  roundtrip (pair ident (literal ds)) pos (i , tt) suffix (ss , tt)

-- L5: refined nat with arbitrary predicate `P : ℕ → Bool`.  Witness:
-- `(ss , wit)` where `ss : SuffixStops isDigit suffix` is the underlying
-- format's well-formedness, and `wit : T (P n)` is the refinement witness
-- supplied by the user.  Exercises the `refined` constructor's roundtrip
-- case end-to-end: parse runs nat, then `liftRefined` (decided via `T?`),
-- and the witness slot closes via `T-irrelevant`.  If `refined`'s
-- signature or `liftRefined-on-witness`'s shape drifts, this fails.
roundtrip-refined-nat : ∀ pos (P : ℕ → Bool) (n : ℕ) (wit : T (P n)) suffix
  → SuffixStops isDigit suffix
  → parse (refined P nat) pos (showNat-chars n ++ₗ suffix)
    ≡ just (mkResult (n , wit)
             (advancePositions pos (showNat-chars n))
             suffix)
roundtrip-refined-nat pos P n wit suffix ss =
  roundtrip (refined P nat) pos (n , wit) suffix ss

-- L6: altSum on the inj₁ branch — literal "X" lifted to `Format (⊤ ⊎ ℕ)`.
-- Tests the left-branch path through `<|>`: `parse f` succeeds first, so
-- `(inj₁ <$> parse f) <|> (inj₂ <$> parse g)` returns `inj₁ tt` directly
-- via `alt-left-just`.  No disjointness witness needed for the left case.
roundtrip-altSum-inj₁ : ∀ pos suffix
  → parse (altSum (literal ('X' ∷ [])) nat) pos
      (('X' ∷ []) ++ₗ suffix)
    ≡ just (mkResult (inj₁ tt)
             (advancePositions pos ('X' ∷ []))
             suffix)
roundtrip-altSum-inj₁ pos suffix =
  roundtrip (altSum (literal ('X' ∷ [])) nat) pos (inj₁ tt) suffix tt

-- L7: decRat — direct delegation through `roundtrip` to
-- `parseDecRat-roundtrip-suffix`.  Catches drift in the `decRat` clause
-- of either `emit`/`parse`/`EmitsOK`/`roundtrip`.
roundtrip-decRat : ∀ pos d suffix
  → SuffixStops isDigit suffix
  → parse decRat pos (showDecRat-dec-chars d ++ₗ suffix)
    ≡ just (mkResult d
             (advancePositions pos (showDecRat-dec-chars d))
             suffix)
roundtrip-decRat pos d suffix ss = roundtrip decRat pos d suffix ss

-- L8: wsOpt — canonical `[]` emit means input reduces to `suffix` and
-- output position to `pos`.  Catches `parseWSOpt`'s zero-consumption
-- composition through `bind-just-step`.
roundtrip-wsOpt : ∀ pos suffix
  → SuffixStops isHSpace suffix
  → parse wsOpt pos suffix
    ≡ just (mkResult tt pos suffix)
roundtrip-wsOpt pos suffix ss = roundtrip wsOpt pos tt suffix ss

-- L9: ws — canonical `' ' ∷ []` emit; output position is
-- `advancePosition pos ' '` (which `advancePositions pos (' ' ∷ [])`
-- reduces to definitionally).  Catches `parseWS-one-space` composition.
roundtrip-ws : ∀ pos suffix
  → SuffixStops isHSpace suffix
  → parse ws pos ((' ' ∷ []) ++ₗ suffix)
    ≡ just (mkResult tt
             (advancePositions pos (' ' ∷ []))
             suffix)
roundtrip-ws pos suffix ss = roundtrip ws pos tt suffix ss
