{-# OPTIONS --safe --without-K #-}

-- Load-bearing reduction canary for the B.3.d Layer 3 `NS_` proof.
--
-- `Namespace.parseNSLine-keyword`'s validity precondition is discharged
-- via `nsKeywords-valid : All (T ∘ validIdentifierᵇ ∘ toList) nsKeywords`
-- using 25 `tt` witnesses.  That's only well-typed if
-- `validIdentifierᵇ (toList kw)` reduces to `true` on every literal
-- keyword string, so `T (...) = T true = ⊤` and `tt : ⊤` typechecks.
--
-- If stdlib `Data.Char.Base` ever changes the primitive-char
-- classification functions (`isAlpha`, `isAlphaNum`, `_≟_`) in a way
-- that blocks reduction on closed chars, this file would fail to
-- typecheck *before* `Namespace.agda` did, making the regression
-- much easier to diagnose.
module Aletheia.DBC.TextParser.Properties.Preamble._Scratch where

open import Data.Bool using (T)
open import Data.String using (toList)
open import Data.Unit using (tt)

open import Aletheia.DBC.Identifier using (validIdentifierᵇ)

_test-NSDescValid : T (validIdentifierᵇ (toList "NS_DESC_"))
_test-NSDescValid = tt

_test-SGMULVAL : T (validIdentifierᵇ (toList "SG_MUL_VAL_"))
_test-SGMULVAL = tt

_test-FILTER : T (validIdentifierᵇ (toList "FILTER"))
_test-FILTER = tt
