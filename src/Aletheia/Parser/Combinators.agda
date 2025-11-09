{-# OPTIONS --safe --without-K #-}

module Aletheia.Parser.Combinators where

open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.Char using (Char; _≈ᵇ_)
open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; zero; suc)
open import Function using (_∘_)

-- | Parser type: consumes a list of characters, returns result and remainder
Parser : Set → Set
Parser A = List Char → Maybe (A × List Char)

-- | Always succeeds with given value
pure : ∀ {A : Set} → A → Parser A
pure x input = just (x , input)

-- | Monadic bind for parsers
_>>=_ : ∀ {A B : Set} → Parser A → (A → Parser B) → Parser B
(p >>= f) input with p input
... | nothing = nothing
... | just (x , rest) = f x rest

infixl 1 _>>=_

-- | Map over parser result
_<$>_ : ∀ {A B : Set} → (A → B) → Parser A → Parser B
(f <$> p) input with p input
... | nothing = nothing
... | just (x , rest) = just (f x , rest)

infixl 4 _<$>_

-- | Sequential composition
_<*>_ : ∀ {A B : Set} → Parser (A → B) → Parser A → Parser B
(pf <*> px) input with pf input
... | nothing = nothing
... | just (f , rest) = (f <$> px) rest

infixl 4 _<*>_

-- | Alternative: try first parser, if it fails, try second
_<|>_ : ∀ {A : Set} → Parser A → Parser A → Parser A
(p1 <|> p2) input with p1 input
... | just result = just result
... | nothing = p2 input

infixl 3 _<|>_

-- | Fail parser
fail : ∀ {A : Set} → Parser A
fail _ = nothing

-- | Parse a single character satisfying predicate
satisfy : (Char → Bool) → Parser Char
satisfy pred [] = nothing
satisfy pred (c ∷ cs) with pred c
... | true = just (c , cs)
... | false = nothing

-- | Parse specific character
char : Char → Parser Char
char target [] = nothing
char target (c ∷ cs) with c ≈ᵇ target
... | true = just (c , cs)
... | false = nothing

-- | Parse zero or more occurrences (with fuel for termination)
manyWithFuel : ∀ {A : Set} → ℕ → Parser A → Parser (List A)
manyWithFuel zero p = pure []
manyWithFuel (suc n) p = 
  ((λ x xs → x ∷ xs) <$> p <*> manyWithFuel n p) <|> pure []

-- | Parse one or more occurrences
someWithFuel : ∀ {A : Set} → ℕ → Parser A → Parser (List A)
someWithFuel n p = (λ x xs → x ∷ xs) <$> p <*> manyWithFuel n p
