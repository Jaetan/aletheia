{-# OPTIONS --safe --no-main #-}

module Aletheia.Parser.Combinators where

open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.Char using (Char)
open import Data.Bool using (Bool; true; false; _∧_; _∨_; not)
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_)
open import Data.String as String using (String)
open import Function using (_∘_; id)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- Parser type: consumes a list of characters, returns result and remainder
-- Using fuel parameter for termination
Parser : Set → Set
Parser A = List Char → Maybe (A × List Char)

-- NOTE: Removed ParseResult record - we use plain pairs (A × List Char)
-- TODO: Phase 3 - Add better error reporting with position information

-- ============================================================================
-- BASIC COMBINATORS
-- ============================================================================

-- | Always succeeds with given value, consumes nothing
pure : ∀ {A : Set} → A → Parser A
pure x input = just (x , input)

-- | Always fails
fail : ∀ {A : Set} → Parser A
fail _ = nothing

-- | Monadic bind for parsers
_>>=_ : ∀ {A B : Set} → Parser A → (A → Parser B) → Parser B
(p >>= f) input with p input
... | nothing = nothing
... | just (x , rest) = f x rest

infixl 1 _>>=_

-- | Map over parser result (functor)
_<$>_ : ∀ {A B : Set} → (A → B) → Parser A → Parser B
(f <$> p) input with p input
... | nothing = nothing
... | just (x , rest) = just (f x , rest)

infixl 4 _<$>_

-- | Applicative: apply a parser of functions to a parser of values
_<*>_ : ∀ {A B : Set} → Parser (A → B) → Parser A → Parser B
(pf <*> px) input with pf input
... | nothing = nothing
... | just (f , rest) = (f <$> px) rest

infixl 4 _<*>_

-- | Sequence two parsers, keep only second result
_*>_ : ∀ {A B : Set} → Parser A → Parser B → Parser B
(p1 *> p2) = p1 >>= λ _ → p2

infixl 4 _*>_

-- | Sequence two parsers, keep only first result
_<*_ : ∀ {A B : Set} → Parser A → Parser B → Parser A
(p1 <* p2) = p1 >>= λ x → p2 >>= λ _ → pure x

infixl 4 _<*_

-- | Alternative: try first parser, if it fails, try second
_<|>_ : ∀ {A : Set} → Parser A → Parser A → Parser A
(p1 <|> p2) input with p1 input
... | just result = just result
... | nothing = p2 input

infixl 3 _<|>_

-- ============================================================================
-- CHARACTER PARSERS
-- ============================================================================

-- | Parse a single character satisfying predicate
satisfy : (Char → Bool) → Parser Char
satisfy pred [] = nothing
satisfy pred (c ∷ cs) with pred c
... | true = just (c , cs)
... | false = nothing

-- | Parse specific character
char : Char → Parser Char
char target = satisfy (λ c → c Data.Char.≈ᵇ target)
  where open import Data.Char using (_≈ᵇ_)

-- | Parse any character
anyChar : Parser Char
anyChar = satisfy (λ _ → true)

-- | Parse one of the given characters
oneOf : List Char → Parser Char
oneOf chars = satisfy (λ c → elem c chars)
  where
    elem : Char → List Char → Bool
    elem c [] = false
    elem c (x ∷ xs) with c Data.Char.≈ᵇ x
      where open import Data.Char using (_≈ᵇ_)
    ... | true = true
    ... | false = elem c xs

-- | Parse none of the given characters
noneOf : List Char → Parser Char
noneOf chars = satisfy (λ c → not (elem c chars))
  where
    elem : Char → List Char → Bool
    elem c [] = false
    elem c (x ∷ xs) with c Data.Char.≈ᵇ x
      where open import Data.Char using (_≈ᵇ_)
    ... | true = true
    ... | false = elem c xs

-- ============================================================================
-- REPETITION COMBINATORS (with fuel for termination)
-- ============================================================================

-- | Parse zero or more occurrences (with fuel for termination)
manyWithFuel : ∀ {A : Set} → ℕ → Parser A → Parser (List A)
manyWithFuel zero p = pure []
manyWithFuel (suc n) p =
  ((λ x xs → x ∷ xs) <$> p <*> manyWithFuel n p) <|> pure []

-- | Parse one or more occurrences
someWithFuel : ∀ {A : Set} → ℕ → Parser A → Parser (List A)
someWithFuel n p = (λ x xs → x ∷ xs) <$> p <*> manyWithFuel n p

-- Default fuel value (can be adjusted)
defaultFuel : ℕ
defaultFuel = 1000

-- Convenient aliases with default fuel
many : ∀ {A : Set} → Parser A → Parser (List A)
many = manyWithFuel defaultFuel

some : ∀ {A : Set} → Parser A → Parser (List A)
some = someWithFuel defaultFuel

-- | Parse exactly n occurrences
count : ∀ {A : Set} → ℕ → Parser A → Parser (List A)
count zero p = pure []
count (suc n) p = (λ x xs → x ∷ xs) <$> p <*> count n p

-- | Parse between min and max occurrences
countRange : ∀ {A : Set} → ℕ → ℕ → Parser A → Parser (List A)
countRange min max p = count min p >>= λ xs →
  manyWithFuel (max Data.Nat.∸ min) p >>= λ ys →
  pure (xs ++ ys)
  where open import Data.Nat using (_∸_)

-- ============================================================================
-- STRING PARSERS
-- ============================================================================

-- | Parse a specific string
string : String → Parser String
string s = parseChars (String.toList s) >>= λ _ → pure s
  where
    parseChars : List Char → Parser (List Char)
    parseChars [] = pure []
    parseChars (c ∷ cs) = char c >>= λ x →
                          parseChars cs >>= λ xs →
                          pure (x ∷ xs)

-- ============================================================================
-- COMMON CHARACTER CLASSES
-- ============================================================================

-- Helper: Convert Char to Nat for comparison using the actual stdlib function
private
  open import Data.Char.Base using (toℕ)

  charToNat : Char → ℕ
  charToNat = toℕ

-- | Check if character is a digit
isDigit : Char → Bool
isDigit c with charToNat c
... | n with charToNat '0' | charToNat '9'
... | n0 | n9 = (n0 Data.Nat.≤ᵇ n) ∧ (n Data.Nat.≤ᵇ n9)
  where open import Data.Nat using (_≤ᵇ_)

-- | Check if character is a lowercase letter
isLower : Char → Bool
isLower c with charToNat c
... | n with charToNat 'a' | charToNat 'z'
... | na | nz = (na Data.Nat.≤ᵇ n) ∧ (n Data.Nat.≤ᵇ nz)
  where open import Data.Nat using (_≤ᵇ_)

-- | Check if character is an uppercase letter
isUpper : Char → Bool
isUpper c with charToNat c
... | n with charToNat 'A' | charToNat 'Z'
... | nA | nZ = (nA Data.Nat.≤ᵇ n) ∧ (n Data.Nat.≤ᵇ nZ)
  where open import Data.Nat using (_≤ᵇ_)

-- | Check if character is a letter
isLetter : Char → Bool
isLetter c = isLower c ∨ isUpper c

-- | Check if character is alphanumeric
isAlphaNum : Char → Bool
isAlphaNum c = isLetter c ∨ isDigit c

-- | Check if character is whitespace
isSpace : Char → Bool
isSpace c = elem c (' ' ∷ '\t' ∷ '\n' ∷ '\r' ∷ [])
  where
    elem : Char → List Char → Bool
    elem c [] = false
    elem c (x ∷ xs) with c Data.Char.≈ᵇ x
      where open import Data.Char using (_≈ᵇ_)
    ... | true = true
    ... | false = elem c xs

-- ============================================================================
-- BASIC CHARACTER CLASS PARSERS
-- ============================================================================

-- | Parse a digit
digit : Parser Char
digit = satisfy isDigit

-- | Parse a letter
letter : Parser Char
letter = satisfy isLetter

-- | Parse alphanumeric character
alphaNum : Parser Char
alphaNum = satisfy isAlphaNum

-- | Parse whitespace character
space : Parser Char
space = satisfy isSpace

-- | Parse zero or more whitespace characters
spaces : Parser (List Char)
spaces = many space

-- | Parse one or more whitespace characters
spaces1 : Parser (List Char)
spaces1 = some space

-- ============================================================================
-- UTILITY COMBINATORS
-- ============================================================================

-- | Parse p between opening and closing parsers
between : ∀ {A B C : Set} → Parser A → Parser B → Parser C → Parser C
between opening closing p = opening *> p <* closing

-- | Parse p followed by separator one or more times
sepBy1 : ∀ {A B : Set} → Parser A → Parser B → Parser (List A)
sepBy1 p sep = (λ x xs → x ∷ xs) <$> p <*> many (sep *> p)

-- | Parse p followed by separator zero or more times
sepBy : ∀ {A B : Set} → Parser A → Parser B → Parser (List A)
sepBy p sep = sepBy1 p sep <|> pure []

-- | Skip whitespace then parse p
lexeme : ∀ {A : Set} → Parser A → Parser A
lexeme p = p <* spaces

-- | Parse a symbol (string) and skip trailing whitespace
symbol : String → Parser String
symbol s = lexeme (string s)

-- | Parse p enclosed in parentheses
parens : ∀ {A : Set} → Parser A → Parser A
parens p = between (symbol "(") (symbol ")") p

-- ============================================================================
-- HELPER FUNCTIONS
-- ============================================================================

-- | Run a parser on a string
parse : ∀ {A : Set} → Parser A → String → Maybe A
parse p s with p (String.toList s)
... | nothing = nothing
... | just (result , []) = just result
... | just (result , remaining) = nothing  -- Didn't consume all input

-- | Run a parser on a string, allow remaining input
parsePartial : ∀ {A : Set} → Parser A → String → Maybe (A × String)
parsePartial p s with p (String.toList s)
... | nothing = nothing
... | just (result , remaining) = just (result , String.fromList remaining)

-- TODO: Add more sophisticated error reporting with position information
-- TODO: Phase 5 - Replace fuel-based repetition with proper termination proof
