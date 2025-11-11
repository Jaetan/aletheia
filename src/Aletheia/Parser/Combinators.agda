{-# OPTIONS --safe --without-K --no-main #-}

module Aletheia.Parser.Combinators where

open import Data.List using (List; []; _∷_; _++_; map; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.Char using (Char)
open import Data.Bool using (Bool; true; false; _∧_; _∨_; not)
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; _≤ᵇ_)
open import Data.String as String using (String)
open import Function using (_∘_; id)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- Parser type: consumes a list of characters, returns result and remainder
-- NEW: Structurally recursive - no fuel needed!
Parser : Set → Set
Parser A = List Char → Maybe (A × List Char)

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
-- REPETITION COMBINATORS (structurally recursive on input length)
-- ============================================================================

-- NEW APPROACH: Make recursion structurally terminating by measuring progress
-- If a parser doesn't consume input, we stop to ensure termination

-- Helper: Check if two lists have the same length
sameLengthᵇ : ∀ {A : Set} → List A → List A → Bool
sameLengthᵇ [] [] = true
sameLengthᵇ (_ ∷ _) [] = false
sameLengthᵇ [] (_ ∷ _) = false
sameLengthᵇ (_ ∷ xs) (_ ∷ ys) = sameLengthᵇ xs ys

-- Helper for many: structurally recursive on input via well-founded recursion
-- Uses the length of the input as a measure
private
  manyHelper : ∀ {A : Set} → Parser A → (input : List Char) → ℕ → Maybe (List A × List Char)
  -- Base case: ran out of attempts
  manyHelper p input zero = just ([] , input)
  -- Recursive case: try parser
  manyHelper p input (suc n) with p input
  ... | nothing = just ([] , input)  -- Parser failed, return empty list
  ... | just (x , rest) with sameLengthᵇ input rest
  ...   | true = just ([] , input)  -- No progress made, stop to ensure termination
  ...   | false with manyHelper p rest n  -- Progress made, continue
  ...     | nothing = just ((x ∷ []) , rest)  -- Couldn't continue, return what we have
  ...     | just (xs , final) = just ((x ∷ xs) , final)

-- | Parse zero or more occurrences (structurally terminating)
many : ∀ {A : Set} → Parser A → Parser (List A)
many p input = manyHelper p input (length input)

-- | Parse one or more occurrences
some : ∀ {A : Set} → Parser A → Parser (List A)
some p = (λ x xs → x ∷ xs) <$> p <*> many p

-- | Parse exactly n occurrences
count : ∀ {A : Set} → ℕ → Parser A → Parser (List A)
count zero p = pure []
count (suc n) p = (λ x xs → x ∷ xs) <$> p <*> count n p

-- | Parse between min and max occurrences
countRange : ∀ {A : Set} → ℕ → ℕ → Parser A → Parser (List A)
countRange min max p = count min p >>= λ xs →
  countUpTo (max Data.Nat.∸ min) p >>= λ ys →
  pure (xs ++ ys)
  where
    open import Data.Nat using (_∸_)

    -- Parse up to n occurrences (structurally recursive on n)
    countUpTo : ∀ {A : Set} → ℕ → Parser A → Parser (List A)
    countUpTo zero p = pure []
    countUpTo (suc n) p = ((λ x xs → x ∷ xs) <$> p <*> countUpTo n p) <|> pure []

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

  -- Pre-computed character codes for efficiency
  code-0 : ℕ
  code-0 = 48  -- '0'

  code-9 : ℕ
  code-9 = 57  -- '9'

  code-A : ℕ
  code-A = 65  -- 'A'

  code-Z : ℕ
  code-Z = 90  -- 'Z'

  code-a : ℕ
  code-a = 97  -- 'a'

  code-z : ℕ
  code-z = 122  -- 'z'

-- | Check if character is a digit
isDigit : Char → Bool
isDigit c = let n = charToNat c
            in (code-0 ≤ᵇ n) ∧ (n ≤ᵇ code-9)

-- | Check if character is uppercase letter
isUpper : Char → Bool
isUpper c = let n = charToNat c
            in (code-A ≤ᵇ n) ∧ (n ≤ᵇ code-Z)

-- | Check if character is lowercase letter
isLower : Char → Bool
isLower c = let n = charToNat c
            in (code-a ≤ᵇ n) ∧ (n ≤ᵇ code-z)

-- | Check if character is a letter
isAlpha : Char → Bool
isAlpha c = isUpper c ∨ isLower c

-- | Check if character is alphanumeric
isAlphaNum : Char → Bool
isAlphaNum c = isAlpha c ∨ isDigit c

-- | Check if character is whitespace
isSpace : Char → Bool
isSpace c = (c Data.Char.≈ᵇ ' ') ∨ (c Data.Char.≈ᵇ '\t') ∨ (c Data.Char.≈ᵇ '\n') ∨ (c Data.Char.≈ᵇ '\r')
  where open import Data.Char using (_≈ᵇ_)

-- Parse a digit character
digit : Parser Char
digit = satisfy isDigit

-- Parse an uppercase letter
upper : Parser Char
upper = satisfy isUpper

-- Parse a lowercase letter
lower : Parser Char
lower = satisfy isLower

-- Parse any letter
letter : Parser Char
letter = satisfy isAlpha

-- Parse any alphanumeric character
alphaNum : Parser Char
alphaNum = satisfy isAlphaNum

-- Parse a whitespace character
space : Parser Char
space = satisfy isSpace

-- Parse zero or more whitespace characters
spaces : Parser (List Char)
spaces = many space

-- ============================================================================
-- UTILITY COMBINATORS
-- ============================================================================

-- | Run a parser and extract result, discarding remainder
runParser : ∀ {A : Set} → Parser A → List Char → Maybe A
runParser p input with p input
... | nothing = nothing
... | just (result , _) = just result

-- | Run parser partially, returning both result and remainder
runParserPartial : ∀ {A : Set} → Parser A → List Char → Maybe (A × List Char)
runParserPartial p input = p input

-- | Optional: parse A or return nothing if it fails
optional : ∀ {A : Set} → Parser A → Parser (Maybe A)
optional p = (just <$> p) <|> pure nothing

-- | Parse something between two delimiters
between : ∀ {A B C : Set} → Parser A → Parser B → Parser C → Parser C
between popen pclose p = popen *> p <* pclose

-- | Parse one or more occurrences separated by a separator
sepBy1 : ∀ {A B : Set} → Parser A → Parser B → Parser (List A)
sepBy1 p sep = (λ x xs → x ∷ xs) <$> p <*> many (sep *> p)

-- | Parse zero or more occurrences separated by a separator
sepBy : ∀ {A B : Set} → Parser A → Parser B → Parser (List A)
sepBy p sep = sepBy1 p sep <|> pure []

-- | Parse one or more occurrences ending with a separator
endBy1 : ∀ {A B : Set} → Parser A → Parser B → Parser (List A)
endBy1 p sep = some (p <* sep)

-- | Parse zero or more occurrences ending with a separator
endBy : ∀ {A B : Set} → Parser A → Parser B → Parser (List A)
endBy p sep = many (p <* sep)

-- | Parse items separated or ended by separator
sepEndBy : ∀ {A B : Set} → Parser A → Parser B → Parser (List A)
sepEndBy p sep = sepBy p sep <* optional sep

-- COMMENTED OUT: chainl1 and chainl have termination issues with the new approach
-- These combinators aren't used in the current codebase
-- Can be re-implemented with proper termination checking if needed

-- -- | Chain parsers with left-associative operator
-- chainl1 : ∀ {A : Set} → Parser A → Parser (A → A → A) → Parser A
-- chainl1 {A} p op = p >>= rest
--   where
--     rest : A → Parser A
--     rest x = (op >>= λ f → p >>= λ y → rest (f x y)) <|> pure x

-- -- | Chain parsers with left-associative operator, with default value
-- chainl : ∀ {A : Set} → Parser A → Parser (A → A → A) → A → Parser A
-- chainl p op x = chainl1 p op <|> pure x
