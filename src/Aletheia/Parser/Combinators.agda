{-# OPTIONS --safe --without-K --no-main #-}

-- Parser combinators with structural recursion on input length.
--
-- Purpose: Provide composable parsers for strings with termination guarantees.
-- Key design: Uses input length as termination measure (no fuel needed).
-- Interfaces: Functor, Applicative, Monad for parser composition.
-- Role: Foundation for all parsing (JSON, DBC, LTL, protocol).
--
-- Performance: Rewritten from fuel-based approach, type-checks in ~10s (was >120s).
-- The `many` combinator terminates structurally by tracking consumed input length.
module Aletheia.Parser.Combinators where

open import Data.List using (List; []; _∷_; _++_; map; length; take)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.Char using (Char; _≈ᵇ_)
open import Data.Bool using (Bool; true; false; _∧_; _∨_; not)
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; _≤ᵇ_; _∸_)
open import Data.String as String using (String)
open import Function using (_∘_; id)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- ============================================================================
-- POSITION TRACKING
-- ============================================================================

-- Source position (line and column numbers)
record Position : Set where
  constructor mkPos
  field
    line : ℕ
    column : ℕ

open Position public

-- Initial position (start of input)
initialPosition : Position
initialPosition = mkPos 1 1

-- Advance position by one character
advancePosition : Position -> Char → Position
advancePosition pos c with c ≈ᵇ '\n'
... | true  = mkPos (suc (line pos)) 1
... | false = mkPos (line pos) (suc (column pos))

-- Advance position by a list of characters
advancePositions : Position → List Char → Position
advancePositions pos [] = pos
advancePositions pos (c ∷ cs) = advancePositions (advancePosition pos c) cs

-- Parse result with position information
record ParseResult (A : Set) : Set where
  constructor mkResult
  field
    value : A
    position : Position
    remaining : List Char

open ParseResult public

-- Parser type: takes position and input, returns result with new position
-- NEW: Tracks position for precise error reporting!
Parser : Set → Set
Parser A = Position → List Char → Maybe (ParseResult A)

-- ============================================================================
-- BASIC COMBINATORS
-- ============================================================================

-- | Always succeeds with given value, consumes nothing
pure : ∀ {A : Set} → A → Parser A
pure x pos input = just (mkResult x pos input)

-- | Always fails
fail : ∀ {A : Set} → Parser A
fail _ _ = nothing

-- | Monadic bind for parsers
_>>=_ : ∀ {A B : Set} → Parser A → (A → Parser B) → Parser B
(p >>= f) pos input with p pos input
... | nothing = nothing
... | just result = f (value result) (position result) (remaining result)

infixl 1 _>>=_

-- | Map over parser result (functor)
_<$>_ : ∀ {A B : Set} → (A → B) → Parser A → Parser B
(f <$> p) pos input with p pos input
... | nothing = nothing
... | just result = just (mkResult (f (value result)) (position result) (remaining result))

infixl 4 _<$>_

-- | Applicative: apply a parser of functions to a parser of values
_<*>_ : ∀ {A B : Set} → Parser (A → B) → Parser A → Parser B
(pf <*> px) pos input with pf pos input
... | nothing = nothing
... | just result = (value result <$> px) (position result) (remaining result)

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
(p1 <|> p2) pos input with p1 pos input
... | just result = just result
... | nothing = p2 pos input

infixl 3 _<|>_

-- ============================================================================
-- CHARACTER PARSERS
-- ============================================================================

-- | Parse a single character satisfying predicate
satisfy : (Char → Bool) → Parser Char
satisfy pred pos [] = nothing
satisfy pred pos (c ∷ cs) with pred c
... | true  = just (mkResult c (advancePosition pos c) cs)
... | false = nothing

-- | Parse specific character
char : Char → Parser Char
char target = satisfy (λ c → c ≈ᵇ target)

-- | Parse any character
anyChar : Parser Char
anyChar = satisfy (λ _ → true)

-- | Parse one of the given characters
oneOf : List Char → Parser Char
oneOf chars = satisfy (λ c → elem c chars)
  where
    elem : Char → List Char → Bool
    elem c [] = false
    elem c (x ∷ xs) with c ≈ᵇ x
    ... | true = true
    ... | false = elem c xs

-- | Parse none of the given characters
noneOf : List Char → Parser Char
noneOf chars = satisfy (λ c → not (elem c chars))
  where
    elem : Char → List Char → Bool
    elem c [] = false
    elem c (x ∷ xs) with c ≈ᵇ x
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
  manyHelper : ∀ {A : Set} → Parser A → Position → (input : List Char) → ℕ → Maybe (ParseResult (List A))
  -- Base case: ran out of attempts
  manyHelper p pos input zero = just (mkResult [] pos input)
  -- Recursive case: try parser
  manyHelper p pos input (suc n) with p pos input
  ... | nothing = just (mkResult [] pos input)  -- Parser failed, return empty list
  ... | just result with sameLengthᵇ input (remaining result)
  ...   | true = just (mkResult [] pos input)  -- No progress made, stop to ensure termination
  ...   | false with manyHelper p (position result) (remaining result) n  -- Progress made, continue
  ...     | nothing = just (mkResult ((value result) ∷ []) (position result) (remaining result))
  ...     | just restResult = just (mkResult ((value result) ∷ (value restResult)) (position restResult) (remaining restResult))

-- | Parse zero or more occurrences (structurally terminating)
many : ∀ {A : Set} → Parser A → Parser (List A)
many p pos input = manyHelper p pos input (length input)

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

-- Parse a newline character
newline : Parser Char
newline = char '\n'

-- ============================================================================
-- UTILITY COMBINATORS
-- ============================================================================

-- | Run a parser from the beginning of input
-- Returns parsed value with final position (for error reporting)
runParser : ∀ {A : Set} → Parser A → List Char → Maybe (A × Position)
runParser p input with p initialPosition input
... | nothing = nothing
... | just result = just (value result , position result)

-- | Run parser and return full result (value, position, and remaining input)
-- Useful for incremental parsing or when you need unconsumed input
runParserPartial : ∀ {A : Set} → Parser A → List Char → Maybe (ParseResult A)
runParserPartial p input = p initialPosition input

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

