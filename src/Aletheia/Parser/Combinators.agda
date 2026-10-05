-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K --no-main #-}

-- Parser combinators with structural recursion.
--
-- Purpose: Provide composable parsers for strings with termination guarantees.
-- Key design: repetition recurses structurally on the input list itself, its
-- length bounding the iterations (no fuel).
-- Interfaces: Functor, Applicative, Monad for parser composition.
-- Role: Foundation for all parsing (JSON, DBC, LTL, protocol).
module Aletheia.Parser.Combinators where

open import Data.List using (List; []; _∷_) renaming (_++_ to _++ₗ_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.Char using (Char; _≈ᵇ_)
open import Data.Char.Base using (isDigit; isAlpha; isSpace; isLower)
open import Data.Bool using (Bool; true; false; not)
open import Data.Bool.ListAction using (any)
open import Data.Nat using (ℕ; zero; suc; _∸_)
open import Data.String as String using (String)

-- ============================================================================
-- POSITION TRACKING
-- ============================================================================

-- Position lives in its own leaf module so non-parser consumers (the
-- error vocabulary, the response serializer) can import it without
-- joining this module's recheck closure. Re-exported here so existing
-- parser-side importers are unaffected.
open import Aletheia.Parser.Position public

-- Parse result with position information
record ParseResult (A : Set) : Set where
  constructor mkResult
  field
    value : A
    position : Position
    remaining : List Char

open ParseResult public

-- Parser type: takes position and input, returns the furthest position
-- reached during the attempt (the WATERMARK — first component) paired
-- with the outcome. The watermark is what makes failed parses report the
-- deepest point any branch reached (byte-exact error positions); the
-- outcome keeps the pre-watermark `Maybe (ParseResult A)` shape so
-- success-side reasoning composes through `proj₂` unchanged.
Parser : Set → Set
Parser A = Position → List Char → Position × Maybe (ParseResult A)

-- ============================================================================
-- BASIC COMBINATORS
-- ============================================================================

-- | Always succeeds with given value, consumes nothing
pure : ∀ {A : Set} → A → Parser A
pure x pos input = pos , just (mkResult x pos input)

-- | Always fails
fail : ∀ {A : Set} → Parser A
fail pos _ = pos , nothing

-- | Monadic bind for parsers
_>>=_ : ∀ {A B : Set} → Parser A → (A → Parser B) → Parser B
(p >>= f) pos input with p pos input
... | w , nothing = w , nothing
... | w , just result with f (value result) (position result) (remaining result)
...   | w' , out = maxₚ w w' , out

infixl 1 _>>=_

-- | Map over parser result (functor)
_<$>_ : ∀ {A B : Set} → (A → B) → Parser A → Parser B
(f <$> p) pos input with p pos input
... | w , nothing = w , nothing
... | w , just result = w , just (mkResult (f (value result)) (position result) (remaining result))

infixl 4 _<$>_

-- | Applicative: apply a parser of functions to a parser of values
_<*>_ : ∀ {A B : Set} → Parser (A → B) → Parser A → Parser B
(pf <*> px) pos input with pf pos input
... | w , nothing = w , nothing
... | w , just result with (value result <$> px) (position result) (remaining result)
...   | w' , out = maxₚ w w' , out

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
... | w , just result = w , just result
... | w , nothing with p2 pos input
...   | w' , out = maxₚ w w' , out

infixl 3 _<|>_

-- ============================================================================
-- CHARACTER PARSERS
-- ============================================================================

-- Helper: Check if character is in a list (Boolean membership test).
-- Delegates to stdlib's `Data.Bool.ListAction.any` (≡ `or ∘ map p`).
private
  elem : Char → List Char → Bool
  elem c = any (c ≈ᵇ_)

-- | Parse a single character satisfying predicate
satisfy : (Char → Bool) → Parser Char
satisfy pred pos [] = pos , nothing
satisfy pred pos (c ∷ cs) with pred c
-- The advanced position is both the success watermark (proj₁) and the
-- result position; bind it once (per-char hot path).  `let` is
-- definitional, so proofs matching this branch close by refl unchanged.
... | true  = let pos' = advancePosition pos c in pos' , just (mkResult c pos' cs)
... | false = pos , nothing

-- | Parse specific character
char : Char → Parser Char
char target = satisfy (λ c → c ≈ᵇ target)

-- | Parse any character
anyChar : Parser Char
anyChar = satisfy (λ _ → true)

-- | Parse one of the given characters
oneOf : List Char → Parser Char
oneOf chars = satisfy (λ c → elem c chars)

-- | Parse none of the given characters
noneOf : List Char → Parser Char
noneOf chars = satisfy (λ c → not (elem c chars))

-- ============================================================================
-- REPETITION COMBINATORS (structurally recursive on the input list)
-- ============================================================================

-- Helper for `many`.  It recurses structurally on its last argument, a list
-- whose length bounds the iterations: `many` passes the input itself, so
-- nothing is computed up front, and each iteration drops one element of it.
-- It stops when the element parser fails, or succeeds at the position it
-- started from, which means it consumed nothing (`samePosᵇ`); either check
-- costs the same whatever is left of the input.
-- Exposed (not private) so roundtrip proofs in `Aletheia.DBC.TextParser.*.Properties`
-- can pattern-match on its structure (see
-- `Aletheia.DBC.TextParser.DecRatParse.Properties.manyHelper-satisfy-exhaust`).
manyHelper : ∀ {A : Set} → Parser A → Position → (input : List Char) → List Char → Position × Maybe (ParseResult (List A))
-- Base case: ran out of attempts
manyHelper p pos input [] = pos , just (mkResult [] pos input)
-- Recursive case: try parser. A failed element parse is SWALLOWED (many
-- succeeds with the shorter list) but its watermark is KEPT — that depth
-- is exactly what the driver reports for the first unparseable statement.
manyHelper p pos input (_ ∷ bound) with p pos input
... | w , nothing = w , just (mkResult [] pos input)  -- Parser failed, return empty list
... | w , just result with samePosᵇ (position result) pos
...   | true = w , just (mkResult [] pos input)  -- No progress made, stop
...   | false with manyHelper p (position result) (remaining result) bound  -- Progress made, continue
...     | w' , nothing = maxₚ w w' , just (mkResult ((value result) ∷ []) (position result) (remaining result))
...     | w' , just restResult = maxₚ w w' , just (mkResult ((value result) ∷ (value restResult)) (position restResult) (remaining restResult))

-- | Parse zero or more occurrences (structurally terminating)
many : ∀ {A : Set} → Parser A → Parser (List A)
many p pos input = manyHelper p pos input input

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
  countUpTo (max ∸ min) p >>= λ ys →
  pure (xs ++ₗ ys)
  where
    -- Parse up to n occurrences (structurally recursive on n)
    countUpTo : ∀ {A : Set} → ℕ → Parser A → Parser (List A)
    countUpTo zero p = pure []
    countUpTo (suc n) p = ((λ x xs → x ∷ xs) <$> p <*> countUpTo n p) <|> pure []

-- ============================================================================
-- STRING PARSERS
-- ============================================================================

-- | Match an exact char list (helper for `string`).  Lifted from
-- `string`'s `where` clause so roundtrip proofs in
-- `Aletheia.DBC.TextParser.Properties.Primitives` can reason about
-- the internal recursion by name (`string-success` + `parseCharsSeq-
-- success`).  Behaviour preserved: `string s` still calls this on
-- `toList s` and discards the result.
parseCharsSeq : List Char → Parser (List Char)
parseCharsSeq []       = pure []
parseCharsSeq (c ∷ cs) = char c >>= λ x →
                         parseCharsSeq cs >>= λ xs →
                         pure (x ∷ xs)

-- | Parse a specific string
string : String → Parser String
string s = parseCharsSeq (String.toList s) >>= λ _ → pure s

-- ============================================================================
-- COMMON CHARACTER CLASSES
-- ============================================================================

-- Use stdlib character classification (isDigit, isAlpha, isSpace, isLower)
-- Character classifiers live in the CharClass leaf module (shared with
-- the DBC identifier vocabulary without pulling it into this module's
-- recheck closure); re-exported here for parser-side importers.
open import Aletheia.Parser.CharClass public

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
-- The watermark rides along so drivers can report byte-exact failure
-- positions (and, on partial success, the deepest swallowed failure).
runParser : ∀ {A : Set} → Parser A → List Char → Position × Maybe (A × Position)
runParser p input with p initialPosition input
... | w , nothing = w , nothing
... | w , just result = w , just (value result , position result)

-- | Run parser and return full result (value, position, and remaining input)
-- Useful for incremental parsing or when you need unconsumed input
runParserPartial : ∀ {A : Set} → Parser A → List Char → Position × Maybe (ParseResult A)
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

