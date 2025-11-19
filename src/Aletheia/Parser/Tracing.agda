{-# OPTIONS --safe --without-K #-}

module Aletheia.Parser.Tracing where

open import Aletheia.Parser.Combinators using (Parser; Position; ParseResult; initialPosition)
open import Data.List using (List; []; _∷_; _++_; length; take; reverse)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.Char using (Char)
open import Data.String as String using (String; fromList)
open import Data.Nat using (ℕ; _+_; _∸_)
open import Data.Bool using (Bool; true; false; if_then_else_)

-- ============================================================================
-- TRACE EVENT TYPES
-- ============================================================================

-- | A trace event records what happened during parsing
data TraceEvent : Set where
  Enter    : String → ℕ → String → TraceEvent  -- Parser name, position, next 20 chars
  Exit     : String → ℕ → Bool → ℕ → TraceEvent  -- Parser name, position, success, chars consumed
  Message  : String → TraceEvent                 -- Custom message

-- | Result of parsing with trace information
record TracedResult (A : Set) : Set where
  constructor traced
  field
    result : Maybe (A × List Char)
    trace  : List TraceEvent

open TracedResult public

-- ============================================================================
-- TRACE UTILITIES
-- ============================================================================

-- | Simple nat to string using standard library
showNat : ℕ → String
showNat n = Data.Nat.Show.show n
  where
    open import Data.Nat.Show

-- | Format trace event as string for display
formatEvent : TraceEvent → String
formatEvent (Enter name pos preview) =
  "[" String.++ name String.++ "] @" String.++ showNat pos String.++
  " ← " String.++ preview
formatEvent (Exit name pos true consumed) =
  "[" String.++ name String.++ "] @" String.++ showNat pos String.++
  " ✓ consumed " String.++ showNat consumed
formatEvent (Exit name pos false _) =
  "[" String.++ name String.++ "] @" String.++ showNat pos String.++ " ✗ failed"
formatEvent (Message msg) =
  "  " String.++ msg

-- | Preview next N characters of input for trace
preview : ℕ → List Char → String
preview n cs =
  let chars = take n cs
      escaped = map escapeChar chars
  in fromList escaped
  where
    escapeChar : Char → Char
    escapeChar '\n' = '␤'  -- Visible newline
    escapeChar ' ' = '·'   -- Visible space
    escapeChar c = c

    map : {A B : Set} → (A → B) → List A → List B
    map f [] = []
    map f (x ∷ xs) = f x ∷ map f xs

-- ============================================================================
-- TRACING WRAPPERS
-- ============================================================================

-- | Wrap a parser to add tracing on entry/exit
-- Updated for Position-aware Parser type
traceParser : ∀ {A : Set} → String → Parser A → (ℕ → List Char → TracedResult A)
traceParser name p pos input =
  let previewStr = preview 20 input
      enterEvent = Enter name pos previewStr
      -- Call parser with initial position (we track our own pos for tracing)
      result = p initialPosition input
  in case result of λ where
    nothing →
      traced nothing (enterEvent ∷ Exit name pos false 0 ∷ [])
    (just parseResult) →
      let value = ParseResult.value parseResult
          rest = ParseResult.remaining parseResult
          consumed = length input ∸ length rest
          exitEvent = Exit name pos true consumed
      in traced (just (value , rest)) (enterEvent ∷ exitEvent ∷ [])
  where
    open import Data.Maybe using (Maybe; just; nothing)
    open import Relation.Binary.PropositionalEquality using (_≡_)

    case_of_ : ∀ {A B : Set} → A → (A → B) → B
    case x of f = f x

-- | Combine traces from sequential parsing
combineTraces : ∀ {A B : Set} → TracedResult A → (A → ℕ → List Char → TracedResult B) → TracedResult B
combineTraces {A} {B} res f =
  case result res of λ where
    nothing → traced nothing (trace res)
    (just (x , rest)) →
      let pos' = length (inputOf res) ∸ length rest
          res' = f x pos' rest
      in traced (result res') (trace res ++ trace res')
  where
    open import Data.Maybe using (Maybe; just; nothing)

    case_of_ : ∀ {A B : Set} → A → (A → B) → B
    case x of f = f x

    -- Recover input length from trace (approximation)
    inputOf : ∀ {A} → TracedResult A → List Char
    inputOf {A} r with result r
    ... | nothing = []
    ... | just (_ , rest) = rest  -- Approximation: use remaining input

-- | Add a custom message to trace
traceMessage : ∀ {A : Set} → String → TracedResult A → TracedResult A
traceMessage msg res =
  traced (result res) (trace res ++ (Message msg ∷ []))

-- | Pretty-print a trace for debugging
formatTrace : List TraceEvent → String
formatTrace events = String.concat (map formatWithNewline events)
  where
    formatWithNewline : TraceEvent → String
    formatWithNewline e = formatEvent e String.++ "\n"

    map : {A B : Set} → (A → B) → List A → List B
    map f [] = []
    map f (x ∷ xs) = f x ∷ map f xs

    -- Concatenate list of strings
    concat : List String → String
    concat [] = ""
    concat (s ∷ ss) = s String.++ concat ss

-- ============================================================================
-- CONVENIENCE FUNCTIONS
-- ============================================================================

-- | Run parser with tracing, return result and formatted trace
runWithTrace : ∀ {A : Set} → String → Parser A → List Char → Maybe A × String
runWithTrace name p input =
  let res = traceParser name p 0 input
  in (case result res of λ where
       nothing → nothing
       (just (x , _)) → just x) , formatTrace (trace res)
  where
    open import Data.Maybe using (Maybe; just; nothing)

    case_of_ : ∀ {A B : Set} → A → (A → B) → B
    case x of f = f x
