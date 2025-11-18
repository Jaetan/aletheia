{-# OPTIONS --safe --without-K #-}

module Aletheia.LTL.DSL.Parser where

open import Aletheia.LTL.DSL.Python
open import Aletheia.Parser.Combinators
open import Aletheia.DBC.Parser using (quotedString; identifier; natural; rational)
open import Data.List using (List; []; _∷_)
open import Data.String using (String; _==_; toList)
open import Data.Rational using (ℚ)
open import Data.Nat using (ℕ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Char using (Char)
open import Data.Bool using (if_then_else_)

-- ============================================================================
-- YAML KEY-VALUE PARSERS
-- ============================================================================

-- Parse a YAML key-value pair: "key: value"
keyValue : ∀ {A : Set} → String → Parser A → Parser A
keyValue expectedKey p =
  identifier >>= λ key →
  spaces *> char ':' *> spaces *>
  (if key == expectedKey
    then p
    else fail)

-- Parse just a key followed by colon (for nested structures)
key : String → Parser String
key expectedKey =
  identifier >>= λ k →
  spaces *> char ':' *> spaces *>
  (if k == expectedKey
    then pure k
    else fail)

-- Skip optional newlines and spaces
skipWS : Parser (List Char)
skipWS = many (satisfy isWSChar)
  where
    open import Data.Bool using (Bool; _∨_)
    open import Data.Char using (_≈ᵇ_)

    isWSChar : Char → Bool
    isWSChar c = (c ≈ᵇ ' ') ∨ (c ≈ᵇ '\n') ∨ (c ≈ᵇ '\r')

-- ============================================================================
-- COMPARISON OPERATOR PARSER
-- ============================================================================

parseCompOp : Parser ComparisonOp
parseCompOp =
  (string "LT" *> pure LT) <|>
  (string "GT" *> pure GT) <|>
  (string "LE" *> pure LE) <|>
  (string "GE" *> pure GE) <|>
  (string "EQ" *> pure EQ) <|>
  (string "NE" *> pure NE)

-- ============================================================================
-- EXPRESSION PARSERS (Phase 2A - Simple properties only)
-- ============================================================================

-- NOTE: For Phase 2A, we parse only simple LTL properties without nested
-- temporal operators. Complex properties (and, or, implies, until, not) are
-- DEFERRED to Phase 2B to avoid termination issues with mutual recursion.
--
-- This covers the majority of our 10 example automotive properties.

-- Parse PythonExpr from YAML
parsePythonExpr : Parser PythonExpr
parsePythonExpr =
  skipWS *>
  key "type" *>
  skipWS *>
  (identifier >>= λ exprType →
  skipWS *>
  (if exprType == "compare"
  then (keyValue "signal" identifier >>= λ sig →
        skipWS *>
        keyValue "op" parseCompOp >>= λ op →
        skipWS *>
        keyValue "value" rational >>= λ val →
        pure (Compare (Signal sig) op (Constant val)))
  else (if exprType == "between"
    then (keyValue "signal" identifier >>= λ sig →
          skipWS *>
          keyValue "min" rational >>= λ minVal →
          skipWS *>
          keyValue "max" rational >>= λ maxVal →
          pure (Between sig minVal maxVal))
    else (if exprType == "changed_by"
      then (keyValue "signal" identifier >>= λ sig →
            skipWS *>
            keyValue "delta" rational >>= λ delta →
            pure (ChangedBy sig delta))
      else (if exprType == "signal"
        then (keyValue "name" identifier >>= λ name →
              pure (Signal name))
        else (if exprType == "constant"
          then (keyValue "value" rational >>= λ val →
                pure (Constant val))
          else fail))))))

-- Parse PythonLTL from YAML (simple temporal operators only)
parsePythonLTL : Parser PythonLTL
parsePythonLTL =
  skipWS *>
  key "type" *>
  skipWS *>
  (identifier >>= λ ltlType →
  skipWS *>
  (if ltlType == "always"
  then (key "formula" *> skipWS *> parsePythonExpr >>= λ expr →
        pure (Always (Expr expr)))
  else (if ltlType == "eventually"
    then (key "formula" *> skipWS *> parsePythonExpr >>= λ expr →
          pure (Eventually (Expr expr)))
    else (if ltlType == "never"
      then (key "formula" *> skipWS *> parsePythonExpr >>= λ expr →
            pure (Never (Expr expr)))
      else (if ltlType == "eventually_within"
        then (keyValue "time_ms" natural >>= λ time →
              skipWS *>
              key "formula" *> skipWS *> parsePythonExpr >>= λ expr →
              pure (EventuallyWithin time (Expr expr)))
        else (if ltlType == "always_within"
          then (keyValue "time_ms" natural >>= λ time →
                skipWS *>
                key "formula" *> skipWS *> parsePythonExpr >>= λ expr →
                pure (AlwaysWithin time (Expr expr)))
          else fail))))))

-- ============================================================================
-- TOP-LEVEL PARSER
-- ============================================================================

-- Parse a complete YAML property specification
parseProperty : String → Maybe PythonLTL
parseProperty input with runParser parsePythonLTL (toList input)
... | just prop = just prop
... | nothing = nothing
