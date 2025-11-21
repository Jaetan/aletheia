{-# OPTIONS --safe --without-K --guardedness #-}

module Aletheia.LTL.DSL.Parser where

open import Aletheia.Prelude
open import Data.String using (_==_; toList)
open import Data.Nat using (_≤?_)
open import Data.Nat.Show using (show)

open import Aletheia.LTL.DSL.Yaml
open import Aletheia.LTL.DSL.Translate
open import Aletheia.LTL.Syntax using (LTL)
open import Aletheia.LTL.SignalPredicate using (SignalPredicate)
open import Aletheia.Parser.Combinators
open import Aletheia.DBC.Parser using (quotedString; identifier; natural; rational)

-- ============================================================================
-- YAML PRIMITIVES
-- ============================================================================

-- Skip whitespace
skipWS : Parser (List Char)
skipWS = many (satisfy isWSChar)
  where
    open import Data.Bool using (Bool; _∨_)
    open import Data.Char using (_≈ᵇ_)

    isWSChar : Char → Bool
    isWSChar c = (c ≈ᵇ ' ') ∨ (c ≈ᵇ '\n') ∨ (c ≈ᵇ '\r') ∨ (c ≈ᵇ '\t')

-- Parse "key: " prefix
parseKey : String → Parser String
parseKey expected =
  skipWS *> identifier >>= λ key →
  skipWS *> char ':' *> skipWS *>
  (if key == expected then pure key else fail)

-- ============================================================================
-- COMPARISON OPERATOR PARSER
-- ============================================================================

parseCompOpYaml : Parser CompOpYaml
parseCompOpYaml =
  (string "LT" *> pure LT-yaml) <|>
  (string "GT" *> pure GT-yaml) <|>
  (string "LE" *> pure LE-yaml) <|>
  (string "GE" *> pure GE-yaml) <|>
  (string "EQ" *> pure EQ-yaml) <|>
  (string "NE" *> pure NE-yaml)

-- ============================================================================
-- EXPRESSION PARSER (No recursion - all leaves)
-- ============================================================================

parseExprYaml : Parser ExprYaml
parseExprYaml =
  skipWS *> parseKey "type" >>= λ _ →
  identifier >>= λ exprType →
  skipWS *>
  (if exprType == "compare"
   then (parseKey "signal" *> identifier >>= λ sig →
         skipWS *>
         parseKey "op" *> parseCompOpYaml >>= λ op →
         skipWS *>
         parseKey "value" *> rational >>= λ val →
         pure (CompareYaml sig op val))
   else (if exprType == "between"
    then (parseKey "signal" *> identifier >>= λ sig →
          skipWS *>
          parseKey "min" *> rational >>= λ minV →
          skipWS *>
          parseKey "max" *> rational >>= λ maxV →
          pure (BetweenYaml sig minV maxV))
    else (if exprType == "changed_by"
     then (parseKey "signal" *> identifier >>= λ sig →
           skipWS *>
           parseKey "delta" *> rational >>= λ delta →
           pure (ChangedByYaml sig delta))
     else (if exprType == "signal"
      then (parseKey "name" *> identifier >>= λ name →
            pure (SignalYaml name))
      else (if exprType == "constant"
       then (parseKey "value" *> rational >>= λ val →
             pure (ConstantYaml val))
       else fail)))))

-- ============================================================================
-- PROPERTY PARSER (Fuel-bounded recursion)
-- ============================================================================

-- Fuel parameter bounds nesting depth to prevent infinite recursion
-- Our schema has maximum depth ~4, so fuel = 10 is more than sufficient
-- This avoids term expansion issues that occur with high fuel values

parsePropertyYaml : ℕ → Parser PropertyYaml
parsePropertyYaml zero = fail  -- Fuel exhausted (should never happen with valid input)
parsePropertyYaml (suc fuel) =
  skipWS *> parseKey "type" >>= λ _ →
  identifier >>= λ propType →
  skipWS *>
  parseByType propType
  where
    -- Expression parsers (helpers)
    parseCompareExpr : Parser ExprYaml
    parseCompareExpr =
      parseKey "signal" *> identifier >>= λ sig →
      skipWS *>
      parseKey "op" *> parseCompOpYaml >>= λ op →
      skipWS *>
      parseKey "value" *> rational >>= λ val →
      pure (CompareYaml sig op val)

    parseBetweenExpr : Parser ExprYaml
    parseBetweenExpr =
      parseKey "signal" *> identifier >>= λ sig →
      skipWS *>
      parseKey "min" *> rational >>= λ minV →
      skipWS *>
      parseKey "max" *> rational >>= λ maxV →
      pure (BetweenYaml sig minV maxV)

    parseChangedByExpr : Parser ExprYaml
    parseChangedByExpr =
      parseKey "signal" *> identifier >>= λ sig →
      skipWS *>
      parseKey "delta" *> rational >>= λ delta →
      pure (ChangedByYaml sig delta)

    parseSignalExpr : Parser ExprYaml
    parseSignalExpr =
      parseKey "name" *> identifier >>= λ name →
      pure (SignalYaml name)

    parseConstantExpr : Parser ExprYaml
    parseConstantExpr =
      parseKey "value" *> rational >>= λ val →
      pure (ConstantYaml val)

    parseByType : String → Parser PropertyYaml
    -- Simple temporal operators (contain expressions - no recursion)
    parseByType "always" =
      parseKey "formula" *> skipWS *> parseExprYaml >>= λ expr →
      pure (AlwaysYaml expr)
    parseByType "eventually" =
      parseKey "formula" *> skipWS *> parseExprYaml >>= λ expr →
      pure (EventuallyYaml expr)
    parseByType "never" =
      parseKey "formula" *> skipWS *> parseExprYaml >>= λ expr →
      pure (NeverYaml expr)

    -- Bounded temporal operators (time in microseconds)
    parseByType "eventually_within" =
      parseKey "time_us" *> natural >>= λ time →
      skipWS *>
      parseKey "formula" *> skipWS *> parseExprYaml >>= λ expr →
      pure (EventuallyWithinYaml time expr)
    parseByType "always_within" =
      parseKey "time_us" *> natural >>= λ time →
      skipWS *>
      parseKey "formula" *> skipWS *> parseExprYaml >>= λ expr →
      pure (AlwaysWithinYaml time expr)

    -- Compound operators (recursive - consume fuel)
    parseByType "not" =
      parseKey "formula" *> skipWS *> parsePropertyYaml fuel >>= λ sub →
      pure (NotYaml sub)
    parseByType "and" =
      parseKey "left" *> skipWS *> parsePropertyYaml fuel >>= λ left →
      skipWS *>
      parseKey "right" *> skipWS *> parsePropertyYaml fuel >>= λ right →
      pure (AndYaml left right)
    parseByType "or" =
      parseKey "left" *> skipWS *> parsePropertyYaml fuel >>= λ left →
      skipWS *>
      parseKey "right" *> skipWS *> parsePropertyYaml fuel >>= λ right →
      pure (OrYaml left right)
    parseByType "implies" =
      parseKey "antecedent" *> skipWS *> parsePropertyYaml fuel >>= λ ante →
      skipWS *>
      parseKey "consequent" *> skipWS *> parsePropertyYaml fuel >>= λ cons →
      pure (ImpliesYaml ante cons)
    parseByType "until" =
      parseKey "left" *> skipWS *> parsePropertyYaml fuel >>= λ left →
      skipWS *>
      parseKey "right" *> skipWS *> parsePropertyYaml fuel >>= λ right →
      pure (UntilYaml left right)

    -- Expression types (base case)
    parseByType "compare" =
      parseCompareExpr >>= λ expr → pure (ExprProperty expr)
    parseByType "between" =
      parseBetweenExpr >>= λ expr → pure (ExprProperty expr)
    parseByType "changed_by" =
      parseChangedByExpr >>= λ expr → pure (ExprProperty expr)
    parseByType "signal" =
      parseSignalExpr >>= λ expr → pure (ExprProperty expr)
    parseByType "constant" =
      parseConstantExpr >>= λ expr → pure (ExprProperty expr)

    parseByType _ = fail

-- ============================================================================
-- TOP-LEVEL PARSER WITH ERROR REPORTING
-- ============================================================================

-- Parser errors
data ParseError : Set where
  SyntaxError : String → Position → ParseError
  FuelExhausted : ℕ → ℕ → ParseError  -- actual depth, fuel limit

-- Parse result: error message or LTL formula
DSLParseResult : Set
DSLParseResult = String ⊎ LTL SignalPredicate

pattern DSLSuccess ltl = inj₂ ltl
pattern DSLError msg = inj₁ msg

-- Format error message
formatError : ParseError → String
formatError (SyntaxError msg pos) =
  "Parse error at line " ++ show (line pos) ++ ", column " ++ show (column pos) ++
  ": Invalid YAML syntax. " ++ msg
formatError (FuelExhausted actualDepth fuelLimit) =
  "Parse error: Property nesting depth (" ++ show actualDepth ++
  ") exceeds parser limit (" ++ show fuelLimit ++
  "). Please simplify the property structure or contact support."

-- Check depth and translate to LTL
checkAndTranslate : PropertyYaml → DSLParseResult
checkAndTranslate propYaml with depth propYaml ≤? 100
... | no _ = inj₁ (formatError (FuelExhausted (depth propYaml) 100))
... | yes _ with translate propYaml
...   | nothing = inj₁ "Translation error: unsupported property structure"
...   | just ltl = inj₂ ltl

-- Main entry point: parse YAML string to LTL formula
parseLTL : String → DSLParseResult
parseLTL input with runParser (parsePropertyYaml 100) (toList input)
... | nothing = inj₁ (formatError (SyntaxError "Could not parse YAML structure. Check property syntax." initialPosition))
... | just result = checkAndTranslate (proj₁ result)
