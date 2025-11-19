{-# OPTIONS --safe --without-K #-}

module Aletheia.LTL.DSL.Convert where

open import Aletheia.LTL.DSL.Yaml
open import Aletheia.LTL.DSL.Python
open import Data.Maybe using (Maybe; just; nothing)

-- ============================================================================
-- CONVERSION: PropertyYaml → PythonLTL
-- ============================================================================

-- Convert comparison operator from YAML to Python AST
convertCompOp : CompOpYaml → ComparisonOp
convertCompOp LT-yaml = LT
convertCompOp GT-yaml = GT
convertCompOp LE-yaml = LE
convertCompOp GE-yaml = GE
convertCompOp EQ-yaml = EQ
convertCompOp NE-yaml = NE

-- Convert expression YAML to PythonExpr
-- No recursion - all expressions are leaves
exprYamlToExpr : ExprYaml → PythonExpr
exprYamlToExpr (CompareYaml sig op val) =
  Compare (Signal sig) (convertCompOp op) (Constant val)
exprYamlToExpr (BetweenYaml sig minV maxV) =
  Between sig minV maxV
exprYamlToExpr (ChangedByYaml sig delta) =
  ChangedBy sig delta
exprYamlToExpr (SignalYaml name) =
  Signal name
exprYamlToExpr (ConstantYaml val) =
  Constant val

-- Convert property YAML to PythonLTL
-- Structurally recursive on PropertyYaml structure
propertyYamlToLTL : PropertyYaml → PythonLTL
propertyYamlToLTL (ExprProperty expr) =
  Expr (exprYamlToExpr expr)

-- Simple temporal operators with expression formulas
propertyYamlToLTL (AlwaysYaml expr) =
  Always (Expr (exprYamlToExpr expr))
propertyYamlToLTL (EventuallyYaml expr) =
  Eventually (Expr (exprYamlToExpr expr))
propertyYamlToLTL (NeverYaml expr) =
  Never (Expr (exprYamlToExpr expr))

-- Bounded temporal operators
propertyYamlToLTL (EventuallyWithinYaml time expr) =
  EventuallyWithin time (Expr (exprYamlToExpr expr))
propertyYamlToLTL (AlwaysWithinYaml time expr) =
  AlwaysWithin time (Expr (exprYamlToExpr expr))

-- Compound operators with recursive sub-properties
-- Structurally smaller arguments - termination is obvious!
propertyYamlToLTL (NotYaml sub) =
  Not (propertyYamlToLTL sub)
propertyYamlToLTL (AndYaml left right) =
  And (propertyYamlToLTL left) (propertyYamlToLTL right)
propertyYamlToLTL (OrYaml left right) =
  Or (propertyYamlToLTL left) (propertyYamlToLTL right)
propertyYamlToLTL (ImpliesYaml ante cons) =
  Implies (propertyYamlToLTL ante) (propertyYamlToLTL cons)
propertyYamlToLTL (UntilYaml left right) =
  Until (propertyYamlToLTL left) (propertyYamlToLTL right)
