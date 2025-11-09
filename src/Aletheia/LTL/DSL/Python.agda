{-# OPTIONS --safe --without-K #-}

module Aletheia.LTL.DSL.Python where

open import Data.Nat using (ℕ)
open import Data.String using (String)
open import Data.Rational using (ℚ)

data ComparisonOp : Set where
  LT GT LE GE EQ NE : ComparisonOp

data PythonExpr : Set where
  Signal : String → PythonExpr
  Constant : ℚ → PythonExpr
  Compare : PythonExpr → ComparisonOp → PythonExpr → PythonExpr

data PythonLTL : Set where
  Expr : PythonExpr → PythonLTL
  Always Eventually : PythonLTL → PythonLTL
  EventuallyWithin : ℕ → PythonLTL → PythonLTL
  Never : PythonLTL → PythonLTL
  Implies : PythonLTL → PythonLTL → PythonLTL
