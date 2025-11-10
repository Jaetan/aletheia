{-# OPTIONS --safe #-}

-- Helper module to pre-compile common stdlib dependencies
-- This will cache the compiled .agdai files for faster subsequent builds

module PrecompileStdlib where

-- Import all modules used by our codebase
open import Data.List
open import Data.Maybe
open import Data.Product
open import Data.Char
open import Data.Char.Base
open import Data.Bool
open import Data.Nat
open import Data.String
open import Function
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

-- This module doesn't need to do anything else
-- Just importing is enough to trigger compilation
