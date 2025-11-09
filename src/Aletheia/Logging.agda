{-# OPTIONS --safe --without-K #-}

module Aletheia.Logging where

open import Data.Nat using (ℕ)
open import Data.String using (String)
open import Data.List using (List)

data LogLevel : Set where
  Debug Warning Info Error : LogLevel

record LogEntry : Set where
  field
    level : LogLevel
    component : String
    message : String
    timestamp : ℕ

record Result (A : Set) : Set where
  field
    value : A
    logs : List LogEntry
