{-# OPTIONS --safe --without-K #-}

module Aletheia.LTL.Syntax where

open import Data.Nat using (ℕ)

data LTL (Atom : Set) : Set where
  Atomic : Atom → LTL Atom
  Not : LTL Atom → LTL Atom
  And Or : LTL Atom → LTL Atom → LTL Atom
  Next : LTL Atom → LTL Atom
  Always Eventually : LTL Atom → LTL Atom
  Until : LTL Atom → LTL Atom → LTL Atom
  EventuallyWithin : ℕ → LTL Atom → LTL Atom
  AlwaysWithin : ℕ → LTL Atom → LTL Atom
