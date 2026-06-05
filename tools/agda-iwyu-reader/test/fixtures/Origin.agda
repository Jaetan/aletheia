{-# OPTIONS --safe --without-K #-}
-- The "origin" module: directly defines a value and a PARAMETRIZED module.
-- A module application of GenR elsewhere creates COPIES whose elaborated bodies
-- unfold back to these origins (Origin.idO / Origin.GenR.wrapR).
module Origin where

idO : {X : Set} → X → X
idO x = x

module GenR (X : Set) where
  wrapR : X → X
  wrapR x = x
