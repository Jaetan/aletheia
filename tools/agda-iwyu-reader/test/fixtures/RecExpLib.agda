{-# OPTIONS --safe --without-K #-}
module RecExpLib where

data U : Set where
  u : U

module Inner where
  record Box : Set where
    field unbox : U
  theBox : Box
  theBox = record { unbox = u }

open Inner public
