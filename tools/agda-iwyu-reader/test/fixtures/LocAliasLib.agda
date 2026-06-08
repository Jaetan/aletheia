{-# OPTIONS --safe --without-K #-}
module LocAliasLib where

data U : Set where
  u : U

module Helper where
  idh : U → U
  idh x = x
