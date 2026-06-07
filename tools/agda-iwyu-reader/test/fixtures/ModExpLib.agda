{-# OPTIONS --safe --without-K #-}
module ModExpLib where

data U : Set where
  u : U

module Impl where
  module Reasoning where
    idr : U → U
    idr x = x

open Impl public
