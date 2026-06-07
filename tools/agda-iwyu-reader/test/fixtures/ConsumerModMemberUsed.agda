{-# OPTIONS --safe --without-K #-}
module ConsumerModMemberUsed where
open import ModExpLib using (U; module Reasoning)
open Reasoning
useR : U → U
useR x = idr x
