{-# OPTIONS --safe --without-K #-}
module ConsumerWildRedundant where
open import WMod using (Tw; mkw; wa; wb)
open import WMod
useAB : Tw
useAB = wa (wb mkw)
