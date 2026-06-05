{-# OPTIONS --safe --without-K #-}
module ConsumerDTDead where
open import OriginDT using (Seed; s0)
open import MidDT using (module InstD)
open InstD
noD : Seed
noD = s0
