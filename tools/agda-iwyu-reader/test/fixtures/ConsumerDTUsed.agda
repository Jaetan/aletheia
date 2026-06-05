{-# OPTIONS --safe --without-K #-}
module ConsumerDTUsed where
open import OriginDT using (Seed)
open import MidDT using (module InstD)
open InstD
useD : D
useD = dcon
