{-# OPTIONS --safe --without-K #-}
module ConsumerIDead where
open import OriginI using (TagI2; mkI2)
open import MidI using (module InstI)
open InstI
r : TagI2
r = mkI2       -- InstI never used
