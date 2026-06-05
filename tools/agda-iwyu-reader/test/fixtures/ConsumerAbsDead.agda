{-# OPTIONS --safe --without-K #-}
module ConsumerAbsDead where
open import AbsGen using (TagAb; mkAb)
open import AbsMid using (module InstAb)
open InstAb
noAb : TagAb
noAb = mkAb
