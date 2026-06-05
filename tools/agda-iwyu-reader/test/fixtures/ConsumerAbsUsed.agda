{-# OPTIONS --safe --without-K #-}
module ConsumerAbsUsed where
open import AbsGen using (TagAb; mkAb)
open import AbsMid using (module InstAb)
open InstAb
useAb : TagAb
useAb = absF mkAb
