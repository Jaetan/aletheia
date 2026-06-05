{-# OPTIONS --safe --without-K #-}
module ConsumerWildDead where
open import WMod
data Other : Set where o : Other
useO : Other
useO = o
