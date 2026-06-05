{-# OPTIONS --safe --without-K #-}
module ConsumerRenameUsed where
open import Origin using () renaming (idO to idR)
useR : {X : Set} → X → X
useR x = idR x
