{-# OPTIONS --safe --without-K #-}
module OpMod where
data TagO : Set where mkO : TagO
_⊕_ : TagO → TagO → TagO
_ ⊕ y = y
_⊗_ : TagO → TagO → TagO
_ ⊗ y = y
