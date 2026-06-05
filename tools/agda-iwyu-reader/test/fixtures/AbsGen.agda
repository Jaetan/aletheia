{-# OPTIONS --safe --without-K #-}
module AbsGen where
data TagAb : Set where mkAb : TagAb
module GenAb (X : Set) where
  abstract
    absF : TagAb → TagAb
    absF t = t
