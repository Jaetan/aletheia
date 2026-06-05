{-# OPTIONS --safe --without-K #-}
module OriginC where
data TagC : Set where mkC : TagC
module GenC (X : Set) where
  wrapC : TagC → TagC
  wrapC t = t
