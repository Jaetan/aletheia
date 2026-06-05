{-# OPTIONS --safe --without-K #-}
module LibP where
data TagP : Set where mkP : TagP
privF : TagP → TagP
privF t = t
otherF : TagP → TagP
otherF t = t
