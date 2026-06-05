{-# OPTIONS --safe --without-K #-}
module ConsumerRecUsed where
open import RecLib using (TagR; mkR; Pair; fstP)
getF : Pair → TagR
getF p = fstP p
