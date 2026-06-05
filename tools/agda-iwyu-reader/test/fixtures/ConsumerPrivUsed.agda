{-# OPTIONS --safe --without-K #-}
module ConsumerPrivUsed where
open import LibP using (TagP; mkP)
private
  open import LibP using (privF)
useP : TagP
useP = privF mkP
