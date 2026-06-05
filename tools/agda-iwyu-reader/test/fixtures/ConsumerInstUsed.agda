{-# OPTIONS --safe --without-K #-}
module ConsumerInstUsed where
open import InstLib using (TagI; getDef; defI)
r : TagI
r = getDef
