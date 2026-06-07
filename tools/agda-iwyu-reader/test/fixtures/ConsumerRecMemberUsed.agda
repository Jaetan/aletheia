{-# OPTIONS --safe --without-K #-}
module ConsumerRecMemberUsed where
open import RecExpLib using (U; Box; theBox)
getU : U
getU = Box.unbox theBox
