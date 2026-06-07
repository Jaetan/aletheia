{-# OPTIONS --safe --without-K #-}
module ConsumerRenamePatUsed where
open import PatLib using (NatLike) renaming (two to twoR)
useTwo : NatLike
useTwo = twoR
