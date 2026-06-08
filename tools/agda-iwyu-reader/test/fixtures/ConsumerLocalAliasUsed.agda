{-# OPTIONS --safe --without-K #-}
module ConsumerLocalAliasUsed where
open import LocAliasLib using (U; module Helper)
open Helper using (idh)
useH : U → U
useH x = idh x
