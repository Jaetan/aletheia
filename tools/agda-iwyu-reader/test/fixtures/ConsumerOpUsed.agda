{-# OPTIONS --safe --without-K #-}
module ConsumerOpUsed where
open import OpMod using (TagO; mkO; _⊕_; _⊗_)
useOp : TagO
useOp = mkO ⊕ mkO
