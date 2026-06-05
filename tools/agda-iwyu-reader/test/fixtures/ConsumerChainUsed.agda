{-# OPTIONS --safe --without-K #-}
module ConsumerChainUsed where
open import OriginC using (TagC; mkC)
open import MidC2 using (module InstC2)
open InstC2
useChain : TagC
useChain = wrapC mkC
