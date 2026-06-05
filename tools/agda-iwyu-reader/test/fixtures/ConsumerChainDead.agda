{-# OPTIONS --safe --without-K #-}
module ConsumerChainDead where
open import OriginC using (TagC; mkC)
open import MidC2 using (module InstC2)
open InstC2
noChain : TagC
noChain = mkC
