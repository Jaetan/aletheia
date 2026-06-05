{-# OPTIONS --safe --without-K #-}
-- USES both the re-exported value (idO) and the module-application copy (wrapR).
-- Expected reader verdicts: Mid=idO USED, Mid=InstR (module) USED.
module ConsumerUsed where

open import Mid using (idO; module InstR)
open InstR

useVal : {X : Set} → X → X
useVal x = idO x      -- elaborates to Origin.idO

useMod : {X : Set} → X → X
useMod x = wrapR x    -- elaborates to Origin.GenR.wrapR (origin of the InstR copy)
