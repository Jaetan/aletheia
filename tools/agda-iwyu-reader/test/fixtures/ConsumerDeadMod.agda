{-# OPTIONS --safe --without-K #-}
-- Imports `module InstR2` but NEVER uses wrapR.  It DOES use Tag/mk independently.
-- Tag is in the copy wrapR's type/args, so blanket namesIn(copy-def) ∩ used would
-- (wrongly) report InstR2 ALIVE via Tag.  Correct verdict: DEAD.
module ConsumerDeadMod where

open import Origin2 using (Tag; mk)
open import Mid2 using (module InstR2)
open InstR2

useTag : Tag
useTag = mk        -- uses Tag/mk (in used-set) but never wrapR
