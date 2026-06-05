{-# OPTIONS --safe --without-K #-}
-- Same imports, but DOES use wrapR.  Correct verdict for InstR2: ALIVE.
module ConsumerUsedMod where

open import Origin2 using (Tag; mk)
open import Mid2 using (module InstR2)
open InstR2

roundTag : Tag
roundTag = wrapR mk       -- uses the module-application copy
