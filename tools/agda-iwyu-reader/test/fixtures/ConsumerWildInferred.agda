{-# OPTIONS --safe --without-K #-}
module ConsumerWildInferred where
open import WInst
r : Ti
r = needI    -- insti resolved by instance search: no body token, only namesIn sees it
