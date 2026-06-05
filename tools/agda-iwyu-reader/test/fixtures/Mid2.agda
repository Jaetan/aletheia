{-# OPTIONS --safe --without-K #-}
module Mid2 where

open import Origin2

module InstR2 where
  open GenR Tag public    -- module application; arg Tag is a QName carried into the copy
