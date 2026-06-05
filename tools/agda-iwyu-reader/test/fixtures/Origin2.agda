{-# OPTIONS --safe --without-K #-}
-- Discriminating origin: GenR.wrapR's TYPE references a QName (Tag), and the
-- module application below passes Tag as the argument.  So namesIn(copy-def)
-- will include Tag (from the type/args) IN ADDITION to the delegated origin.
module Origin2 where

data Tag : Set where
  mk : Tag

module GenR (X : Set) where
  wrapR : Tag → Tag       -- type mentions Tag (a real QName, used elsewhere)
  wrapR t = t
