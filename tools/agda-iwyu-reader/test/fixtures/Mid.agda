{-# OPTIONS --safe --without-K #-}
-- The "middle" module: re-exports a VALUE (open ... public, no copy) AND
-- instantiates the parametrized module via a module application (open GenR X
-- public inside InstR — this DOES create copies of wrapR under InstR).
module Mid where

open import Origin
open Origin using (idO) public   -- value re-export: scope anameName stays Origin.idO

module InstR {X : Set} where
  open GenR X public             -- module application: copies wrapR into InstR._
