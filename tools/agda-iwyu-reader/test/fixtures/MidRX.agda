{-# OPTIONS --safe --without-K #-}
module MidRX where
open import OriginRX public   -- re-exports Trx, mkrx, rxUsed, rxUnused
reOwn : Trx → Trx
reOwn t = t
