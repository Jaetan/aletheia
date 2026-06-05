{-# OPTIONS --safe --without-K #-}
module OriginRX where
data Trx : Set where mkrx : Trx
rxUsed : Trx → Trx
rxUsed t = t
rxUnused : Trx → Trx
rxUnused t = t
