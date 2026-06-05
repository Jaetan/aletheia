{-# OPTIONS --safe --without-K #-}
module ConsumerReExpNarrow where
open import MidRX
useRe : Trx
useRe = rxUsed mkrx   -- uses re-exported rxUsed + mkrx + Trx; NOT rxUnused, NOT reOwn
