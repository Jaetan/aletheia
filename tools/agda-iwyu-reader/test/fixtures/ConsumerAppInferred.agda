{-# OPTIONS --safe --without-K #-}
module ConsumerAppInferred where
open import MidAX
needA : {{BoxA}} → Tax
needA {{b}} = unboxA b
r : Tax
r = needA    -- boxA (the applied copy) resolved by instance search: no body token
