{-# OPTIONS --safe --without-K #-}
module PatLib where
data NatLike : Set where
  zeroL : NatLike
  sucL  : NatLike → NatLike
pattern two = sucL (sucL zeroL)
