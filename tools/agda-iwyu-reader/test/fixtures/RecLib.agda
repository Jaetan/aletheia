{-# OPTIONS --safe --without-K #-}
module RecLib where
data TagR : Set where mkR : TagR
record Pair : Set where
  field fstP : TagR
        sndP : TagR
open Pair public
