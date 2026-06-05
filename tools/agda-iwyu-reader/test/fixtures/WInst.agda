{-# OPTIONS --safe --without-K #-}
module WInst where
data Ti : Set where mki : Ti
record HasI : Set where
  field geti : Ti
open HasI public
instance
  insti : HasI
  insti = record { geti = mki }
needI : {{HasI}} → Ti
needI {{r}} = HasI.geti r
