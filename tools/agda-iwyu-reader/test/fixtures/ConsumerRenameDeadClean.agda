{-# OPTIONS --safe --without-K #-}
module ConsumerRenameDeadClean where
open import Origin using () renaming (idO to idR)
data Dummy : Set where d : Dummy
