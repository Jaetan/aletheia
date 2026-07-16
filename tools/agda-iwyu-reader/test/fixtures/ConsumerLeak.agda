-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}
-- `inner` is imported but never written here.  Scrutinising `outer x` with `in eq`
-- forces `outer` to reduce, so `inner`'s QName is baked into the elaborated
-- with-function.  That baked reference is fully qualified and resolves through the
-- transitive import, so it does not need this scope entry: `inner` is DEAD.
module ConsumerLeak where

open import Agda.Builtin.Equality using (_≡_; refl)
open import LeakLib using (TagL; mkL; outer; inner)

f : TagL → TagL
f x with outer x in eq
... | mkL = mkL
