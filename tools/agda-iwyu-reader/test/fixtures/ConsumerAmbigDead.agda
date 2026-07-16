-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}
-- The counterpart of ConsumerAmbigTerm: `nilA` is imported but never written, so an
-- overloaded name must still be reported DEAD.  Suspending the syntactic signal for
-- these names must not degrade into "overloaded => always keep".
module ConsumerAmbigDead where

open import AmbigMid using (BoxA; nilA)

v : BoxA → BoxA
v x = x
