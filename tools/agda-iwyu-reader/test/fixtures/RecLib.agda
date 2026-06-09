-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}
module RecLib where
data TagR : Set where mkR : TagR
record Pair : Set where
  field fstP : TagR
        sndP : TagR
open Pair public
