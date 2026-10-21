-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- The JSON text grammar of RFC 8259, rule for rule.
--
-- Each rule of the RFC's ABNF (sections 2 to 7) is a relation on lists of
-- characters, named after the rule and quoted above it; a sequence holds the
-- concatenation of the lists its parts hold.  It is the specification
-- `Aletheia.Protocol.JSON.Parse` is proven against: a text the parser accepts
-- whole is a `JSONText`.  The `unescaped` rule's upper bound, U+10FFFF, is
-- the largest code point an Agda `Char` holds.
module Aletheia.Protocol.JSON.RFC8259 where

open import Data.Char using (Char)
open import Data.Char.Base using (toℕ)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.All using (All)
open import Data.Nat using (_≤_)
open import Data.Product using (_×_)
open import Data.Sum using (_⊎_)
open import Relation.Binary.PropositionalEquality using (_≢_)

-- ws = *( %x20 / %x09 / %x0A / %x0D )
data WsChar : Char → Set where
  ws-space : WsChar ' '
  ws-tab   : WsChar '\t'
  ws-lf    : WsChar '\n'
  ws-cr    : WsChar '\r'

Ws : List Char → Set
Ws = All WsChar

-- begin-array = ws %x5B ws, begin-object = ws %x7B ws, end-array = ws %x5D ws,
-- end-object = ws %x7D ws, name-separator = ws %x3A ws,
-- value-separator = ws %x2C ws
data Structural (s : Char) : List Char → Set where
  structural-ws : ∀ {a b} → Ws a → Ws b → Structural s (a ++ s ∷ b)

-- DIGIT = %x30-39
Digit : Char → Set
Digit c = 48 ≤ toℕ c × toℕ c ≤ 57

-- int = zero / ( digit1-9 *DIGIT )
data Int : List Char → Set where
  int-zero    : Int ('0' ∷ [])
  int-nonzero : ∀ {c cs} → Digit c → c ≢ '0' → All Digit cs → Int (c ∷ cs)

-- [ minus ]
data OptMinus : List Char → Set where
  no-minus : OptMinus []
  minus    : OptMinus ('-' ∷ [])

-- [ frac ], frac = decimal-point 1*DIGIT
data OptFrac : List Char → Set where
  no-frac : OptFrac []
  frac    : ∀ {c cs} → Digit c → All Digit cs → OptFrac ('.' ∷ c ∷ cs)

-- e = %x65 / %x45
data E : Char → Set where
  e-lower : E 'e'
  e-upper : E 'E'

-- [ minus / plus ]
data OptSign : List Char → Set where
  no-sign    : OptSign []
  sign-minus : OptSign ('-' ∷ [])
  sign-plus  : OptSign ('+' ∷ [])

-- [ exp ], exp = e [ minus / plus ] 1*DIGIT
data OptExp : List Char → Set where
  no-exp : OptExp []
  exp    : ∀ {e s c cs} → E e → OptSign s → Digit c → All Digit cs → OptExp (e ∷ s ++ c ∷ cs)

-- number = [ minus ] int [ frac ] [ exp ]
data Number : List Char → Set where
  number : ∀ {m i f x} → OptMinus m → Int i → OptFrac f → OptExp x → Number (m ++ i ++ f ++ x)

-- unescaped = %x20-21 / %x23-5B / %x5D-10FFFF
Unescaped : Char → Set
Unescaped c = 32 ≤ toℕ c × c ≢ '"' × c ≢ '\\'

-- HEXDIG = DIGIT / "A" / "B" / "C" / "D" / "E" / "F", either case
HexDig : Char → Set
HexDig c = Digit c ⊎ (65 ≤ toℕ c × toℕ c ≤ 70) ⊎ (97 ≤ toℕ c × toℕ c ≤ 102)

-- char = unescaped /
--     escape (
--         %x22 /          ; "    quotation mark  U+0022
--         %x5C /          ; \    reverse solidus U+005C
--         %x2F /          ; /    solidus         U+002F
--         %x62 /          ; b    backspace       U+0008
--         %x66 /          ; f    form feed       U+000C
--         %x6E /          ; n    line feed       U+000A
--         %x72 /          ; r    carriage return U+000D
--         %x74 /          ; t    tab             U+0009
--         %x75 4HEXDIG )  ; uXXXX                U+XXXX
data StringChar : List Char → Set where
  char-unescaped : ∀ {c} → Unescaped c → StringChar (c ∷ [])
  char-quote     : StringChar ('\\' ∷ '"' ∷ [])
  char-backslash : StringChar ('\\' ∷ '\\' ∷ [])
  char-solidus   : StringChar ('\\' ∷ '/' ∷ [])
  char-backspace : StringChar ('\\' ∷ 'b' ∷ [])
  char-formfeed  : StringChar ('\\' ∷ 'f' ∷ [])
  char-linefeed  : StringChar ('\\' ∷ 'n' ∷ [])
  char-return    : StringChar ('\\' ∷ 'r' ∷ [])
  char-tab       : StringChar ('\\' ∷ 't' ∷ [])
  char-unicode   : ∀ {h₁ h₂ h₃ h₄} → HexDig h₁ → HexDig h₂ → HexDig h₃ → HexDig h₄ →
                   StringChar ('\\' ∷ 'u' ∷ h₁ ∷ h₂ ∷ h₃ ∷ h₄ ∷ [])

-- *char
data StringChars : List Char → Set where
  chars-none : StringChars []
  chars-more : ∀ {c cs} → StringChar c → StringChars cs → StringChars (c ++ cs)

-- string = quotation-mark *char quotation-mark
data StringLit : List Char → Set where
  string-lit : ∀ {cs} → StringChars cs → StringLit ('"' ∷ cs ++ '"' ∷ [])

mutual
  -- value = false / null / true / object / array / number / string
  data Value : List Char → Set where
    value-false  : Value ('f' ∷ 'a' ∷ 'l' ∷ 's' ∷ 'e' ∷ [])
    value-null   : Value ('n' ∷ 'u' ∷ 'l' ∷ 'l' ∷ [])
    value-true   : Value ('t' ∷ 'r' ∷ 'u' ∷ 'e' ∷ [])
    value-object : ∀ {b ms e} → Structural '{' b → Members ms → Structural '}' e → Value (b ++ ms ++ e)
    value-array  : ∀ {b vs e} → Structural '[' b → Values vs → Structural ']' e → Value (b ++ vs ++ e)
    value-number : ∀ {cs} → Number cs → Value cs
    value-string : ∀ {cs} → StringLit cs → Value cs

  -- object = begin-object [ member *( value-separator member ) ] end-object
  data Members : List Char → Set where
    members-none : Members []
    members-some : ∀ {m ms} → Member m → MoreMembers ms → Members (m ++ ms)

  data MoreMembers : List Char → Set where
    more-members-none : MoreMembers []
    more-members      : ∀ {s m ms} → Structural ',' s → Member m → MoreMembers ms → MoreMembers (s ++ m ++ ms)

  -- member = string name-separator value
  data Member : List Char → Set where
    member : ∀ {k s v} → StringLit k → Structural ':' s → Value v → Member (k ++ s ++ v)

  -- array = begin-array [ value *( value-separator value ) ] end-array
  data Values : List Char → Set where
    values-none : Values []
    values-some : ∀ {v vs} → Value v → MoreValues vs → Values (v ++ vs)

  data MoreValues : List Char → Set where
    more-values-none : MoreValues []
    more-values      : ∀ {s v vs} → Structural ',' s → Value v → MoreValues vs → MoreValues (s ++ v ++ vs)

-- JSON-text = ws value ws
data JSONText : List Char → Set where
  json-text : ∀ {a v b} → Ws a → Value v → Ws b → JSONText (a ++ v ++ b)
