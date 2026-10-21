-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Every reply is RFC 8259 JSON text, and holds no raw control character.
--
-- The JSON parser reads back what the formatter writes for a value whose
-- numbers every reader decodes (`Aletheia.Protocol.JSON.Properties.Roundtrip`),
-- every reply's numbers are such (`formatResponse-readable`), and whatever the
-- parser reads whole is RFC 8259 JSON text (`Aletheia.Protocol.JSON.
-- Properties.Sound`).  Every character of such a text is at or above U+0020,
-- or one of the four whitespace characters.
module Aletheia.Protocol.ResponseFormat.Properties.JSONText where

open import Data.Char using (Char)
import Data.Bool
import Data.Nat
open import Data.Char.Base using (toℕ)
open import Data.Integer using (+_; -[1+_]; -≤-; +≤+)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.All.Properties using (++⁺)
open import Data.Nat using (_≤_; _<_; s≤s)
open import Data.Nat.Properties using (≤-<-trans; ≤-trans; <ᵇ⇒<; ≤ᵇ⇒≤)
open import Data.Product using (_,_)
open import Data.Rational using (mkℚ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)

open import Aletheia.DBC.DecRat.Literal using (heldMagnitude)
open import Aletheia.Limits using (observed-ceiling)
open import Aletheia.Parser.Position using (initialPosition)
open import Aletheia.Protocol.JSON.Format using (formatJSONChars)
open import Aletheia.Protocol.JSON.Properties.Roundtrip using (ReadExactly; parseJSON-formatJSONChars)
open import Aletheia.Protocol.JSON.Properties.Sound using (parseJSON-sound)
open import Aletheia.Protocol.JSON.RFC8259 using (Digit; E; HexDig; Int; JSONText; Member; Members; MoreMembers; MoreValues; Number; OptExp; OptFrac; OptMinus; OptSign; StringChar; StringChars; StringLit; Structural; Value; Values; Ws; WsChar; char-backslash; char-backspace; char-formfeed; char-linefeed; char-quote; char-return; char-solidus; char-tab; char-unescaped; char-unicode; chars-more; chars-none; e-lower; e-upper; exp; frac; int-nonzero; int-zero; json-text; member; members-none; members-some; minus; more-members; more-members-none; more-values; more-values-none; no-exp; no-frac; no-minus; no-sign; number; sign-minus; sign-plus; string-lit; structural-ws; value-array; value-false; value-null; value-number; value-object; value-string; value-true; values-none; values-some)
open import Aletheia.Protocol.ResponseFormat using (formatResponse)
open import Aletheia.Protocol.ResponseFormat.Properties using (InReaderRange; satisfy-map; formatResponse-readable)

-- ============================================================================
-- EVERY REPLY IS JSON TEXT
-- ============================================================================

private
  ceiling<held : observed-ceiling < heldMagnitude
  ceiling<held = <ᵇ⇒< observed-ceiling heldMagnitude tt

  2^63<held : 9223372036854775808 < heldMagnitude
  2^63<held = <ᵇ⇒< 9223372036854775808 heldMagnitude tt

-- A rational every reader decodes is one the parser reads exactly.
readable-exact : ∀ q → InReaderRange q → ReadExactly q
readable-exact (mkℚ (+ n)    d _) (_ , +≤+ n≤ , d≤)     = ≤-<-trans n≤ ceiling<held , ≤-<-trans d≤ ceiling<held
readable-exact (mkℚ -[1+ n ] d _) (-≤- n≤ , _ , d≤)     = ≤-<-trans (s≤s n≤) 2^63<held , ≤-<-trans d≤ ceiling<held

-- THEOREM: every reply's characters are RFC 8259 JSON text.  Erased, since
-- it reads the erased proofs the replies carry.
@0 reply-is-JSONText : ∀ r → JSONText (formatJSONChars (formatResponse r))
reply-is-JSONText r =
  parseJSON-sound initialPosition (formatJSONChars j) _
    (parseJSON-formatJSONChars initialPosition j (satisfy-map readable-exact j (formatResponse-readable r)))
  where
    j = formatResponse r

-- ============================================================================
-- NO RAW CONTROL CHARACTER
-- ============================================================================

-- A character JSON text may hold as it is: U+0020 or above, or whitespace.
data TextChar (c : Char) : Set where
  printable : 32 ≤ toℕ c → TextChar c
  spacing   : WsChar c → TextChar c

private
  -- A character known by its code.
  lit : ∀ c → Data.Bool.T (32 Data.Nat.≤ᵇ toℕ c) → TextChar c
  lit c t = printable (≤ᵇ⇒≤ 32 (toℕ c) t)

  digit-text : ∀ {c} → Digit c → TextChar c
  digit-text (48≤ , _) = printable (≤-trans (≤ᵇ⇒≤ 32 48 tt) 48≤)

  hex-text : ∀ {c} → HexDig c → TextChar c
  hex-text (inj₁ d)              = digit-text d
  hex-text (inj₂ (inj₁ (65≤ , _))) = printable (≤-trans (≤ᵇ⇒≤ 32 65 tt) 65≤)
  hex-text (inj₂ (inj₂ (97≤ , _))) = printable (≤-trans (≤ᵇ⇒≤ 32 97 tt) 97≤)

  digits-text : ∀ {cs} → All Digit cs → All TextChar cs
  digits-text []       = []
  digits-text (d ∷ ds) = digit-text d ∷ digits-text ds

  ws-text : ∀ {cs} → Ws cs → All TextChar cs
  ws-text []       = []
  ws-text (w ∷ ws) = spacing w ∷ ws-text ws

structural-text : ∀ {s cs} → Data.Bool.T (32 Data.Nat.≤ᵇ toℕ s) → Structural s cs → All TextChar cs
structural-text t (structural-ws wa wb) = ++⁺ (ws-text wa) (lit _ t ∷ ws-text wb)

number-text : ∀ {cs} → Number cs → All TextChar cs
number-text (number m i f x) = ++⁺ (minus-text m) (++⁺ (int-text i) (++⁺ (frac-text f) (exp-text x)))
  where
    minus-text : ∀ {cs} → OptMinus cs → All TextChar cs
    minus-text no-minus = []
    minus-text minus    = lit '-' tt ∷ []
    int-text : ∀ {cs} → Int cs → All TextChar cs
    int-text int-zero                = lit '0' tt ∷ []
    int-text (int-nonzero d _ ds)    = digit-text d ∷ digits-text ds
    frac-text : ∀ {cs} → OptFrac cs → All TextChar cs
    frac-text no-frac       = []
    frac-text (frac d ds)   = lit '.' tt ∷ digit-text d ∷ digits-text ds
    e-text : ∀ {c} → E c → TextChar c
    e-text e-lower = lit 'e' tt
    e-text e-upper = lit 'E' tt
    sign-text : ∀ {cs} → OptSign cs → All TextChar cs
    sign-text no-sign    = []
    sign-text sign-minus = lit '-' tt ∷ []
    sign-text sign-plus  = lit '+' tt ∷ []
    exp-text : ∀ {cs} → OptExp cs → All TextChar cs
    exp-text no-exp            = []
    exp-text (exp e s d ds)    = e-text e ∷ ++⁺ (sign-text s) (digit-text d ∷ digits-text ds)

stringChar-text : ∀ {cs} → StringChar cs → All TextChar cs
stringChar-text (char-unescaped (32≤ , _)) = printable 32≤ ∷ []
stringChar-text char-quote                 = lit '\\' tt ∷ lit '"' tt ∷ []
stringChar-text char-backslash             = lit '\\' tt ∷ lit '\\' tt ∷ []
stringChar-text char-solidus               = lit '\\' tt ∷ lit '/' tt ∷ []
stringChar-text char-backspace             = lit '\\' tt ∷ lit 'b' tt ∷ []
stringChar-text char-formfeed              = lit '\\' tt ∷ lit 'f' tt ∷ []
stringChar-text char-linefeed              = lit '\\' tt ∷ lit 'n' tt ∷ []
stringChar-text char-return                = lit '\\' tt ∷ lit 'r' tt ∷ []
stringChar-text char-tab                   = lit '\\' tt ∷ lit 't' tt ∷ []
stringChar-text (char-unicode h₁ h₂ h₃ h₄) =
  lit '\\' tt ∷ lit 'u' tt ∷ hex-text h₁ ∷ hex-text h₂ ∷ hex-text h₃ ∷ hex-text h₄ ∷ []

stringChars-text : ∀ {cs} → StringChars cs → All TextChar cs
stringChars-text chars-none        = []
stringChars-text (chars-more c cs) = ++⁺ (stringChar-text c) (stringChars-text cs)

stringLit-text : ∀ {cs} → StringLit cs → All TextChar cs
stringLit-text (string-lit cs) = lit '"' tt ∷ ++⁺ (stringChars-text cs) (lit '"' tt ∷ [])

mutual
  value-text : ∀ {cs} → Value cs → All TextChar cs
  value-text value-false              = lit 'f' tt ∷ lit 'a' tt ∷ lit 'l' tt ∷ lit 's' tt ∷ lit 'e' tt ∷ []
  value-text value-null               = lit 'n' tt ∷ lit 'u' tt ∷ lit 'l' tt ∷ lit 'l' tt ∷ []
  value-text value-true               = lit 't' tt ∷ lit 'r' tt ∷ lit 'u' tt ∷ lit 'e' tt ∷ []
  value-text (value-object b ms e)    = ++⁺ (structural-text tt b) (++⁺ (members-text ms) (structural-text tt e))
  value-text (value-array b vs e)     = ++⁺ (structural-text tt b) (++⁺ (values-text vs) (structural-text tt e))
  value-text (value-number n)         = number-text n
  value-text (value-string s)         = stringLit-text s

  members-text : ∀ {cs} → Members cs → All TextChar cs
  members-text members-none        = []
  members-text (members-some m ms) = ++⁺ (member-text m) (more-members-text ms)

  more-members-text : ∀ {cs} → MoreMembers cs → All TextChar cs
  more-members-text more-members-none     = []
  more-members-text (more-members s m ms) = ++⁺ (structural-text tt s) (++⁺ (member-text m) (more-members-text ms))

  member-text : ∀ {cs} → Member cs → All TextChar cs
  member-text (member k s v) = ++⁺ (stringLit-text k) (++⁺ (structural-text tt s) (value-text v))

  values-text : ∀ {cs} → Values cs → All TextChar cs
  values-text values-none        = []
  values-text (values-some v vs) = ++⁺ (value-text v) (more-values-text vs)

  more-values-text : ∀ {cs} → MoreValues cs → All TextChar cs
  more-values-text more-values-none     = []
  more-values-text (more-values s v vs) = ++⁺ (structural-text tt s) (++⁺ (value-text v) (more-values-text vs))

jsonText-chars : ∀ {cs} → JSONText cs → All TextChar cs
jsonText-chars (json-text wa v wb) = ++⁺ (ws-text wa) (++⁺ (value-text v) (ws-text wb))

-- THEOREM: no reply holds a raw control character other than whitespace.
@0 reply-chars : ∀ r → All TextChar (formatJSONChars (formatResponse r))
reply-chars r = jsonText-chars (reply-is-JSONText r)
