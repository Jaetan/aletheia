{-# OPTIONS --without-K #-}

-- B.3.d Layer 3 Commit 3c.2 — `parseRawAttrDefault` per-line construct
-- roundtrip.
--
-- `parseRawAttrDefault` consumes
--   `"BA_DEF_DEF_" ws string-lit ws raw-value ws? ";" newline (many newline)`
-- and yields a `RawAttrDefault { name = ... ; value = ... }`.  The line
-- ends with `;\n` (no leading space before `;`, unlike BA_DEF_'s ` ;\n`).
--
-- The roundtrip is parameterised on the `RawAttrValue` shape because
-- `parseRawAttrValue = (parseStringLit *> RavString) <|> (parseDecRat *>
-- RavDecRat)` accepts inputs from three emission shapes:
--   * `RavString s`               — emit `quoteStringLit-chars s`
--   * `RavDecRat d` (frac form)   — emit `showDecRat-dec-chars d`
--   * `RavDecRat (fromℤ z)`       — emit `showInt-chars z` (bare-int)
--
-- Layer 4 dispatches on `AttrValue` (AVString / AVFloat / AVInt /
-- AVEnum / AVHex) and picks the matching shape via `rawOfDefaultValue`
-- + the matching value-emit equality.

module Aletheia.DBC.TextParser.Properties.Attributes.Default where

open import Data.Bool using (Bool; true; false; T)
open import Data.Char using (Char)
open import Data.Char.Base using (_≈ᵇ_; isDigit)
open import Data.Integer using (ℤ; +_; -[1+_])
open import Data.List using (List; []; _∷_; length) renaming (_++_ to _++ₗ_)
open import Data.List.Properties using () renaming (++-assoc to ++ₗ-assoc; length-++ to length-++ₗ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (∃₂; _,_; Σ; _×_)
open import Data.String using (String; toList)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst; _≢_)

open import Aletheia.Parser.Combinators
  using (Position; Parser; ParseResult; mkResult; advancePosition; advancePositions;
         _>>=_; pure; _<|>_; _*>_; _<*_; string;
         char; many; satisfy)
open import Aletheia.DBC.DecRat using (DecRat; fromℤ)
open import Aletheia.DBC.Types using (AttrType)
open import Aletheia.DBC.Identifier using (Identifier)

open import Aletheia.DBC.TextParser.Attributes
  using (parseRawAttrDefault; parseRawAttrValue;
         RawAttrDefault; mkRawAttrDefault;
         RawAttrValue; RavString; RavDecRat)
open import Aletheia.DBC.TextParser.DecRatParse using (parseDecRat)
open import Aletheia.DBC.TextParser.Lexer
  using (parseWS; parseWSOpt; parseStringLit; parseNewline; isHSpace)

open import Aletheia.DBC.TextFormatter.Emitter
  using (quoteStringLit-chars; showDecRat-dec-chars; showInt-chars;
         showNat-chars; digitChar)

open import Aletheia.DBC.TextParser.Properties.Primitives using
  ( parseWS-one-space; parseStringLit-roundtrip
  ; alt-right-nothing; alt-left-just; bind-nothing
  ; string-success; string-*>-success)
open import Aletheia.DBC.TextParser.DecRatParse.Properties using
  ( bind-just-step
  ; SuffixStops; ∷-stop; []-stop
  ; advancePositions-++
  ; manyHelper-satisfy-exhaust-many
  ; parseDecRat-roundtrip-suffix
  ; parseDecRat-bareInt-roundtrip-suffix
  ; showNat-chars-head; digitChar-≢-dash
  ; showDecRat-chars-head-dash; showDecRat-chars-head-digit
  ; headOr)
open import Aletheia.DBC.TextParser.Properties.Preamble.Newline using
  ( isNewlineStart
  ; parseNewline-match-LF
  ; manyHelper-parseNewline-exhaust)

-- ============================================================================
-- parseStringLit failure on non-quote head
-- ============================================================================

private
  -- Generic lemma: parseStringLit fails when the head char is not '"'.
  parseStringLit-fail-on-non-quote : ∀ pos c rest
    → (c ≈ᵇ '"') ≡ false
    → parseStringLit pos (c ∷ rest) ≡ nothing
  parseStringLit-fail-on-non-quote pos c rest c-eq =
    bind-nothing (char '"')
      (λ _ → many (Aletheia.DBC.TextParser.Lexer.parseStringChar) >>= λ chars →
             char '"' >>= λ _ → pure (Data.String.fromList chars))
      pos (c ∷ rest)
      char-fails
    where
      open import Data.String using (fromList)
      char-fails : char '"' pos (c ∷ rest) ≡ nothing
      char-fails rewrite c-eq = refl

-- ============================================================================
-- parseRawAttrValue per-emit-shape roundtrips
-- ============================================================================

-- RavString: parseStringLit succeeds, alt-left-just lifts to parseRawAttrValue.
parseRawAttrValue-roundtrip-RavString :
  ∀ pos s suffix
  → SuffixStops (λ c → c ≈ᵇ '"') suffix
  → parseRawAttrValue pos (quoteStringLit-chars s ++ₗ suffix)
    ≡ just (mkResult (RavString s)
              (advancePositions pos (quoteStringLit-chars s))
              suffix)
parseRawAttrValue-roundtrip-RavString pos s suffix ss =
  alt-left-just
    (parseStringLit >>= λ s₁ → pure (RavString s₁))
    (parseDecRat    >>= λ d  → pure (RavDecRat d))
    pos (quoteStringLit-chars s ++ₗ suffix) _
    (bind-just-step parseStringLit (λ s₁ → pure (RavString s₁))
       pos (quoteStringLit-chars s ++ₗ suffix)
       s (advancePositions pos (quoteStringLit-chars s)) suffix
       (parseStringLit-roundtrip pos s suffix ss))

-- RavDecRat (frac form): parseStringLit fails on non-quote head, then
-- parseDecRat (frac wrapper) succeeds.
parseRawAttrValue-roundtrip-RavDecRatFrac :
  ∀ pos d suffix
  → SuffixStops isDigit suffix
  → ∀ c tail
  → showDecRat-dec-chars d ≡ c ∷ tail
  → (c ≈ᵇ '"') ≡ false
  → parseRawAttrValue pos (showDecRat-dec-chars d ++ₗ suffix)
    ≡ just (mkResult (RavDecRat d)
              (advancePositions pos (showDecRat-dec-chars d))
              suffix)
parseRawAttrValue-roundtrip-RavDecRatFrac pos d suffix ss-digit c tail head-eq c-not-quote =
  trans
    (alt-right-nothing
       (parseStringLit >>= λ s₁ → pure (RavString s₁))
       (parseDecRat    >>= λ d₁ → pure (RavDecRat d₁))
       pos (showDecRat-dec-chars d ++ₗ suffix)
       (bind-nothing parseStringLit (λ s₁ → pure (RavString s₁))
          pos (showDecRat-dec-chars d ++ₗ suffix)
          (subst (λ chars → parseStringLit pos (chars ++ₗ suffix) ≡ nothing)
                 (sym head-eq)
                 (parseStringLit-fail-on-non-quote pos c (tail ++ₗ suffix) c-not-quote))))
    (bind-just-step parseDecRat (λ d₁ → pure (RavDecRat d₁))
       pos (showDecRat-dec-chars d ++ₗ suffix)
       d (advancePositions pos (showDecRat-dec-chars d)) suffix
       (parseDecRat-roundtrip-suffix d pos suffix ss-digit))

-- RavDecRat (bare-int form, fromℤ z): parseStringLit fails, parseDecRat
-- (bare-int wrapper) succeeds; result value is `fromℤ z`.
parseRawAttrValue-roundtrip-RavDecRatBareInt :
  ∀ pos z suffix
  → SuffixStops isDigit suffix
  → '.' ≢ headOr suffix '_'
  → ∀ c tail
  → showInt-chars z ≡ c ∷ tail
  → (c ≈ᵇ '"') ≡ false
  → parseRawAttrValue pos (showInt-chars z ++ₗ suffix)
    ≡ just (mkResult (RavDecRat (fromℤ z))
              (advancePositions pos (showInt-chars z))
              suffix)
parseRawAttrValue-roundtrip-RavDecRatBareInt pos z suffix ss-digit not-dot c tail head-eq c-not-quote =
  trans
    (alt-right-nothing
       (parseStringLit >>= λ s₁ → pure (RavString s₁))
       (parseDecRat    >>= λ d₁ → pure (RavDecRat d₁))
       pos (showInt-chars z ++ₗ suffix)
       (bind-nothing parseStringLit (λ s₁ → pure (RavString s₁))
          pos (showInt-chars z ++ₗ suffix)
          (subst (λ chars → parseStringLit pos (chars ++ₗ suffix) ≡ nothing)
                 (sym head-eq)
                 (parseStringLit-fail-on-non-quote pos c (tail ++ₗ suffix) c-not-quote))))
    (bind-just-step parseDecRat (λ d₁ → pure (RavDecRat d₁))
       pos (showInt-chars z ++ₗ suffix)
       (fromℤ z) (advancePositions pos (showInt-chars z)) suffix
       (parseDecRat-bareInt-roundtrip-suffix z pos suffix ss-digit not-dot))

-- ============================================================================
-- Trace module for parseRawAttrDefault bind chain
-- ============================================================================

private
  module Trace (pos : Position) (name : String) (value-chars : List Char)
               (outer-suffix : List Char) where
    cs-name : List Char
    cs-name = quoteStringLit-chars name

    pos1 : Position  -- after string "BA_DEF_DEF_"
    pos1 = advancePositions pos (toList "BA_DEF_DEF_")

    pos2 : Position  -- after parseWS (1 space)
    pos2 = advancePosition pos1 ' '

    pos3 : Position  -- after parseStringLit
    pos3 = advancePositions pos2 cs-name

    pos4 : Position  -- after parseWS (1 space)
    pos4 = advancePosition pos3 ' '

    pos5 : Position  -- after parseRawAttrValue
    pos5 = advancePositions pos4 value-chars

    -- pos6 = pos5 (parseWSOpt consumes 0 spaces — head is ';')
    pos7 : Position  -- after char ';'
    pos7 = advancePosition pos5 ';'

    pos8 : Position  -- after parseNewline
    pos8 = advancePosition pos7 '\n'

    rest-tail : List Char
    rest-tail = ';' ∷ '\n' ∷ outer-suffix

    body-after-keyword : List Char
    body-after-keyword =
      ' ' ∷ cs-name ++ₗ ' ' ∷ value-chars ++ₗ rest-tail

    body-after-WS1 : List Char
    body-after-WS1 = cs-name ++ₗ ' ' ∷ value-chars ++ₗ rest-tail

    body-after-name : List Char
    body-after-name = ' ' ∷ value-chars ++ₗ rest-tail

    body-after-WS2 : List Char
    body-after-WS2 = value-chars ++ₗ rest-tail

    body-after-value : List Char
    body-after-value = rest-tail

    body-after-WSOpt : List Char
    body-after-WSOpt = ';' ∷ '\n' ∷ outer-suffix

    body-after-semi : List Char
    body-after-semi = '\n' ∷ outer-suffix

    body-after-NL : List Char
    body-after-NL = outer-suffix

-- ============================================================================
-- Parameterised after-keyword bind chain
-- ============================================================================

parseRawAttrDefault-after-keyword :
  ∀ pos (name : String) (raw-value : RawAttrValue) (value-chars : List Char)
    (outer-suffix : List Char)
  → SuffixStops isNewlineStart outer-suffix
  → SuffixStops isHSpace (value-chars ++ₗ ';' ∷ '\n' ∷ outer-suffix)
  → let open Trace pos name value-chars outer-suffix in
    parseRawAttrValue pos4 body-after-WS2
      ≡ just (mkResult raw-value pos5 body-after-value)
  → parseRawAttrDefault pos
      ('B' ∷ 'A' ∷ '_' ∷ 'D' ∷ 'E' ∷ 'F' ∷ '_' ∷ 'D' ∷ 'E' ∷ 'F' ∷ '_' ∷
        Trace.body-after-keyword pos name value-chars outer-suffix)
    ≡ just (mkResult (mkRawAttrDefault name raw-value)
              (Trace.pos8 pos name value-chars outer-suffix)
              outer-suffix)
parseRawAttrDefault-after-keyword pos name raw-value value-chars outer-suffix
  ss-NL value-stops-isHSpace value-eq =
    -- Step 1: string "BA_DEF_DEF_"
    trans (bind-just-step (string "BA_DEF_DEF_")
           (λ _ → parseWS >>= λ _ →
                  parseStringLit >>= λ n →
                  parseWS >>= λ _ →
                  parseRawAttrValue >>= λ v →
                  parseWSOpt >>= λ _ →
                  char ';' >>= λ _ →
                  parseNewline >>= λ _ →
                  many parseNewline >>= λ _ →
                  pure (mkRawAttrDefault n v))
           pos
           ('B' ∷ 'A' ∷ '_' ∷ 'D' ∷ 'E' ∷ 'F' ∷ '_' ∷ 'D' ∷ 'E' ∷ 'F' ∷ '_' ∷
            body-after-keyword)
           "BA_DEF_DEF_" pos1 body-after-keyword
           (string-success pos "BA_DEF_DEF_" body-after-keyword))
    -- Step 2: parseWS consumes ' '.
    (trans (bind-just-step parseWS
              (λ _ → parseStringLit >>= λ n →
                     parseWS >>= λ _ →
                     parseRawAttrValue >>= λ v →
                     parseWSOpt >>= λ _ →
                     char ';' >>= λ _ →
                     parseNewline >>= λ _ →
                     many parseNewline >>= λ _ →
                     pure (mkRawAttrDefault n v))
              pos1 body-after-keyword
              (' ' ∷ []) pos2 body-after-WS1
              (parseWS-one-space pos1 body-after-WS1
                qsl-stops-isHSpace))
    -- Step 3: parseStringLit reads name.
    (trans (bind-just-step parseStringLit
              (λ n → parseWS >>= λ _ →
                     parseRawAttrValue >>= λ v →
                     parseWSOpt >>= λ _ →
                     char ';' >>= λ _ →
                     parseNewline >>= λ _ →
                     many parseNewline >>= λ _ →
                     pure (mkRawAttrDefault n v))
              pos2 body-after-WS1
              name pos3 body-after-name
              (parseStringLit-roundtrip pos2 name body-after-name (∷-stop refl)))
    -- Step 4: parseWS consumes ' '.
    (trans (bind-just-step parseWS
              (λ _ → parseRawAttrValue >>= λ v →
                     parseWSOpt >>= λ _ →
                     char ';' >>= λ _ →
                     parseNewline >>= λ _ →
                     many parseNewline >>= λ _ →
                     pure (mkRawAttrDefault name v))
              pos3 body-after-name
              (' ' ∷ []) pos4 body-after-WS2
              (parseWS-one-space pos3 body-after-WS2 value-stops-isHSpace))
    -- Step 5: parseRawAttrValue (caller's witness).
    (trans (bind-just-step parseRawAttrValue
              (λ v → parseWSOpt >>= λ _ →
                     char ';' >>= λ _ →
                     parseNewline >>= λ _ →
                     many parseNewline >>= λ _ →
                     pure (mkRawAttrDefault name v))
              pos4 body-after-WS2
              raw-value pos5 body-after-value
              value-eq)
    -- Step 6: parseWSOpt consumes 0 spaces (head ';' is non-hspace).
    (trans (bind-just-step parseWSOpt
              (λ _ → char ';' >>= λ _ →
                     parseNewline >>= λ _ →
                     many parseNewline >>= λ _ →
                     pure (mkRawAttrDefault name raw-value))
              pos5 body-after-value
              [] pos5 body-after-WSOpt
              (parseWSOpt-empty pos5 outer-suffix))
    -- Step 7: char ';'.
    (trans (bind-just-step (char ';')
              (λ _ → parseNewline >>= λ _ →
                     many parseNewline >>= λ _ →
                     pure (mkRawAttrDefault name raw-value))
              pos5 body-after-WSOpt
              ';' pos7 body-after-semi
              refl)
    -- Step 8: parseNewline.
    (trans (bind-just-step parseNewline
              (λ _ → many parseNewline >>= λ _ →
                     pure (mkRawAttrDefault name raw-value))
              pos7 body-after-semi
              '\n' pos8 body-after-NL
              (parseNewline-match-LF pos7 outer-suffix))
    -- Step 9: many parseNewline consumes 0 newlines.
    (trans (bind-just-step (many parseNewline)
              (λ _ → pure (mkRawAttrDefault name raw-value))
              pos8 body-after-NL
              [] pos8 outer-suffix
              (manyHelper-parseNewline-exhaust pos8 outer-suffix
                (length outer-suffix) ss-NL))
      refl))))))))
  where
    open Trace pos name value-chars outer-suffix

    qsl-stops-isHSpace :
      SuffixStops isHSpace (quoteStringLit-chars name ++ₗ
        ' ' ∷ value-chars ++ₗ ';' ∷ '\n' ∷ outer-suffix)
    qsl-stops-isHSpace = ∷-stop refl

    parseWSOpt-empty :
      ∀ (p : Position) (rest : List Char) →
      parseWSOpt p (';' ∷ '\n' ∷ rest)
      ≡ just (mkResult [] p (';' ∷ '\n' ∷ rest))
    parseWSOpt-empty p rest =
      manyHelper-satisfy-exhaust-many isHSpace
        p [] (';' ∷ '\n' ∷ rest)
        AllList.[]
        (∷-stop refl)
      where
        import Data.List.Relation.Unary.All as AllList


-- ============================================================================
-- Top-level dispatcher cases — RavString / RavDecRatFrac / RavDecRatBareInt
-- ============================================================================

-- For each emit-shape, the top-level proof composes
-- `parseRawAttrDefault-after-keyword` with the matching
-- `parseRawAttrValue-roundtrip-X` witness and the input-list-eq /
-- pos-fold-cong adjustments mirroring `parseAttrDef-roundtrip`'s pattern.

-- The shape lemma `emitAttrDefault-shape-X`-style is inlined here as
-- `++ₗ-assoc` chains because the formatter `emitAttrDefault-chars
-- defs d` is typed (takes AttrDefault, threads defs for ENUM lookup).
-- 3c.2 ships the raw-level roundtrip; Layer 4 / 3c.5 will bridge the
-- typed formatter via `Common.refineDefaultValue-rawOfDefault-roundtrip`.

private
  -- digitChar d ≢ '"' for d < 10.
  digitChar-not-quote : ∀ d → d Data.Nat.< 10 → (digitChar d ≈ᵇ '"') ≡ false
  digitChar-not-quote 0 _ = refl
  digitChar-not-quote 1 _ = refl
  digitChar-not-quote 2 _ = refl
  digitChar-not-quote 3 _ = refl
  digitChar-not-quote 4 _ = refl
  digitChar-not-quote 5 _ = refl
  digitChar-not-quote 6 _ = refl
  digitChar-not-quote 7 _ = refl
  digitChar-not-quote 8 _ = refl
  digitChar-not-quote 9 _ = refl
  digitChar-not-quote (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc _))))))))))
    (Data.Nat.s≤s (Data.Nat.s≤s (Data.Nat.s≤s (Data.Nat.s≤s (Data.Nat.s≤s
      (Data.Nat.s≤s (Data.Nat.s≤s (Data.Nat.s≤s (Data.Nat.s≤s (Data.Nat.s≤s ()))))))))))

  -- digitChar d is not hspace.
  digitChar-not-isHSpace : ∀ d → isHSpace (digitChar d) ≡ false
  digitChar-not-isHSpace 0 = refl
  digitChar-not-isHSpace 1 = refl
  digitChar-not-isHSpace 2 = refl
  digitChar-not-isHSpace 3 = refl
  digitChar-not-isHSpace 4 = refl
  digitChar-not-isHSpace 5 = refl
  digitChar-not-isHSpace 6 = refl
  digitChar-not-isHSpace 7 = refl
  digitChar-not-isHSpace 8 = refl
  digitChar-not-isHSpace 9 = refl
  digitChar-not-isHSpace (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc _)))))))))) = refl

  -- showInt-chars head non-quote / non-hspace.
  showInt-chars-head : ∀ z →
    ∃₂ λ x tail → showInt-chars z ≡ x ∷ tail × (x ≈ᵇ '"') ≡ false × isHSpace x ≡ false
  showInt-chars-head (+ n) with showNat-chars-head n
  ... | d , tail , d<10 , eq =
        digitChar d , tail , eq , digitChar-not-quote d d<10 , digitChar-not-isHSpace d
  showInt-chars-head -[1+ _ ] = '-' , _ , refl , refl , refl

  -- showDecRat-dec-chars head non-quote / non-hspace.
  showDecRat-chars-head : ∀ d →
    ∃₂ λ x tail → showDecRat-dec-chars d ≡ x ∷ tail × (x ≈ᵇ '"') ≡ false × isHSpace x ≡ false
  showDecRat-chars-head (Aletheia.DBC.DecRat.mkDecRat (+ zero) a b cx)
    with showDecRat-chars-head-digit zero a b cx
  ... | k , tail , k<10 , eq =
        digitChar k , tail , eq , digitChar-not-quote k k<10 , digitChar-not-isHSpace k
  showDecRat-chars-head (Aletheia.DBC.DecRat.mkDecRat (+ suc n) a b cx)
    with showDecRat-chars-head-digit (suc n) a b cx
  ... | k , tail , k<10 , eq =
        digitChar k , tail , eq , digitChar-not-quote k k<10 , digitChar-not-isHSpace k
  showDecRat-chars-head (Aletheia.DBC.DecRat.mkDecRat -[1+ n ] a b cx)
    with showDecRat-chars-head-dash n a b cx
  ... | tail , eq = '-' , tail , eq , refl , refl

  -- SuffixStops witness for the value-chars-prefixed input at step 4.
  -- Head is the first char of value-chars (which is non-empty for all
  -- 3 emit shapes); precondition discharged via showInt/showDecRat
  -- head witnesses + ∷-stop.
  value-stops-isHSpace-RavString : ∀ s outer-suffix
    → SuffixStops isHSpace (quoteStringLit-chars s ++ₗ ';' ∷ '\n' ∷ outer-suffix)
  value-stops-isHSpace-RavString _ _ = ∷-stop refl

  value-stops-isHSpace-RavDecRatFrac : ∀ d outer-suffix
    → SuffixStops isHSpace (showDecRat-dec-chars d ++ₗ ';' ∷ '\n' ∷ outer-suffix)
  value-stops-isHSpace-RavDecRatFrac d outer-suffix
    with showDecRat-chars-head d
  ... | x , tail , eq , _ , x-not-hsp =
    subst (λ chars → SuffixStops isHSpace (chars ++ₗ ';' ∷ '\n' ∷ outer-suffix))
          (sym eq) (∷-stop x-not-hsp)

  value-stops-isHSpace-RavDecRatBareInt : ∀ z outer-suffix
    → SuffixStops isHSpace (showInt-chars z ++ₗ ';' ∷ '\n' ∷ outer-suffix)
  value-stops-isHSpace-RavDecRatBareInt z outer-suffix
    with showInt-chars-head z
  ... | x , tail , eq , _ , x-not-hsp =
    subst (λ chars → SuffixStops isHSpace (chars ++ₗ ';' ∷ '\n' ∷ outer-suffix))
          (sym eq) (∷-stop x-not-hsp)


-- ============================================================================
-- Top-level dispatcher: 3 cases by emit shape
-- ============================================================================

-- RavString: emit `quoteStringLit-chars s` for the value.
parseRawAttrDefault-roundtrip-RavString :
  ∀ pos (name : String) (s : String) (outer-suffix : List Char)
  → SuffixStops isNewlineStart outer-suffix
  → parseRawAttrDefault pos
      (toList "BA_DEF_DEF_ " ++ₗ quoteStringLit-chars name ++ₗ
        ' ' ∷ quoteStringLit-chars s ++ₗ toList ";\n" ++ₗ outer-suffix)
    ≡ just (mkResult (mkRawAttrDefault name (RavString s))
              (Trace.pos8 pos name (quoteStringLit-chars s) outer-suffix)
              outer-suffix)
parseRawAttrDefault-roundtrip-RavString pos name s outer-suffix ss-NL =
  trans input-eq
    (parseRawAttrDefault-after-keyword pos name (RavString s)
      (quoteStringLit-chars s) outer-suffix ss-NL
      (value-stops-isHSpace-RavString s outer-suffix)
      value-eq)
  where
    open Trace pos name (quoteStringLit-chars s) outer-suffix
    -- Reshape input: ((BA_DEF_DEF_ ) ++ qsl-name ++ ' ' ∷ qsl-s ++ ";\n") ++ outer
    -- ≡ 'B' ∷ 'A' ∷ ... ∷ ' ' ∷ qsl-name ++ ' ' ∷ qsl-s ++ ';' ∷ '\n' ∷ outer
    input-eq :
      parseRawAttrDefault pos
        (toList "BA_DEF_DEF_ " ++ₗ quoteStringLit-chars name ++ₗ
          ' ' ∷ quoteStringLit-chars s ++ₗ toList ";\n" ++ₗ outer-suffix)
      ≡ parseRawAttrDefault pos
        ('B' ∷ 'A' ∷ '_' ∷ 'D' ∷ 'E' ∷ 'F' ∷ '_' ∷ 'D' ∷ 'E' ∷ 'F' ∷ '_' ∷
          body-after-keyword)
    input-eq = refl

    value-eq :
      parseRawAttrValue pos4
        (quoteStringLit-chars s ++ₗ ';' ∷ '\n' ∷ outer-suffix)
      ≡ just (mkResult (RavString s) pos5 (';' ∷ '\n' ∷ outer-suffix))
    value-eq = parseRawAttrValue-roundtrip-RavString pos4 s
                 (';' ∷ '\n' ∷ outer-suffix) (∷-stop refl)

-- RavDecRat (frac form): emit `showDecRat-dec-chars d`.
parseRawAttrDefault-roundtrip-RavDecRatFrac :
  ∀ pos (name : String) (d : DecRat) (outer-suffix : List Char)
  → SuffixStops isNewlineStart outer-suffix
  → parseRawAttrDefault pos
      (toList "BA_DEF_DEF_ " ++ₗ quoteStringLit-chars name ++ₗ
        ' ' ∷ showDecRat-dec-chars d ++ₗ toList ";\n" ++ₗ outer-suffix)
    ≡ just (mkResult (mkRawAttrDefault name (RavDecRat d))
              (Trace.pos8 pos name (showDecRat-dec-chars d) outer-suffix)
              outer-suffix)
parseRawAttrDefault-roundtrip-RavDecRatFrac pos name d outer-suffix ss-NL
  with showDecRat-chars-head d
... | c , tail , head-eq , c-not-quote , _ =
  trans input-eq
    (parseRawAttrDefault-after-keyword pos name (RavDecRat d)
      (showDecRat-dec-chars d) outer-suffix ss-NL
      (value-stops-isHSpace-RavDecRatFrac d outer-suffix)
      value-eq)
  where
    open Trace pos name (showDecRat-dec-chars d) outer-suffix
    input-eq :
      parseRawAttrDefault pos
        (toList "BA_DEF_DEF_ " ++ₗ quoteStringLit-chars name ++ₗ
          ' ' ∷ showDecRat-dec-chars d ++ₗ toList ";\n" ++ₗ outer-suffix)
      ≡ parseRawAttrDefault pos
        ('B' ∷ 'A' ∷ '_' ∷ 'D' ∷ 'E' ∷ 'F' ∷ '_' ∷ 'D' ∷ 'E' ∷ 'F' ∷ '_' ∷
          body-after-keyword)
    input-eq = refl

    value-eq :
      parseRawAttrValue pos4
        (showDecRat-dec-chars d ++ₗ ';' ∷ '\n' ∷ outer-suffix)
      ≡ just (mkResult (RavDecRat d) pos5 (';' ∷ '\n' ∷ outer-suffix))
    value-eq = parseRawAttrValue-roundtrip-RavDecRatFrac pos4 d
                 (';' ∷ '\n' ∷ outer-suffix) (∷-stop refl)
                 c tail head-eq c-not-quote

-- RavDecRat (bare-int form, fromℤ z): emit `showInt-chars z`.
parseRawAttrDefault-roundtrip-RavDecRatBareInt :
  ∀ pos (name : String) (z : ℤ) (outer-suffix : List Char)
  → SuffixStops isNewlineStart outer-suffix
  → parseRawAttrDefault pos
      (toList "BA_DEF_DEF_ " ++ₗ quoteStringLit-chars name ++ₗ
        ' ' ∷ showInt-chars z ++ₗ toList ";\n" ++ₗ outer-suffix)
    ≡ just (mkResult (mkRawAttrDefault name (RavDecRat (fromℤ z)))
              (Trace.pos8 pos name (showInt-chars z) outer-suffix)
              outer-suffix)
parseRawAttrDefault-roundtrip-RavDecRatBareInt pos name z outer-suffix ss-NL
  with showInt-chars-head z
... | c , tail , head-eq , c-not-quote , _ =
  trans input-eq
    (parseRawAttrDefault-after-keyword pos name (RavDecRat (fromℤ z))
      (showInt-chars z) outer-suffix ss-NL
      (value-stops-isHSpace-RavDecRatBareInt z outer-suffix)
      value-eq)
  where
    open Trace pos name (showInt-chars z) outer-suffix
    input-eq :
      parseRawAttrDefault pos
        (toList "BA_DEF_DEF_ " ++ₗ quoteStringLit-chars name ++ₗ
          ' ' ∷ showInt-chars z ++ₗ toList ";\n" ++ₗ outer-suffix)
      ≡ parseRawAttrDefault pos
        ('B' ∷ 'A' ∷ '_' ∷ 'D' ∷ 'E' ∷ 'F' ∷ '_' ∷ 'D' ∷ 'E' ∷ 'F' ∷ '_' ∷
          body-after-keyword)
    input-eq = refl

    value-eq :
      parseRawAttrValue pos4
        (showInt-chars z ++ₗ ';' ∷ '\n' ∷ outer-suffix)
      ≡ just (mkResult (RavDecRat (fromℤ z)) pos5 (';' ∷ '\n' ∷ outer-suffix))
    value-eq = parseRawAttrValue-roundtrip-RavDecRatBareInt pos4 z
                 (';' ∷ '\n' ∷ outer-suffix) (∷-stop refl) (λ ())
                 c tail head-eq c-not-quote
