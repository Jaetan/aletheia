{-# OPTIONS --without-K #-}

-- B.3.d Layer 3 Commit 3c.3 — `parseRawAttrAssign` × ATgtNetwork
-- per-line construct roundtrips (3 emit shapes).
--
-- ATgtNetwork is the fall-through branch of `parseStandardAttrTarget
-- <|> pure ATgtNetwork`.  The 4-fold `<|>` chain (parseNodeTgt /
-- parseMsgTgt / parseSigTgt / parseEvTgt) fails on any of the 3
-- value-leading char classes (`'"'` / `'-'` / decimal digit), and the
-- outer `<|>` falls through to `pure ATgtNetwork`.
--
-- Per-target sub-files for the other 4 standard targets and 2 rel
-- targets cascade beside this one (see facade
-- `Properties/Attributes/Assign.agda`).

module Aletheia.DBC.TextParser.Properties.Attributes.Assign.Network where

open import Data.Bool using (Bool; true; false; T)
open import Data.Char using (Char)
open import Data.Char.Base using (_≈ᵇ_; isDigit)
open import Data.Integer using (ℤ; +_; -[1+_])
open import Data.List using (List; []; _∷_; length) renaming (_++_ to _++ₗ_)
open import Data.List.Properties using () renaming (++-assoc to ++ₗ-assoc; length-++ to length-++ₗ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (∃₂; _,_; Σ; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.String using (String; toList)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst; _≢_)

open import Aletheia.Parser.Combinators
  using (Position; Parser; ParseResult; mkResult; advancePosition; advancePositions;
         _>>=_; pure; _<|>_; _*>_; _<*_; string;
         char; many; satisfy; fail)
open import Aletheia.DBC.DecRat using (DecRat; fromℤ)
open import Aletheia.DBC.Types using
  ( AttrTarget; ATgtNetwork; ATgtNode; ATgtMessage; ATgtSignal; ATgtEnvVar
  ; ATgtNodeMsg; ATgtNodeSig)
open import Aletheia.DBC.Identifier using (Identifier)

open import Aletheia.DBC.TextParser.Attributes
  using (parseRawAttrAssign; parseRawAttrValue;
         RawAttrAssign; mkRawAttrAssign;
         RawAttrValue; RavString; RavDecRat;
         parseStandardAttrTarget;
         parseNodeTgt; parseMsgTgt; parseSigTgt; parseEvTgt)
open import Aletheia.DBC.TextParser.Lexer
  using (parseWS; parseWSOpt; parseStringLit; parseNewline;
         isHSpace)

open import Aletheia.DBC.TextFormatter.Emitter
  using (quoteStringLit-chars; showDecRat-dec-chars; showInt-chars; digitChar)

open import Aletheia.DBC.TextParser.Properties.Primitives using
  ( parseWS-one-space; parseStringLit-roundtrip
  ; alt-right-nothing; alt-left-just; bind-nothing
  ; string-success; string-*>-success)
open import Aletheia.DBC.TextParser.DecRatParse.Properties using
  ( bind-just-step
  ; SuffixStops; ∷-stop; []-stop
  ; manyHelper-satisfy-exhaust-many
  ; parseDecRat-roundtrip-suffix
  ; parseDecRat-bareInt-roundtrip-suffix)
open import Aletheia.DBC.TextParser.Properties.Preamble.Newline using
  ( isNewlineStart
  ; parseNewline-match-LF
  ; manyHelper-parseNewline-exhaust)
open import Aletheia.DBC.TextParser.Properties.Attributes.Default using
  ( parseRawAttrValue-roundtrip-RavString
  ; parseRawAttrValue-roundtrip-RavDecRatFrac
  ; parseRawAttrValue-roundtrip-RavDecRatBareInt)
open import Aletheia.DBC.TextParser.Properties.Attributes.Assign.Common using
  ( showInt-chars-head-classify; showDecRat-chars-head-classify
  ; value-stops-isHSpace-RavString
  ; value-stops-isHSpace-RavDecRatFrac
  ; value-stops-isHSpace-RavDecRatBareInt)

-- ============================================================================
-- parseStandardAttrTarget failure on value-leading chars
-- ============================================================================
--
-- For ATgtNetwork case, the input after parseStringLit + parseWS starts
-- with the value's first char ('"', '-', or a digit), not a target
-- keyword.  Each parseXTgt fails on `string "X_"` for the wrong head,
-- and the 3-fold `<|>` collapses to nothing.

private
  parseNodeTgt-fails-on-quote : ∀ pos rest →
    parseNodeTgt pos ('"' ∷ rest) ≡ nothing
  parseNodeTgt-fails-on-quote _ _ = refl

  parseMsgTgt-fails-on-quote : ∀ pos rest →
    parseMsgTgt pos ('"' ∷ rest) ≡ nothing
  parseMsgTgt-fails-on-quote _ _ = refl

  parseSigTgt-fails-on-quote : ∀ pos rest →
    parseSigTgt pos ('"' ∷ rest) ≡ nothing
  parseSigTgt-fails-on-quote _ _ = refl

  parseEvTgt-fails-on-quote : ∀ pos rest →
    parseEvTgt pos ('"' ∷ rest) ≡ nothing
  parseEvTgt-fails-on-quote _ _ = refl

  parseNodeTgt-fails-on-dash : ∀ pos rest →
    parseNodeTgt pos ('-' ∷ rest) ≡ nothing
  parseNodeTgt-fails-on-dash _ _ = refl

  parseMsgTgt-fails-on-dash : ∀ pos rest →
    parseMsgTgt pos ('-' ∷ rest) ≡ nothing
  parseMsgTgt-fails-on-dash _ _ = refl

  parseSigTgt-fails-on-dash : ∀ pos rest →
    parseSigTgt pos ('-' ∷ rest) ≡ nothing
  parseSigTgt-fails-on-dash _ _ = refl

  parseEvTgt-fails-on-dash : ∀ pos rest →
    parseEvTgt pos ('-' ∷ rest) ≡ nothing
  parseEvTgt-fails-on-dash _ _ = refl

  parseNodeTgt-fails-on-digit : ∀ d pos rest →
    d Data.Nat.< 10 → parseNodeTgt pos (digitChar d ∷ rest) ≡ nothing
  parseNodeTgt-fails-on-digit 0 _ _ _ = refl
  parseNodeTgt-fails-on-digit 1 _ _ _ = refl
  parseNodeTgt-fails-on-digit 2 _ _ _ = refl
  parseNodeTgt-fails-on-digit 3 _ _ _ = refl
  parseNodeTgt-fails-on-digit 4 _ _ _ = refl
  parseNodeTgt-fails-on-digit 5 _ _ _ = refl
  parseNodeTgt-fails-on-digit 6 _ _ _ = refl
  parseNodeTgt-fails-on-digit 7 _ _ _ = refl
  parseNodeTgt-fails-on-digit 8 _ _ _ = refl
  parseNodeTgt-fails-on-digit 9 _ _ _ = refl
  parseNodeTgt-fails-on-digit (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc _))))))))))
    _ _ (Data.Nat.s≤s (Data.Nat.s≤s (Data.Nat.s≤s (Data.Nat.s≤s (Data.Nat.s≤s
      (Data.Nat.s≤s (Data.Nat.s≤s (Data.Nat.s≤s (Data.Nat.s≤s (Data.Nat.s≤s ()))))))))))

  parseMsgTgt-fails-on-digit : ∀ d pos rest →
    d Data.Nat.< 10 → parseMsgTgt pos (digitChar d ∷ rest) ≡ nothing
  parseMsgTgt-fails-on-digit 0 _ _ _ = refl
  parseMsgTgt-fails-on-digit 1 _ _ _ = refl
  parseMsgTgt-fails-on-digit 2 _ _ _ = refl
  parseMsgTgt-fails-on-digit 3 _ _ _ = refl
  parseMsgTgt-fails-on-digit 4 _ _ _ = refl
  parseMsgTgt-fails-on-digit 5 _ _ _ = refl
  parseMsgTgt-fails-on-digit 6 _ _ _ = refl
  parseMsgTgt-fails-on-digit 7 _ _ _ = refl
  parseMsgTgt-fails-on-digit 8 _ _ _ = refl
  parseMsgTgt-fails-on-digit 9 _ _ _ = refl
  parseMsgTgt-fails-on-digit (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc _))))))))))
    _ _ (Data.Nat.s≤s (Data.Nat.s≤s (Data.Nat.s≤s (Data.Nat.s≤s (Data.Nat.s≤s
      (Data.Nat.s≤s (Data.Nat.s≤s (Data.Nat.s≤s (Data.Nat.s≤s (Data.Nat.s≤s ()))))))))))

  parseSigTgt-fails-on-digit : ∀ d pos rest →
    d Data.Nat.< 10 → parseSigTgt pos (digitChar d ∷ rest) ≡ nothing
  parseSigTgt-fails-on-digit 0 _ _ _ = refl
  parseSigTgt-fails-on-digit 1 _ _ _ = refl
  parseSigTgt-fails-on-digit 2 _ _ _ = refl
  parseSigTgt-fails-on-digit 3 _ _ _ = refl
  parseSigTgt-fails-on-digit 4 _ _ _ = refl
  parseSigTgt-fails-on-digit 5 _ _ _ = refl
  parseSigTgt-fails-on-digit 6 _ _ _ = refl
  parseSigTgt-fails-on-digit 7 _ _ _ = refl
  parseSigTgt-fails-on-digit 8 _ _ _ = refl
  parseSigTgt-fails-on-digit 9 _ _ _ = refl
  parseSigTgt-fails-on-digit (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc _))))))))))
    _ _ (Data.Nat.s≤s (Data.Nat.s≤s (Data.Nat.s≤s (Data.Nat.s≤s (Data.Nat.s≤s
      (Data.Nat.s≤s (Data.Nat.s≤s (Data.Nat.s≤s (Data.Nat.s≤s (Data.Nat.s≤s ()))))))))))

  parseEvTgt-fails-on-digit : ∀ d pos rest →
    d Data.Nat.< 10 → parseEvTgt pos (digitChar d ∷ rest) ≡ nothing
  parseEvTgt-fails-on-digit 0 _ _ _ = refl
  parseEvTgt-fails-on-digit 1 _ _ _ = refl
  parseEvTgt-fails-on-digit 2 _ _ _ = refl
  parseEvTgt-fails-on-digit 3 _ _ _ = refl
  parseEvTgt-fails-on-digit 4 _ _ _ = refl
  parseEvTgt-fails-on-digit 5 _ _ _ = refl
  parseEvTgt-fails-on-digit 6 _ _ _ = refl
  parseEvTgt-fails-on-digit 7 _ _ _ = refl
  parseEvTgt-fails-on-digit 8 _ _ _ = refl
  parseEvTgt-fails-on-digit 9 _ _ _ = refl
  parseEvTgt-fails-on-digit (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc _))))))))))
    _ _ (Data.Nat.s≤s (Data.Nat.s≤s (Data.Nat.s≤s (Data.Nat.s≤s (Data.Nat.s≤s
      (Data.Nat.s≤s (Data.Nat.s≤s (Data.Nat.s≤s (Data.Nat.s≤s (Data.Nat.s≤s ()))))))))))

  -- Compose: parseStandardAttrTarget = ((parseNodeTgt <|> parseMsgTgt)
  -- <|> parseSigTgt) <|> parseEvTgt (left-associative via `infixl 3`)
  -- fails on '"'/'-'/digit head.

  parseStandardAttrTarget-fails-on-quote : ∀ pos rest →
    parseStandardAttrTarget pos ('"' ∷ rest) ≡ nothing
  parseStandardAttrTarget-fails-on-quote pos rest =
    trans (alt-right-nothing
            ((parseNodeTgt <|> parseMsgTgt) <|> parseSigTgt)
            parseEvTgt pos ('"' ∷ rest)
            (trans (alt-right-nothing
                     (parseNodeTgt <|> parseMsgTgt)
                     parseSigTgt pos ('"' ∷ rest)
                     (trans (alt-right-nothing
                              parseNodeTgt parseMsgTgt pos ('"' ∷ rest)
                              (parseNodeTgt-fails-on-quote pos rest))
                            (parseMsgTgt-fails-on-quote pos rest)))
                   (parseSigTgt-fails-on-quote pos rest)))
          (parseEvTgt-fails-on-quote pos rest)

  parseStandardAttrTarget-fails-on-dash : ∀ pos rest →
    parseStandardAttrTarget pos ('-' ∷ rest) ≡ nothing
  parseStandardAttrTarget-fails-on-dash pos rest =
    trans (alt-right-nothing
            ((parseNodeTgt <|> parseMsgTgt) <|> parseSigTgt)
            parseEvTgt pos ('-' ∷ rest)
            (trans (alt-right-nothing
                     (parseNodeTgt <|> parseMsgTgt)
                     parseSigTgt pos ('-' ∷ rest)
                     (trans (alt-right-nothing
                              parseNodeTgt parseMsgTgt pos ('-' ∷ rest)
                              (parseNodeTgt-fails-on-dash pos rest))
                            (parseMsgTgt-fails-on-dash pos rest)))
                   (parseSigTgt-fails-on-dash pos rest)))
          (parseEvTgt-fails-on-dash pos rest)

  parseStandardAttrTarget-fails-on-digit : ∀ d pos rest →
    d Data.Nat.< 10 →
    parseStandardAttrTarget pos (digitChar d ∷ rest) ≡ nothing
  parseStandardAttrTarget-fails-on-digit d pos rest d<10 =
    trans (alt-right-nothing
            ((parseNodeTgt <|> parseMsgTgt) <|> parseSigTgt)
            parseEvTgt pos (digitChar d ∷ rest)
            (trans (alt-right-nothing
                     (parseNodeTgt <|> parseMsgTgt)
                     parseSigTgt pos (digitChar d ∷ rest)
                     (trans (alt-right-nothing
                              parseNodeTgt parseMsgTgt pos (digitChar d ∷ rest)
                              (parseNodeTgt-fails-on-digit d pos rest d<10))
                            (parseMsgTgt-fails-on-digit d pos rest d<10)))
                   (parseSigTgt-fails-on-digit d pos rest d<10)))
          (parseEvTgt-fails-on-digit d pos rest d<10)

-- ============================================================================
-- (parseStandardAttrTarget <|> pure ATgtNetwork) on value-leading chars
-- ============================================================================

private
  optStandardScope-Network-on-quote : ∀ pos rest →
    (parseStandardAttrTarget <|> pure ATgtNetwork) pos ('"' ∷ rest)
    ≡ just (mkResult ATgtNetwork pos ('"' ∷ rest))
  optStandardScope-Network-on-quote pos rest =
    trans (alt-right-nothing parseStandardAttrTarget
             (pure ATgtNetwork) pos ('"' ∷ rest)
             (parseStandardAttrTarget-fails-on-quote pos rest))
          refl

  optStandardScope-Network-on-dash : ∀ pos rest →
    (parseStandardAttrTarget <|> pure ATgtNetwork) pos ('-' ∷ rest)
    ≡ just (mkResult ATgtNetwork pos ('-' ∷ rest))
  optStandardScope-Network-on-dash pos rest =
    trans (alt-right-nothing parseStandardAttrTarget
             (pure ATgtNetwork) pos ('-' ∷ rest)
             (parseStandardAttrTarget-fails-on-dash pos rest))
          refl

  optStandardScope-Network-on-digit : ∀ d pos rest →
    d Data.Nat.< 10 →
    (parseStandardAttrTarget <|> pure ATgtNetwork) pos (digitChar d ∷ rest)
    ≡ just (mkResult ATgtNetwork pos (digitChar d ∷ rest))
  optStandardScope-Network-on-digit d pos rest d<10 =
    trans (alt-right-nothing parseStandardAttrTarget
             (pure ATgtNetwork) pos (digitChar d ∷ rest)
             (parseStandardAttrTarget-fails-on-digit d pos rest d<10))
          refl

  -- target-eq helper: given a head classification (digit or dash) for
  -- the first char of value-chars, optStandardScope-Network falls
  -- through.  Shared by frac and bareInt cases.
  optStandardScope-Network-on-classified :
    ∀ pos x tail outer-suffix
    → ((Σ ℕ λ k → x ≡ digitChar k × k Data.Nat.< 10) ⊎ (x ≡ '-'))
    → (parseStandardAttrTarget <|> pure ATgtNetwork) pos
        (x ∷ tail ++ₗ ';' ∷ '\n' ∷ outer-suffix)
      ≡ just (mkResult ATgtNetwork pos
                (x ∷ tail ++ₗ ';' ∷ '\n' ∷ outer-suffix))
  optStandardScope-Network-on-classified pos x tail outer-suffix (inj₁ (k , x≡dig , k<10)) =
    subst (λ y → (parseStandardAttrTarget <|> pure ATgtNetwork) pos
                    (y ∷ tail ++ₗ ';' ∷ '\n' ∷ outer-suffix)
                  ≡ just (mkResult ATgtNetwork pos
                            (y ∷ tail ++ₗ ';' ∷ '\n' ∷ outer-suffix)))
          (sym x≡dig)
          (optStandardScope-Network-on-digit k pos
             (tail ++ₗ ';' ∷ '\n' ∷ outer-suffix) k<10)
  optStandardScope-Network-on-classified pos x tail outer-suffix (inj₂ x≡dash) =
    subst (λ y → (parseStandardAttrTarget <|> pure ATgtNetwork) pos
                    (y ∷ tail ++ₗ ';' ∷ '\n' ∷ outer-suffix)
                  ≡ just (mkResult ATgtNetwork pos
                            (y ∷ tail ++ₗ ';' ∷ '\n' ∷ outer-suffix)))
          (sym x≡dash)
          (optStandardScope-Network-on-dash pos
             (tail ++ₗ ';' ∷ '\n' ∷ outer-suffix))

  target-eq-Network-DecRat-frac :
    ∀ pos4 d outer-suffix →
    (parseStandardAttrTarget <|> pure ATgtNetwork) pos4
      (showDecRat-dec-chars d ++ₗ ';' ∷ '\n' ∷ outer-suffix)
    ≡ just (mkResult ATgtNetwork pos4
              (showDecRat-dec-chars d ++ₗ ';' ∷ '\n' ∷ outer-suffix))
  target-eq-Network-DecRat-frac pos4 d outer-suffix
    with showDecRat-chars-head-classify d
  ... | x , tail , head-eq , _ , _ , inj-or-dash =
    subst (λ chars → (parseStandardAttrTarget <|> pure ATgtNetwork) pos4
                        (chars ++ₗ ';' ∷ '\n' ∷ outer-suffix)
                      ≡ just (mkResult ATgtNetwork pos4
                                (chars ++ₗ ';' ∷ '\n' ∷ outer-suffix)))
          (sym head-eq)
          (optStandardScope-Network-on-classified pos4 x tail outer-suffix inj-or-dash)

  target-eq-Network-DecRat-bareInt :
    ∀ pos4 z outer-suffix →
    (parseStandardAttrTarget <|> pure ATgtNetwork) pos4
      (showInt-chars z ++ₗ ';' ∷ '\n' ∷ outer-suffix)
    ≡ just (mkResult ATgtNetwork pos4
              (showInt-chars z ++ₗ ';' ∷ '\n' ∷ outer-suffix))
  target-eq-Network-DecRat-bareInt pos4 z outer-suffix
    with showInt-chars-head-classify z
  ... | x , tail , head-eq , _ , _ , inj-or-dash =
    subst (λ chars → (parseStandardAttrTarget <|> pure ATgtNetwork) pos4
                        (chars ++ₗ ';' ∷ '\n' ∷ outer-suffix)
                      ≡ just (mkResult ATgtNetwork pos4
                                (chars ++ₗ ';' ∷ '\n' ∷ outer-suffix)))
          (sym head-eq)
          (optStandardScope-Network-on-classified pos4 x tail outer-suffix inj-or-dash)

-- ============================================================================
-- Trace module for parseRawAttrAssign with ATgtNetwork target
-- ============================================================================

module TraceNetwork (pos : Position) (name : String) (value-chars : List Char)
                    (outer-suffix : List Char) where
  cs-name = quoteStringLit-chars name

  pos1 : Position  -- after string "BA_"
  pos1 = advancePositions pos (toList "BA_")

  pos2 : Position  -- after parseWS
  pos2 = advancePosition pos1 ' '

  pos3 : Position  -- after parseStringLit
  pos3 = advancePositions pos2 cs-name

  pos4 : Position  -- after parseWS
  pos4 = advancePosition pos3 ' '

  -- pos5 = pos4 (no consumption for ATgtNetwork via fall-through)
  pos6 : Position  -- after parseRawAttrValue
  pos6 = advancePositions pos4 value-chars

  -- pos7 = pos6 (parseWSOpt 0 iter on ';' head)
  pos8 : Position  -- after char ';'
  pos8 = advancePosition pos6 ';'

  pos9 : Position  -- after parseNewline
  pos9 = advancePosition pos8 '\n'

  rest-tail : List Char
  rest-tail = ';' ∷ '\n' ∷ outer-suffix

  body-after-keyword : List Char
  body-after-keyword = ' ' ∷ cs-name ++ₗ ' ' ∷ value-chars ++ₗ rest-tail

  body-after-WS1 : List Char
  body-after-WS1 = cs-name ++ₗ ' ' ∷ value-chars ++ₗ rest-tail

  body-after-name : List Char
  body-after-name = ' ' ∷ value-chars ++ₗ rest-tail

  body-after-WS2 : List Char
  body-after-WS2 = value-chars ++ₗ rest-tail

  -- (parseStandardAttrTarget <|> pure ATgtNetwork) — ATgtNetwork case
  -- consumes nothing.
  body-after-target : List Char
  body-after-target = body-after-WS2

  body-after-value : List Char
  body-after-value = rest-tail

  body-after-WSOpt : List Char
  body-after-WSOpt = ';' ∷ '\n' ∷ outer-suffix

  body-after-semi : List Char
  body-after-semi = '\n' ∷ outer-suffix

  body-after-NL : List Char
  body-after-NL = outer-suffix

-- ============================================================================
-- Parameterised after-keyword for ATgtNetwork case
-- ============================================================================

parseRawAttrAssign-after-keyword-Network :
  ∀ pos (name : String) (raw-value : RawAttrValue) (value-chars : List Char)
    (outer-suffix : List Char)
  → SuffixStops isNewlineStart outer-suffix
  → SuffixStops isHSpace (value-chars ++ₗ ';' ∷ '\n' ∷ outer-suffix)
  → let open TraceNetwork pos name value-chars outer-suffix in
    (parseStandardAttrTarget <|> pure ATgtNetwork) pos4 body-after-WS2
      ≡ just (mkResult ATgtNetwork pos4 body-after-target)
  → parseRawAttrValue pos4 body-after-target
      ≡ just (mkResult raw-value pos6 body-after-value)
  → parseRawAttrAssign pos
      ('B' ∷ 'A' ∷ '_' ∷ TraceNetwork.body-after-keyword pos name value-chars outer-suffix)
    ≡ just (mkResult (mkRawAttrAssign name ATgtNetwork raw-value)
              (TraceNetwork.pos9 pos name value-chars outer-suffix)
              outer-suffix)
parseRawAttrAssign-after-keyword-Network pos name raw-value value-chars outer-suffix
  ss-NL value-stops-isHSpace target-eq value-eq =
    -- Step 1: string "BA_"
    trans (bind-just-step (string "BA_")
           (λ _ → parseWS >>= λ _ →
                  parseStringLit >>= λ n →
                  parseWS >>= λ _ →
                  (parseStandardAttrTarget <|> pure ATgtNetwork) >>= λ t →
                  parseRawAttrValue >>= λ v →
                  parseWSOpt >>= λ _ →
                  char ';' >>= λ _ →
                  parseNewline >>= λ _ →
                  many parseNewline >>= λ _ →
                  pure (mkRawAttrAssign n t v))
           pos
           ('B' ∷ 'A' ∷ '_' ∷ body-after-keyword)
           "BA_" pos1 body-after-keyword
           (string-success pos "BA_" body-after-keyword))
    -- Step 2: parseWS consumes ' '.
    (trans (bind-just-step parseWS
              (λ _ → parseStringLit >>= λ n →
                     parseWS >>= λ _ →
                     (parseStandardAttrTarget <|> pure ATgtNetwork) >>= λ t →
                     parseRawAttrValue >>= λ v →
                     parseWSOpt >>= λ _ →
                     char ';' >>= λ _ →
                     parseNewline >>= λ _ →
                     many parseNewline >>= λ _ →
                     pure (mkRawAttrAssign n t v))
              pos1 body-after-keyword
              (' ' ∷ []) pos2 body-after-WS1
              (parseWS-one-space pos1 body-after-WS1 (∷-stop refl)))
    -- Step 3: parseStringLit reads name.
    (trans (bind-just-step parseStringLit
              (λ n → parseWS >>= λ _ →
                     (parseStandardAttrTarget <|> pure ATgtNetwork) >>= λ t →
                     parseRawAttrValue >>= λ v →
                     parseWSOpt >>= λ _ →
                     char ';' >>= λ _ →
                     parseNewline >>= λ _ →
                     many parseNewline >>= λ _ →
                     pure (mkRawAttrAssign n t v))
              pos2 body-after-WS1
              name pos3 body-after-name
              (parseStringLit-roundtrip pos2 name body-after-name (∷-stop refl)))
    -- Step 4: parseWS consumes ' '.
    (trans (bind-just-step parseWS
              (λ _ → (parseStandardAttrTarget <|> pure ATgtNetwork) >>= λ t →
                     parseRawAttrValue >>= λ v →
                     parseWSOpt >>= λ _ →
                     char ';' >>= λ _ →
                     parseNewline >>= λ _ →
                     many parseNewline >>= λ _ →
                     pure (mkRawAttrAssign name t v))
              pos3 body-after-name
              (' ' ∷ []) pos4 body-after-WS2
              (parseWS-one-space pos3 body-after-WS2 value-stops-isHSpace))
    -- Step 5: (parseStandardAttrTarget <|> pure ATgtNetwork) — falls through.
    (trans (bind-just-step (parseStandardAttrTarget <|> pure ATgtNetwork)
              (λ t → parseRawAttrValue >>= λ v →
                     parseWSOpt >>= λ _ →
                     char ';' >>= λ _ →
                     parseNewline >>= λ _ →
                     many parseNewline >>= λ _ →
                     pure (mkRawAttrAssign name t v))
              pos4 body-after-WS2
              ATgtNetwork pos4 body-after-target
              target-eq)
    -- Step 6: parseRawAttrValue.
    (trans (bind-just-step parseRawAttrValue
              (λ v → parseWSOpt >>= λ _ →
                     char ';' >>= λ _ →
                     parseNewline >>= λ _ →
                     many parseNewline >>= λ _ →
                     pure (mkRawAttrAssign name ATgtNetwork v))
              pos4 body-after-target
              raw-value pos6 body-after-value
              value-eq)
    -- Step 7: parseWSOpt consumes 0 spaces.
    (trans (bind-just-step parseWSOpt
              (λ _ → char ';' >>= λ _ →
                     parseNewline >>= λ _ →
                     many parseNewline >>= λ _ →
                     pure (mkRawAttrAssign name ATgtNetwork raw-value))
              pos6 body-after-value
              [] pos6 body-after-WSOpt
              (parseWSOpt-empty pos6 outer-suffix))
    -- Step 8: char ';'.
    (trans (bind-just-step (char ';')
              (λ _ → parseNewline >>= λ _ →
                     many parseNewline >>= λ _ →
                     pure (mkRawAttrAssign name ATgtNetwork raw-value))
              pos6 body-after-WSOpt
              ';' pos8 body-after-semi
              refl)
    -- Step 9: parseNewline.
    (trans (bind-just-step parseNewline
              (λ _ → many parseNewline >>= λ _ →
                     pure (mkRawAttrAssign name ATgtNetwork raw-value))
              pos8 body-after-semi
              '\n' pos9 body-after-NL
              (parseNewline-match-LF pos8 outer-suffix))
    -- Step 10: many parseNewline 0 iterations.
    (trans (bind-just-step (many parseNewline)
              (λ _ → pure (mkRawAttrAssign name ATgtNetwork raw-value))
              pos9 body-after-NL
              [] pos9 outer-suffix
              (manyHelper-parseNewline-exhaust pos9 outer-suffix
                (length outer-suffix) ss-NL))
      refl)))))))))
  where
    open TraceNetwork pos name value-chars outer-suffix

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
-- Top-level dispatcher: ATgtNetwork × RavString
-- ============================================================================

parseRawAttrAssign-roundtrip-ATgtNetwork-RavString :
  ∀ pos (name : String) (s : String) (outer-suffix : List Char)
  → SuffixStops isNewlineStart outer-suffix
  → parseRawAttrAssign pos
      (toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
        ' ' ∷ quoteStringLit-chars s ++ₗ toList ";\n" ++ₗ outer-suffix)
    ≡ just (mkResult
              (mkRawAttrAssign name ATgtNetwork (RavString s))
              (TraceNetwork.pos9 pos name (quoteStringLit-chars s) outer-suffix)
              outer-suffix)
parseRawAttrAssign-roundtrip-ATgtNetwork-RavString pos name s outer-suffix ss-NL =
  trans input-eq
    (parseRawAttrAssign-after-keyword-Network pos name (RavString s)
      (quoteStringLit-chars s) outer-suffix ss-NL
      (value-stops-isHSpace-RavString s outer-suffix)
      target-eq
      value-eq)
  where
    open TraceNetwork pos name (quoteStringLit-chars s) outer-suffix

    input-eq :
      parseRawAttrAssign pos
        (toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
          ' ' ∷ quoteStringLit-chars s ++ₗ toList ";\n" ++ₗ outer-suffix)
      ≡ parseRawAttrAssign pos
        ('B' ∷ 'A' ∷ '_' ∷ body-after-keyword)
    input-eq = refl

    target-eq :
      (parseStandardAttrTarget <|> pure ATgtNetwork) pos4 body-after-WS2
      ≡ just (mkResult ATgtNetwork pos4 body-after-target)
    target-eq = optStandardScope-Network-on-quote pos4 _

    value-eq :
      parseRawAttrValue pos4
        (quoteStringLit-chars s ++ₗ ';' ∷ '\n' ∷ outer-suffix)
      ≡ just (mkResult (RavString s) pos6 (';' ∷ '\n' ∷ outer-suffix))
    value-eq = parseRawAttrValue-roundtrip-RavString pos4 s
                 (';' ∷ '\n' ∷ outer-suffix) (∷-stop refl)

-- ============================================================================
-- ATgtNetwork × RavDecRat-frac dispatcher
-- ============================================================================

parseRawAttrAssign-roundtrip-ATgtNetwork-RavDecRatFrac :
  ∀ pos (name : String) (d : DecRat) (outer-suffix : List Char)
  → SuffixStops isNewlineStart outer-suffix
  → parseRawAttrAssign pos
      (toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
        ' ' ∷ showDecRat-dec-chars d ++ₗ toList ";\n" ++ₗ outer-suffix)
    ≡ just (mkResult
              (mkRawAttrAssign name ATgtNetwork (RavDecRat d))
              (TraceNetwork.pos9 pos name (showDecRat-dec-chars d) outer-suffix)
              outer-suffix)
parseRawAttrAssign-roundtrip-ATgtNetwork-RavDecRatFrac pos name d outer-suffix ss-NL
  with showDecRat-chars-head-classify d
... | c , tail , head-eq , c-not-quote , _ , _ =
  trans input-eq
    (parseRawAttrAssign-after-keyword-Network pos name (RavDecRat d)
      (showDecRat-dec-chars d) outer-suffix ss-NL
      (value-stops-isHSpace-RavDecRatFrac d outer-suffix)
      (target-eq-Network-DecRat-frac pos4 d outer-suffix)
      value-eq)
  where
    open TraceNetwork pos name (showDecRat-dec-chars d) outer-suffix
    input-eq :
      parseRawAttrAssign pos
        (toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
          ' ' ∷ showDecRat-dec-chars d ++ₗ toList ";\n" ++ₗ outer-suffix)
      ≡ parseRawAttrAssign pos
        ('B' ∷ 'A' ∷ '_' ∷ body-after-keyword)
    input-eq = refl

    value-eq :
      parseRawAttrValue pos4
        (showDecRat-dec-chars d ++ₗ ';' ∷ '\n' ∷ outer-suffix)
      ≡ just (mkResult (RavDecRat d) pos6 (';' ∷ '\n' ∷ outer-suffix))
    value-eq = parseRawAttrValue-roundtrip-RavDecRatFrac pos4 d
                 (';' ∷ '\n' ∷ outer-suffix) (∷-stop refl)
                 c tail head-eq c-not-quote

-- ============================================================================
-- ATgtNetwork × RavDecRat-bareInt dispatcher
-- ============================================================================

parseRawAttrAssign-roundtrip-ATgtNetwork-RavDecRatBareInt :
  ∀ pos (name : String) (z : ℤ) (outer-suffix : List Char)
  → SuffixStops isNewlineStart outer-suffix
  → parseRawAttrAssign pos
      (toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
        ' ' ∷ showInt-chars z ++ₗ toList ";\n" ++ₗ outer-suffix)
    ≡ just (mkResult
              (mkRawAttrAssign name ATgtNetwork (RavDecRat (fromℤ z)))
              (TraceNetwork.pos9 pos name (showInt-chars z) outer-suffix)
              outer-suffix)
parseRawAttrAssign-roundtrip-ATgtNetwork-RavDecRatBareInt pos name z outer-suffix ss-NL
  with showInt-chars-head-classify z
... | c , tail , head-eq , c-not-quote , _ , _ =
  trans input-eq
    (parseRawAttrAssign-after-keyword-Network pos name (RavDecRat (fromℤ z))
      (showInt-chars z) outer-suffix ss-NL
      (value-stops-isHSpace-RavDecRatBareInt z outer-suffix)
      (target-eq-Network-DecRat-bareInt pos4 z outer-suffix)
      value-eq)
  where
    open TraceNetwork pos name (showInt-chars z) outer-suffix
    input-eq :
      parseRawAttrAssign pos
        (toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
          ' ' ∷ showInt-chars z ++ₗ toList ";\n" ++ₗ outer-suffix)
      ≡ parseRawAttrAssign pos
        ('B' ∷ 'A' ∷ '_' ∷ body-after-keyword)
    input-eq = refl

    value-eq :
      parseRawAttrValue pos4
        (showInt-chars z ++ₗ ';' ∷ '\n' ∷ outer-suffix)
      ≡ just (mkResult (RavDecRat (fromℤ z)) pos6 (';' ∷ '\n' ∷ outer-suffix))
    value-eq = parseRawAttrValue-roundtrip-RavDecRatBareInt pos4 z
                 (';' ∷ '\n' ∷ outer-suffix) (∷-stop refl) (λ ())
                 c tail head-eq c-not-quote
