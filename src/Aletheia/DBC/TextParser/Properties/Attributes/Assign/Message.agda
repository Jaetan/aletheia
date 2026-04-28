{-# OPTIONS --safe --without-K #-}

-- B.3.d Layer 3 Commit 3c.3 — `parseRawAttrAssign` × ATgtMessage
-- per-line construct roundtrips (3 emit shapes).
--
-- ATgtMessage is the `parseMsgTgt` branch of `parseStandardAttrTarget`
-- (second alternative in the 4-fold `<|>`).  Line-shape:
--   `BA_<sp>"name"<sp>BO_<sp>showℕ-dec-chars(rawCanIdℕ cid)<sp>vstr;\n`.
--   parseMsgTgt: `string "BO_" *> ws *> parseNatural *> ws *>
--                 wrapMsgTarget rawId`.
-- `wrapMsgTarget` does `with buildCANId rawId | just cid → pure (ATgtMessage cid)`,
-- and the closure via `buildCANId-rawCanIdℕ` (from Comments/Comment.agda)
-- folds the inner with-aux on the roundtrip case.

module Aletheia.DBC.TextParser.Properties.Attributes.Assign.Message where

open import Data.Bool using (Bool; true; false; T)
open import Data.Char using (Char)
open import Data.Char.Base using (_≈ᵇ_)
open import Data.Integer using (ℤ; +_; -[1+_])
open import Data.List using (List; []; _∷_; length) renaming (_++_ to _++ₗ_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.String using (String; toList)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

open import Aletheia.Parser.Combinators
  using (Position; Parser; ParseResult; mkResult; advancePosition; advancePositions;
         _>>=_; pure; _<|>_; _*>_; string;
         char; many; satisfy)
open import Aletheia.DBC.DecRat using (DecRat; fromℤ)
open import Aletheia.DBC.Types using
  ( AttrTarget; ATgtNetwork; ATgtNode; ATgtMessage; ATgtSignal; ATgtEnvVar)
open import Aletheia.CAN.Frame using (CANId)

open import Aletheia.DBC.TextParser.Attributes
  using (parseRawAttrAssign; parseRawAttrValue;
         RawAttrAssign; mkRawAttrAssign;
         RawAttrValue; RavString; RavDecRat;
         parseStandardAttrTarget;
         parseNodeTgt; parseMsgTgt; parseSigTgt; parseEvTgt;
         wrapMsgTarget)
open import Aletheia.DBC.TextParser.Lexer
  using (parseWS; parseWSOpt; parseStringLit; parseNewline; parseNatural;
         isHSpace)
open import Aletheia.DBC.TextParser.Topology.Foundations using (buildCANId)

open import Aletheia.DBC.TextFormatter.Emitter
  using (quoteStringLit-chars; showDecRat-dec-chars; showInt-chars;
         showℕ-dec-chars; digitChar)
open import Aletheia.DBC.TextFormatter.Topology using (rawCanIdℕ)

open import Aletheia.DBC.TextParser.Properties.Primitives using
  ( parseWS-one-space; parseStringLit-roundtrip
  ; alt-right-nothing; alt-left-just
  ; string-success)
open import Aletheia.DBC.TextParser.DecRatParse.Properties using
  ( bind-just-step
  ; SuffixStops; ∷-stop; []-stop
  ; parseNatural-showNat-chars
  ; manyHelper-satisfy-exhaust-many)
open import Aletheia.DBC.TextParser.Properties.Preamble.Newline using
  ( isNewlineStart
  ; parseNewline-match-LF
  ; manyHelper-parseNewline-exhaust)
open import Aletheia.DBC.TextParser.Properties.Comments.Comment using
  ( buildCANId-rawCanIdℕ)
open import Aletheia.DBC.TextParser.Properties.Attributes.Default using
  ( parseRawAttrValue-roundtrip-RavString
  ; parseRawAttrValue-roundtrip-RavDecRatFrac
  ; parseRawAttrValue-roundtrip-RavDecRatBareInt)
open import Aletheia.DBC.TextParser.Properties.Attributes.Assign.Common using
  ( showInt-chars-head-classify; showDecRat-chars-head-classify
  ; value-stops-isHSpace-RavString
  ; value-stops-isHSpace-RavDecRatFrac
  ; value-stops-isHSpace-RavDecRatBareInt
  ; showNat-chars-head-stop-isHSpace)

-- ============================================================================
-- wrapMsgTarget-roundtrip — discharge the inner with-aux via
-- buildCANId-rawCanIdℕ (mirrors wrapCTMessage-roundtrip in Comment.agda).
-- ============================================================================

wrapMsgTarget-roundtrip :
  ∀ (cid : CANId) (pos : Position) (input : List Char)
  → wrapMsgTarget (rawCanIdℕ cid) pos input
    ≡ just (mkResult (ATgtMessage cid) pos input)
wrapMsgTarget-roundtrip cid pos input
  with buildCANId (rawCanIdℕ cid) | buildCANId-rawCanIdℕ cid
... | just .cid | refl = refl

-- ============================================================================
-- parseMsgTgt-roundtrip
-- ============================================================================

parseMsgTgt-roundtrip :
  ∀ pos (cid : CANId) (suffix : List Char)
  → SuffixStops isHSpace suffix
  → parseMsgTgt pos
      ('B' ∷ 'O' ∷ '_' ∷ ' ' ∷ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ ' ' ∷ suffix)
    ≡ just (mkResult (ATgtMessage cid)
              (advancePosition
                (advancePositions
                  (advancePosition
                    (advancePositions pos (toList "BO_"))
                    ' ')
                  (showℕ-dec-chars (rawCanIdℕ cid)))
                ' ')
              suffix)
parseMsgTgt-roundtrip pos cid suffix ss-suffix =
  trans (bind-just-step (string "BO_")
           (λ _ → parseWS >>= λ _ →
                  parseNatural >>= λ r →
                  parseWS >>= λ _ →
                  wrapMsgTarget r)
           pos
           ('B' ∷ 'O' ∷ '_' ∷ ' ' ∷ digits ++ₗ ' ' ∷ suffix)
           "BO_" pos1 (' ' ∷ digits ++ₗ ' ' ∷ suffix)
           (string-success pos "BO_"
              (' ' ∷ digits ++ₗ ' ' ∷ suffix)))
  (trans (bind-just-step parseWS
            (λ _ → parseNatural >>= λ r →
                   parseWS >>= λ _ →
                   wrapMsgTarget r)
            pos1 (' ' ∷ digits ++ₗ ' ' ∷ suffix)
            (' ' ∷ []) pos2 (digits ++ₗ ' ' ∷ suffix)
            (parseWS-one-space pos1 (digits ++ₗ ' ' ∷ suffix)
               (showNat-chars-head-stop-isHSpace (rawCanIdℕ cid) (' ' ∷ suffix))))
  (trans (bind-just-step parseNatural
            (λ r → parseWS >>= λ _ →
                   wrapMsgTarget r)
            pos2 (digits ++ₗ ' ' ∷ suffix)
            (rawCanIdℕ cid) pos3 (' ' ∷ suffix)
            (parseNatural-showNat-chars pos2 (rawCanIdℕ cid) (' ' ∷ suffix)
               (∷-stop refl)))
  (trans (bind-just-step parseWS
            (λ _ → wrapMsgTarget (rawCanIdℕ cid))
            pos3 (' ' ∷ suffix)
            (' ' ∷ []) pos4 suffix
            (parseWS-one-space pos3 suffix ss-suffix))
    (wrapMsgTarget-roundtrip cid pos4 suffix))))
  where
    digits : List Char
    digits = showℕ-dec-chars (rawCanIdℕ cid)
    pos1 : Position
    pos1 = advancePositions pos (toList "BO_")
    pos2 : Position
    pos2 = advancePosition pos1 ' '
    pos3 : Position
    pos3 = advancePositions pos2 digits
    pos4 : Position
    pos4 = advancePosition pos3 ' '

-- ============================================================================
-- parseNodeTgt-fails-on-BO + alt-left-just lift through parseStandardAttrTarget
-- ============================================================================

private
  -- string "BU_" fails on 'B' ∷ 'O' input — char 'U' on 'O' is nothing.
  parseNodeTgt-fails-on-BO :
    ∀ pos rest →
    parseNodeTgt pos ('B' ∷ 'O' ∷ rest) ≡ nothing
  parseNodeTgt-fails-on-BO _ _ = refl

  parseStandardAttrTarget-on-Message :
    ∀ pos (cid : CANId) (suffix : List Char)
    → SuffixStops isHSpace suffix
    → parseStandardAttrTarget pos
        ('B' ∷ 'O' ∷ '_' ∷ ' ' ∷ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ ' ' ∷ suffix)
      ≡ just (mkResult (ATgtMessage cid)
                (advancePosition
                  (advancePositions
                    (advancePosition
                      (advancePositions pos (toList "BO_"))
                      ' ')
                    (showℕ-dec-chars (rawCanIdℕ cid)))
                  ' ')
                suffix)
  parseStandardAttrTarget-on-Message pos cid suffix ss-suffix =
    alt-left-just
      ((parseNodeTgt <|> parseMsgTgt) <|> parseSigTgt) parseEvTgt pos
      ('B' ∷ 'O' ∷ '_' ∷ ' ' ∷ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ ' ' ∷ suffix)
      _
      (alt-left-just
         (parseNodeTgt <|> parseMsgTgt) parseSigTgt pos
         ('B' ∷ 'O' ∷ '_' ∷ ' ' ∷ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ ' ' ∷ suffix)
         _
         (trans (alt-right-nothing parseNodeTgt parseMsgTgt pos
                  ('B' ∷ 'O' ∷ '_' ∷ ' ' ∷ showℕ-dec-chars (rawCanIdℕ cid)
                    ++ₗ ' ' ∷ suffix)
                  (parseNodeTgt-fails-on-BO pos
                    ('_' ∷ ' ' ∷ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ ' ' ∷ suffix)))
                (parseMsgTgt-roundtrip pos cid suffix ss-suffix)))

  optStandardScope-on-Message :
    ∀ pos (cid : CANId) (suffix : List Char)
    → SuffixStops isHSpace suffix
    → (parseStandardAttrTarget <|> pure ATgtNetwork) pos
        ('B' ∷ 'O' ∷ '_' ∷ ' ' ∷ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ ' ' ∷ suffix)
      ≡ just (mkResult (ATgtMessage cid)
                (advancePosition
                  (advancePositions
                    (advancePosition
                      (advancePositions pos (toList "BO_"))
                      ' ')
                    (showℕ-dec-chars (rawCanIdℕ cid)))
                  ' ')
                suffix)
  optStandardScope-on-Message pos cid suffix ss-suffix =
    alt-left-just parseStandardAttrTarget (pure ATgtNetwork) pos
      ('B' ∷ 'O' ∷ '_' ∷ ' ' ∷ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ ' ' ∷ suffix)
      _
      (parseStandardAttrTarget-on-Message pos cid suffix ss-suffix)

-- ============================================================================
-- TraceMessage
-- ============================================================================

module TraceMessage (pos : Position) (name : List Char) (cid : CANId)
                    (value-chars : List Char) (outer-suffix : List Char) where
  cs-name = quoteStringLit-chars name
  cs-id = showℕ-dec-chars (rawCanIdℕ cid)

  pos1 : Position
  pos1 = advancePositions pos (toList "BA_")
  pos2 : Position
  pos2 = advancePosition pos1 ' '
  pos3 : Position
  pos3 = advancePositions pos2 cs-name
  pos4 : Position
  pos4 = advancePosition pos3 ' '
  pos4a : Position
  pos4a = advancePositions pos4 (toList "BO_")
  pos4b : Position
  pos4b = advancePosition pos4a ' '
  pos4c : Position
  pos4c = advancePositions pos4b cs-id
  pos5 : Position
  pos5 = advancePosition pos4c ' '
  pos6 : Position
  pos6 = advancePositions pos5 value-chars
  pos8 : Position
  pos8 = advancePosition pos6 ';'
  pos9 : Position
  pos9 = advancePosition pos8 '\n'

  rest-tail : List Char
  rest-tail = ';' ∷ '\n' ∷ outer-suffix

  body-after-keyword : List Char
  body-after-keyword =
    ' ' ∷ cs-name ++ₗ ' ' ∷ 'B' ∷ 'O' ∷ '_' ∷ ' ' ∷ cs-id ++ₗ
      ' ' ∷ value-chars ++ₗ rest-tail

  body-after-WS1 : List Char
  body-after-WS1 =
    cs-name ++ₗ ' ' ∷ 'B' ∷ 'O' ∷ '_' ∷ ' ' ∷ cs-id ++ₗ
      ' ' ∷ value-chars ++ₗ rest-tail

  body-after-name : List Char
  body-after-name =
    ' ' ∷ 'B' ∷ 'O' ∷ '_' ∷ ' ' ∷ cs-id ++ₗ
      ' ' ∷ value-chars ++ₗ rest-tail

  body-after-WS2 : List Char
  body-after-WS2 =
    'B' ∷ 'O' ∷ '_' ∷ ' ' ∷ cs-id ++ₗ ' ' ∷ value-chars ++ₗ rest-tail

  body-after-target : List Char
  body-after-target = value-chars ++ₗ rest-tail

  body-after-value : List Char
  body-after-value = rest-tail

  body-after-WSOpt : List Char
  body-after-WSOpt = ';' ∷ '\n' ∷ outer-suffix

  body-after-semi : List Char
  body-after-semi = '\n' ∷ outer-suffix

  body-after-NL : List Char
  body-after-NL = outer-suffix

-- ============================================================================
-- Parameterised after-keyword for ATgtMessage
-- ============================================================================

parseRawAttrAssign-after-keyword-Message :
  ∀ pos (name : List Char) (cid : CANId) (raw-value : RawAttrValue)
    (value-chars : List Char) (outer-suffix : List Char)
  → SuffixStops isNewlineStart outer-suffix
  → SuffixStops isHSpace (value-chars ++ₗ ';' ∷ '\n' ∷ outer-suffix)
  → let open TraceMessage pos name cid value-chars outer-suffix in
    parseRawAttrValue pos5 body-after-target
      ≡ just (mkResult raw-value pos6 body-after-value)
  → parseRawAttrAssign pos
      ('B' ∷ 'A' ∷ '_' ∷ TraceMessage.body-after-keyword pos name cid value-chars outer-suffix)
    ≡ just (mkResult (mkRawAttrAssign name (ATgtMessage cid) raw-value)
              (TraceMessage.pos9 pos name cid value-chars outer-suffix)
              outer-suffix)
parseRawAttrAssign-after-keyword-Message pos name cid raw-value value-chars outer-suffix
  ss-NL value-stops-isHSpace value-eq =
    trans (bind-just-step (string "BA_")
           (λ _ → parseWS >>= λ _ →
                  parseStringLit >>= λ qn →
                  parseWS >>= λ _ →
                  (parseStandardAttrTarget <|> pure ATgtNetwork) >>= λ t →
                  parseRawAttrValue >>= λ v →
                  parseWSOpt >>= λ _ →
                  char ';' >>= λ _ →
                  parseNewline >>= λ _ →
                  many parseNewline >>= λ _ →
                  pure (mkRawAttrAssign qn t v))
           pos
           ('B' ∷ 'A' ∷ '_' ∷ body-after-keyword)
           "BA_" pos1 body-after-keyword
           (string-success pos "BA_" body-after-keyword))
    (trans (bind-just-step parseWS
              (λ _ → parseStringLit >>= λ qn →
                     parseWS >>= λ _ →
                     (parseStandardAttrTarget <|> pure ATgtNetwork) >>= λ t →
                     parseRawAttrValue >>= λ v →
                     parseWSOpt >>= λ _ →
                     char ';' >>= λ _ →
                     parseNewline >>= λ _ →
                     many parseNewline >>= λ _ →
                     pure (mkRawAttrAssign qn t v))
              pos1 body-after-keyword
              (' ' ∷ []) pos2 body-after-WS1
              (parseWS-one-space pos1 body-after-WS1 (∷-stop refl)))
    (trans (bind-just-step parseStringLit
              (λ qn → parseWS >>= λ _ →
                     (parseStandardAttrTarget <|> pure ATgtNetwork) >>= λ t →
                     parseRawAttrValue >>= λ v →
                     parseWSOpt >>= λ _ →
                     char ';' >>= λ _ →
                     parseNewline >>= λ _ →
                     many parseNewline >>= λ _ →
                     pure (mkRawAttrAssign qn t v))
              pos2 body-after-WS1
              name pos3 body-after-name
              (parseStringLit-roundtrip pos2 name body-after-name (∷-stop refl)))
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
              (parseWS-one-space pos3 body-after-WS2 (∷-stop refl)))
    (trans (bind-just-step (parseStandardAttrTarget <|> pure ATgtNetwork)
              (λ t → parseRawAttrValue >>= λ v →
                     parseWSOpt >>= λ _ →
                     char ';' >>= λ _ →
                     parseNewline >>= λ _ →
                     many parseNewline >>= λ _ →
                     pure (mkRawAttrAssign name t v))
              pos4 body-after-WS2
              (ATgtMessage cid) pos5 body-after-target
              (optStandardScope-on-Message pos4 cid
                 (value-chars ++ₗ rest-tail) value-stops-isHSpace))
    (trans (bind-just-step parseRawAttrValue
              (λ v → parseWSOpt >>= λ _ →
                     char ';' >>= λ _ →
                     parseNewline >>= λ _ →
                     many parseNewline >>= λ _ →
                     pure (mkRawAttrAssign name (ATgtMessage cid) v))
              pos5 body-after-target
              raw-value pos6 body-after-value
              value-eq)
    (trans (bind-just-step parseWSOpt
              (λ _ → char ';' >>= λ _ →
                     parseNewline >>= λ _ →
                     many parseNewline >>= λ _ →
                     pure (mkRawAttrAssign name (ATgtMessage cid) raw-value))
              pos6 body-after-value
              [] pos6 body-after-WSOpt
              (parseWSOpt-empty pos6 outer-suffix))
    (trans (bind-just-step (char ';')
              (λ _ → parseNewline >>= λ _ →
                     many parseNewline >>= λ _ →
                     pure (mkRawAttrAssign name (ATgtMessage cid) raw-value))
              pos6 body-after-WSOpt
              ';' pos8 body-after-semi
              refl)
    (trans (bind-just-step parseNewline
              (λ _ → many parseNewline >>= λ _ →
                     pure (mkRawAttrAssign name (ATgtMessage cid) raw-value))
              pos8 body-after-semi
              '\n' pos9 body-after-NL
              (parseNewline-match-LF pos8 outer-suffix))
    (trans (bind-just-step (many parseNewline)
              (λ _ → pure (mkRawAttrAssign name (ATgtMessage cid) raw-value))
              pos9 body-after-NL
              [] pos9 outer-suffix
              (manyHelper-parseNewline-exhaust pos9 outer-suffix
                (length outer-suffix) ss-NL))
      refl)))))))))
  where
    open TraceMessage pos name cid value-chars outer-suffix

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
-- Top-level dispatchers: ATgtMessage × {RavString, frac, bareInt}
-- ============================================================================

parseRawAttrAssign-roundtrip-ATgtMessage-RavString :
  ∀ pos (name : List Char) (cid : CANId) (s : List Char) (outer-suffix : List Char)
  → SuffixStops isNewlineStart outer-suffix
  → parseRawAttrAssign pos
      (toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
        toList " BO_ " ++ₗ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
        ' ' ∷ quoteStringLit-chars s ++ₗ toList ";\n" ++ₗ outer-suffix)
    ≡ just (mkResult
              (mkRawAttrAssign name (ATgtMessage cid) (RavString s))
              (TraceMessage.pos9 pos name cid (quoteStringLit-chars s) outer-suffix)
              outer-suffix)
parseRawAttrAssign-roundtrip-ATgtMessage-RavString pos name cid s outer-suffix ss-NL =
  trans input-eq
    (parseRawAttrAssign-after-keyword-Message pos name cid (RavString s)
      (quoteStringLit-chars s) outer-suffix ss-NL
      (value-stops-isHSpace-RavString s outer-suffix)
      value-eq)
  where
    open TraceMessage pos name cid (quoteStringLit-chars s) outer-suffix

    input-eq :
      parseRawAttrAssign pos
        (toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
          toList " BO_ " ++ₗ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
          ' ' ∷ quoteStringLit-chars s ++ₗ toList ";\n" ++ₗ outer-suffix)
      ≡ parseRawAttrAssign pos
        ('B' ∷ 'A' ∷ '_' ∷ body-after-keyword)
    input-eq = refl

    value-eq :
      parseRawAttrValue pos5
        (quoteStringLit-chars s ++ₗ ';' ∷ '\n' ∷ outer-suffix)
      ≡ just (mkResult (RavString s) pos6 (';' ∷ '\n' ∷ outer-suffix))
    value-eq = parseRawAttrValue-roundtrip-RavString pos5 s
                 (';' ∷ '\n' ∷ outer-suffix) (∷-stop refl)

parseRawAttrAssign-roundtrip-ATgtMessage-RavDecRatFrac :
  ∀ pos (name : List Char) (cid : CANId) (d : DecRat) (outer-suffix : List Char)
  → SuffixStops isNewlineStart outer-suffix
  → parseRawAttrAssign pos
      (toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
        toList " BO_ " ++ₗ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
        ' ' ∷ showDecRat-dec-chars d ++ₗ toList ";\n" ++ₗ outer-suffix)
    ≡ just (mkResult
              (mkRawAttrAssign name (ATgtMessage cid) (RavDecRat d))
              (TraceMessage.pos9 pos name cid (showDecRat-dec-chars d) outer-suffix)
              outer-suffix)
parseRawAttrAssign-roundtrip-ATgtMessage-RavDecRatFrac pos name cid d outer-suffix ss-NL
  with showDecRat-chars-head-classify d
... | c , tail , head-eq , c-not-quote , _ , _ =
  trans input-eq
    (parseRawAttrAssign-after-keyword-Message pos name cid (RavDecRat d)
      (showDecRat-dec-chars d) outer-suffix ss-NL
      (value-stops-isHSpace-RavDecRatFrac d outer-suffix)
      value-eq)
  where
    open TraceMessage pos name cid (showDecRat-dec-chars d) outer-suffix

    input-eq :
      parseRawAttrAssign pos
        (toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
          toList " BO_ " ++ₗ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
          ' ' ∷ showDecRat-dec-chars d ++ₗ toList ";\n" ++ₗ outer-suffix)
      ≡ parseRawAttrAssign pos
        ('B' ∷ 'A' ∷ '_' ∷ body-after-keyword)
    input-eq = refl

    value-eq :
      parseRawAttrValue pos5
        (showDecRat-dec-chars d ++ₗ ';' ∷ '\n' ∷ outer-suffix)
      ≡ just (mkResult (RavDecRat d) pos6 (';' ∷ '\n' ∷ outer-suffix))
    value-eq = parseRawAttrValue-roundtrip-RavDecRatFrac pos5 d
                 (';' ∷ '\n' ∷ outer-suffix) (∷-stop refl)
                 c tail head-eq c-not-quote

parseRawAttrAssign-roundtrip-ATgtMessage-RavDecRatBareInt :
  ∀ pos (name : List Char) (cid : CANId) (z : ℤ) (outer-suffix : List Char)
  → SuffixStops isNewlineStart outer-suffix
  → parseRawAttrAssign pos
      (toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
        toList " BO_ " ++ₗ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
        ' ' ∷ showInt-chars z ++ₗ toList ";\n" ++ₗ outer-suffix)
    ≡ just (mkResult
              (mkRawAttrAssign name (ATgtMessage cid) (RavDecRat (fromℤ z)))
              (TraceMessage.pos9 pos name cid (showInt-chars z) outer-suffix)
              outer-suffix)
parseRawAttrAssign-roundtrip-ATgtMessage-RavDecRatBareInt pos name cid z outer-suffix ss-NL
  with showInt-chars-head-classify z
... | c , tail , head-eq , c-not-quote , _ , _ =
  trans input-eq
    (parseRawAttrAssign-after-keyword-Message pos name cid (RavDecRat (fromℤ z))
      (showInt-chars z) outer-suffix ss-NL
      (value-stops-isHSpace-RavDecRatBareInt z outer-suffix)
      value-eq)
  where
    open TraceMessage pos name cid (showInt-chars z) outer-suffix

    input-eq :
      parseRawAttrAssign pos
        (toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
          toList " BO_ " ++ₗ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
          ' ' ∷ showInt-chars z ++ₗ toList ";\n" ++ₗ outer-suffix)
      ≡ parseRawAttrAssign pos
        ('B' ∷ 'A' ∷ '_' ∷ body-after-keyword)
    input-eq = refl

    value-eq :
      parseRawAttrValue pos5
        (showInt-chars z ++ₗ ';' ∷ '\n' ∷ outer-suffix)
      ≡ just (mkResult (RavDecRat (fromℤ z)) pos6 (';' ∷ '\n' ∷ outer-suffix))
    value-eq = parseRawAttrValue-roundtrip-RavDecRatBareInt pos5 z
                 (';' ∷ '\n' ∷ outer-suffix) (∷-stop refl) (λ ())
                 c tail head-eq c-not-quote
