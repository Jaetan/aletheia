{-# OPTIONS --safe --without-K #-}

-- B.3.d Layer 3 Commit 3c.3 — `parseRawAttrAssign` × ATgtEnvVar
-- per-line construct roundtrips (3 emit shapes).
--
-- ATgtEnvVar is the `parseEvTgt` branch (last alternative in
-- `parseStandardAttrTarget`).  Line-shape:
--   `BA_<sp>"name"<sp>EV_<sp>EnvVarName<sp>vstr;\n`.
--   parseEvTgt: `string "EV_" *> ws *> parseIdentifier *> ws *>
--                pure (ATgtEnvVar ev)`.
-- Composition: parseStandardAttrTarget = ((Node <|> Msg) <|> Sig) <|> EvTgt;
-- alt-right-nothing through Node/Msg/Sig (all fail on 'E' head), then
-- alt-left-just on parseEvTgt (success).

module Aletheia.DBC.TextParser.Properties.Attributes.Assign.EnvVar where

open import Data.Bool using (Bool; true; false; T)
open import Data.Char using (Char)
open import Data.Char.Base using (_≈ᵇ_)
open import Data.Integer using (ℤ; +_; -[1+_])
open import Data.List using (List; []; _∷_; length) renaming (_++_ to _++ₗ_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _×_; _,_)
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
open import Aletheia.DBC.Identifier using (Identifier; isIdentCont)

open import Aletheia.DBC.TextParser.Attributes
  using (parseRawAttrAssign; parseRawAttrValue;
         RawAttrAssign; mkRawAttrAssign;
         RawAttrValue; RavString; RavDecRat;
         parseStandardAttrTarget;
         parseNodeTgt; parseMsgTgt; parseSigTgt; parseEvTgt)
open import Aletheia.DBC.TextParser.Lexer
  using (parseWS; parseWSOpt; parseStringLit; parseNewline;
         parseIdentifier; isHSpace)

open import Aletheia.DBC.TextFormatter.Emitter
  using (quoteStringLit-chars; showDecRat-dec-chars; showInt-chars; digitChar)

open import Aletheia.DBC.TextParser.Properties.Primitives using
  ( parseWS-one-space; parseStringLit-roundtrip; parseIdentifier-roundtrip
  ; alt-right-nothing; alt-left-just
  ; string-success)
open import Aletheia.DBC.TextParser.DecRatParse.Properties using
  ( bind-just-step
  ; SuffixStops; ∷-stop; []-stop
  ; manyHelper-satisfy-exhaust-many)
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
open import Aletheia.DBC.TextParser.Properties.Attributes.Assign.Node using
  ( IdentNameStop)

-- ============================================================================
-- parseEvTgt-roundtrip
-- ============================================================================

private
  ws-stops-isIdentCont : ∀ rest → SuffixStops isIdentCont (' ' ∷ rest)
  ws-stops-isIdentCont _ = ∷-stop refl

  ident-name-stops-isHSpace :
    ∀ (n : Identifier) (rest : List Char)
    → IdentNameStop n
    → SuffixStops isHSpace (Identifier.name n ++ₗ rest)
  ident-name-stops-isHSpace n rest (c , cs , cs-eq , c-not-hsp) =
    subst (λ chars → SuffixStops isHSpace (chars ++ₗ rest))
          (sym cs-eq) (∷-stop c-not-hsp)

parseEvTgt-roundtrip :
  ∀ pos (ev : Identifier) (suffix : List Char)
  → IdentNameStop ev
  → SuffixStops isHSpace suffix
  → parseEvTgt pos
      ('E' ∷ 'V' ∷ '_' ∷ ' ' ∷ Identifier.name ev ++ₗ ' ' ∷ suffix)
    ≡ just (mkResult (ATgtEnvVar ev)
              (advancePosition
                (advancePositions
                  (advancePosition
                    (advancePositions pos (toList "EV_"))
                    ' ')
                  (Identifier.name ev))
                ' ')
              suffix)
parseEvTgt-roundtrip pos ev suffix ev-stop ss-suffix =
  trans (bind-just-step (string "EV_")
           (λ _ → parseWS >>= λ _ →
                  parseIdentifier >>= λ ident →
                  parseWS >>= λ _ →
                  pure (ATgtEnvVar ident))
           pos
           ('E' ∷ 'V' ∷ '_' ∷ ' ' ∷ Identifier.name ev ++ₗ ' ' ∷ suffix)
           "EV_" pos1 (' ' ∷ Identifier.name ev ++ₗ ' ' ∷ suffix)
           (string-success pos "EV_"
              (' ' ∷ Identifier.name ev ++ₗ ' ' ∷ suffix)))
  (trans (bind-just-step parseWS
            (λ _ → parseIdentifier >>= λ ident →
                   parseWS >>= λ _ →
                   pure (ATgtEnvVar ident))
            pos1 (' ' ∷ Identifier.name ev ++ₗ ' ' ∷ suffix)
            (' ' ∷ []) pos2 (Identifier.name ev ++ₗ ' ' ∷ suffix)
            (parseWS-one-space pos1
               (Identifier.name ev ++ₗ ' ' ∷ suffix)
               (ident-name-stops-isHSpace ev (' ' ∷ suffix) ev-stop)))
  (trans (bind-just-step parseIdentifier
            (λ ident → parseWS >>= λ _ →
                       pure (ATgtEnvVar ident))
            pos2 (Identifier.name ev ++ₗ ' ' ∷ suffix)
            ev pos3 (' ' ∷ suffix)
            (parseIdentifier-roundtrip pos2 ev (' ' ∷ suffix)
               (ws-stops-isIdentCont suffix)))
  (trans (bind-just-step parseWS
            (λ _ → pure (ATgtEnvVar ev))
            pos3 (' ' ∷ suffix)
            (' ' ∷ []) pos4 suffix
            (parseWS-one-space pos3 suffix ss-suffix))
    refl)))
  where
    pos1 : Position
    pos1 = advancePositions pos (toList "EV_")
    pos2 : Position
    pos2 = advancePosition pos1 ' '
    pos3 : Position
    pos3 = advancePositions pos2 (Identifier.name ev)
    pos4 : Position
    pos4 = advancePosition pos3 ' '

-- ============================================================================
-- parseStandardAttrTarget composition for ATgtEnvVar (last alt)
-- ============================================================================

private
  parseNodeTgt-fails-on-E :
    ∀ pos rest → parseNodeTgt pos ('E' ∷ rest) ≡ nothing
  parseNodeTgt-fails-on-E _ _ = refl

  parseMsgTgt-fails-on-E :
    ∀ pos rest → parseMsgTgt pos ('E' ∷ rest) ≡ nothing
  parseMsgTgt-fails-on-E _ _ = refl

  parseSigTgt-fails-on-E :
    ∀ pos rest → parseSigTgt pos ('E' ∷ rest) ≡ nothing
  parseSigTgt-fails-on-E _ _ = refl

  parseStandardAttrTarget-on-EnvVar :
    ∀ pos (ev : Identifier) (suffix : List Char)
    → IdentNameStop ev
    → SuffixStops isHSpace suffix
    → parseStandardAttrTarget pos
        ('E' ∷ 'V' ∷ '_' ∷ ' ' ∷ Identifier.name ev ++ₗ ' ' ∷ suffix)
      ≡ just (mkResult (ATgtEnvVar ev)
                (advancePosition
                  (advancePositions
                    (advancePosition
                      (advancePositions pos (toList "EV_"))
                      ' ')
                    (Identifier.name ev))
                  ' ')
                suffix)
  parseStandardAttrTarget-on-EnvVar pos ev suffix ev-stop ss-suffix =
    trans (alt-right-nothing
            ((parseNodeTgt <|> parseMsgTgt) <|> parseSigTgt) parseEvTgt pos
            ev-input
            (trans (alt-right-nothing
                     (parseNodeTgt <|> parseMsgTgt) parseSigTgt pos
                     ev-input
                     (trans (alt-right-nothing parseNodeTgt parseMsgTgt pos
                              ev-input
                              (parseNodeTgt-fails-on-E pos
                                ('V' ∷ '_' ∷ ' ' ∷ Identifier.name ev
                                  ++ₗ ' ' ∷ suffix)))
                            (parseMsgTgt-fails-on-E pos
                              ('V' ∷ '_' ∷ ' ' ∷ Identifier.name ev
                                ++ₗ ' ' ∷ suffix))))
                   (parseSigTgt-fails-on-E pos
                     ('V' ∷ '_' ∷ ' ' ∷ Identifier.name ev
                       ++ₗ ' ' ∷ suffix))))
          (parseEvTgt-roundtrip pos ev suffix ev-stop ss-suffix)
    where
      ev-input : List Char
      ev-input =
        'E' ∷ 'V' ∷ '_' ∷ ' ' ∷ Identifier.name ev ++ₗ ' ' ∷ suffix

  optStandardScope-on-EnvVar :
    ∀ pos (ev : Identifier) (suffix : List Char)
    → IdentNameStop ev
    → SuffixStops isHSpace suffix
    → (parseStandardAttrTarget <|> pure ATgtNetwork) pos
        ('E' ∷ 'V' ∷ '_' ∷ ' ' ∷ Identifier.name ev ++ₗ ' ' ∷ suffix)
      ≡ just (mkResult (ATgtEnvVar ev)
                (advancePosition
                  (advancePositions
                    (advancePosition
                      (advancePositions pos (toList "EV_"))
                      ' ')
                    (Identifier.name ev))
                  ' ')
                suffix)
  optStandardScope-on-EnvVar pos ev suffix ev-stop ss-suffix =
    alt-left-just parseStandardAttrTarget (pure ATgtNetwork) pos
      ('E' ∷ 'V' ∷ '_' ∷ ' ' ∷ Identifier.name ev ++ₗ ' ' ∷ suffix)
      _
      (parseStandardAttrTarget-on-EnvVar pos ev suffix ev-stop ss-suffix)

-- ============================================================================
-- TraceEnvVar
-- ============================================================================

module TraceEnvVar (pos : Position) (name : List Char) (ev : Identifier)
                   (value-chars : List Char) (outer-suffix : List Char) where
  cs-name = quoteStringLit-chars name
  cs-ev = Identifier.name ev

  pos1 : Position
  pos1 = advancePositions pos (toList "BA_")
  pos2 : Position
  pos2 = advancePosition pos1 ' '
  pos3 : Position
  pos3 = advancePositions pos2 cs-name
  pos4 : Position
  pos4 = advancePosition pos3 ' '
  pos4a : Position
  pos4a = advancePositions pos4 (toList "EV_")
  pos4b : Position
  pos4b = advancePosition pos4a ' '
  pos4c : Position
  pos4c = advancePositions pos4b cs-ev
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
    ' ' ∷ cs-name ++ₗ ' ' ∷ 'E' ∷ 'V' ∷ '_' ∷ ' ' ∷ cs-ev ++ₗ
      ' ' ∷ value-chars ++ₗ rest-tail

  body-after-WS1 : List Char
  body-after-WS1 =
    cs-name ++ₗ ' ' ∷ 'E' ∷ 'V' ∷ '_' ∷ ' ' ∷ cs-ev ++ₗ
      ' ' ∷ value-chars ++ₗ rest-tail

  body-after-name : List Char
  body-after-name =
    ' ' ∷ 'E' ∷ 'V' ∷ '_' ∷ ' ' ∷ cs-ev ++ₗ
      ' ' ∷ value-chars ++ₗ rest-tail

  body-after-WS2 : List Char
  body-after-WS2 =
    'E' ∷ 'V' ∷ '_' ∷ ' ' ∷ cs-ev ++ₗ ' ' ∷ value-chars ++ₗ rest-tail

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
-- Parameterised after-keyword for ATgtEnvVar
-- ============================================================================

parseRawAttrAssign-after-keyword-EnvVar :
  ∀ pos (name : List Char) (ev : Identifier) (raw-value : RawAttrValue)
    (value-chars : List Char) (outer-suffix : List Char)
  → IdentNameStop ev
  → SuffixStops isNewlineStart outer-suffix
  → SuffixStops isHSpace (value-chars ++ₗ ';' ∷ '\n' ∷ outer-suffix)
  → let open TraceEnvVar pos name ev value-chars outer-suffix in
    parseRawAttrValue pos5 body-after-target
      ≡ just (mkResult raw-value pos6 body-after-value)
  → parseRawAttrAssign pos
      ('B' ∷ 'A' ∷ '_' ∷
        TraceEnvVar.body-after-keyword pos name ev value-chars outer-suffix)
    ≡ just (mkResult (mkRawAttrAssign name (ATgtEnvVar ev) raw-value)
              (TraceEnvVar.pos9 pos name ev value-chars outer-suffix)
              outer-suffix)
parseRawAttrAssign-after-keyword-EnvVar pos name ev raw-value value-chars outer-suffix
  ev-stop ss-NL value-stops-isHSpace value-eq =
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
              (ATgtEnvVar ev) pos5 body-after-target
              (optStandardScope-on-EnvVar pos4 ev
                 (value-chars ++ₗ rest-tail) ev-stop value-stops-isHSpace))
    (trans (bind-just-step parseRawAttrValue
              (λ v → parseWSOpt >>= λ _ →
                     char ';' >>= λ _ →
                     parseNewline >>= λ _ →
                     many parseNewline >>= λ _ →
                     pure (mkRawAttrAssign name (ATgtEnvVar ev) v))
              pos5 body-after-target
              raw-value pos6 body-after-value
              value-eq)
    (trans (bind-just-step parseWSOpt
              (λ _ → char ';' >>= λ _ →
                     parseNewline >>= λ _ →
                     many parseNewline >>= λ _ →
                     pure (mkRawAttrAssign name (ATgtEnvVar ev) raw-value))
              pos6 body-after-value
              [] pos6 body-after-WSOpt
              (parseWSOpt-empty pos6 outer-suffix))
    (trans (bind-just-step (char ';')
              (λ _ → parseNewline >>= λ _ →
                     many parseNewline >>= λ _ →
                     pure (mkRawAttrAssign name (ATgtEnvVar ev) raw-value))
              pos6 body-after-WSOpt
              ';' pos8 body-after-semi
              refl)
    (trans (bind-just-step parseNewline
              (λ _ → many parseNewline >>= λ _ →
                     pure (mkRawAttrAssign name (ATgtEnvVar ev) raw-value))
              pos8 body-after-semi
              '\n' pos9 body-after-NL
              (parseNewline-match-LF pos8 outer-suffix))
    (trans (bind-just-step (many parseNewline)
              (λ _ → pure (mkRawAttrAssign name (ATgtEnvVar ev) raw-value))
              pos9 body-after-NL
              [] pos9 outer-suffix
              (manyHelper-parseNewline-exhaust pos9 outer-suffix
                (length outer-suffix) ss-NL))
      refl)))))))))
  where
    open TraceEnvVar pos name ev value-chars outer-suffix

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
-- Top-level dispatchers: ATgtEnvVar × {RavString, frac, bareInt}
-- ============================================================================

parseRawAttrAssign-roundtrip-ATgtEnvVar-RavString :
  ∀ pos (name : List Char) (ev : Identifier) (s : List Char) (outer-suffix : List Char)
  → IdentNameStop ev
  → SuffixStops isNewlineStart outer-suffix
  → parseRawAttrAssign pos
      (toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
        toList " EV_ " ++ₗ Identifier.name ev ++ₗ
        ' ' ∷ quoteStringLit-chars s ++ₗ toList ";\n" ++ₗ outer-suffix)
    ≡ just (mkResult
              (mkRawAttrAssign name (ATgtEnvVar ev) (RavString s))
              (TraceEnvVar.pos9 pos name ev (quoteStringLit-chars s) outer-suffix)
              outer-suffix)
parseRawAttrAssign-roundtrip-ATgtEnvVar-RavString pos name ev s outer-suffix ev-stop ss-NL =
  trans input-eq
    (parseRawAttrAssign-after-keyword-EnvVar pos name ev (RavString s)
      (quoteStringLit-chars s) outer-suffix ev-stop ss-NL
      (value-stops-isHSpace-RavString s outer-suffix)
      value-eq)
  where
    open TraceEnvVar pos name ev (quoteStringLit-chars s) outer-suffix

    input-eq :
      parseRawAttrAssign pos
        (toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
          toList " EV_ " ++ₗ Identifier.name ev ++ₗ
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

parseRawAttrAssign-roundtrip-ATgtEnvVar-RavDecRatFrac :
  ∀ pos (name : List Char) (ev : Identifier) (d : DecRat) (outer-suffix : List Char)
  → IdentNameStop ev
  → SuffixStops isNewlineStart outer-suffix
  → parseRawAttrAssign pos
      (toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
        toList " EV_ " ++ₗ Identifier.name ev ++ₗ
        ' ' ∷ showDecRat-dec-chars d ++ₗ toList ";\n" ++ₗ outer-suffix)
    ≡ just (mkResult
              (mkRawAttrAssign name (ATgtEnvVar ev) (RavDecRat d))
              (TraceEnvVar.pos9 pos name ev (showDecRat-dec-chars d) outer-suffix)
              outer-suffix)
parseRawAttrAssign-roundtrip-ATgtEnvVar-RavDecRatFrac pos name ev d outer-suffix ev-stop ss-NL
  with showDecRat-chars-head-classify d
... | c , tail , head-eq , c-not-quote , _ , _ =
  trans input-eq
    (parseRawAttrAssign-after-keyword-EnvVar pos name ev (RavDecRat d)
      (showDecRat-dec-chars d) outer-suffix ev-stop ss-NL
      (value-stops-isHSpace-RavDecRatFrac d outer-suffix)
      value-eq)
  where
    open TraceEnvVar pos name ev (showDecRat-dec-chars d) outer-suffix

    input-eq :
      parseRawAttrAssign pos
        (toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
          toList " EV_ " ++ₗ Identifier.name ev ++ₗ
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

parseRawAttrAssign-roundtrip-ATgtEnvVar-RavDecRatBareInt :
  ∀ pos (name : List Char) (ev : Identifier) (z : ℤ) (outer-suffix : List Char)
  → IdentNameStop ev
  → SuffixStops isNewlineStart outer-suffix
  → parseRawAttrAssign pos
      (toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
        toList " EV_ " ++ₗ Identifier.name ev ++ₗ
        ' ' ∷ showInt-chars z ++ₗ toList ";\n" ++ₗ outer-suffix)
    ≡ just (mkResult
              (mkRawAttrAssign name (ATgtEnvVar ev) (RavDecRat (fromℤ z)))
              (TraceEnvVar.pos9 pos name ev (showInt-chars z) outer-suffix)
              outer-suffix)
parseRawAttrAssign-roundtrip-ATgtEnvVar-RavDecRatBareInt pos name ev z outer-suffix ev-stop ss-NL
  with showInt-chars-head-classify z
... | c , tail , head-eq , c-not-quote , _ , _ =
  trans input-eq
    (parseRawAttrAssign-after-keyword-EnvVar pos name ev (RavDecRat (fromℤ z))
      (showInt-chars z) outer-suffix ev-stop ss-NL
      (value-stops-isHSpace-RavDecRatBareInt z outer-suffix)
      value-eq)
  where
    open TraceEnvVar pos name ev (showInt-chars z) outer-suffix

    input-eq :
      parseRawAttrAssign pos
        (toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
          toList " EV_ " ++ₗ Identifier.name ev ++ₗ
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
