{-# OPTIONS --without-K #-}

-- B.3.d Layer 3 Commit 3c.3 — `parseRawAttrAssign` × ATgtSignal
-- per-line construct roundtrips (3 emit shapes).
--
-- ATgtSignal is the `parseSigTgt` branch (third alternative).
-- Line-shape:
--   `BA_<sp>"name"<sp>SG_<sp>showℕ-dec-chars(rawCanIdℕ cid)<sp>SigName<sp>vstr;\n`.
--   parseSigTgt: `string "SG_" *> ws *> parseNatural *> ws *>
--                 parseIdentifier *> ws *> wrapSigTarget rawId sig`.
--
-- Per-call precondition `IdentNameStop sig` for the SigName: SigName's
-- first char is non-isHSpace.  Owed at Layer 4 universally from
-- `validIdentifierᵇ` (re-uses `Node.IdentNameStop`).

module Aletheia.DBC.TextParser.Properties.Attributes.Assign.Signal where

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
open import Aletheia.CAN.Frame using (CANId)

open import Aletheia.DBC.TextParser.Attributes
  using (parseRawAttrAssign; parseRawAttrValue;
         RawAttrAssign; mkRawAttrAssign;
         RawAttrValue; RavString; RavDecRat;
         parseStandardAttrTarget;
         parseNodeTgt; parseMsgTgt; parseSigTgt; parseEvTgt;
         wrapSigTarget)
open import Aletheia.DBC.TextParser.Lexer
  using (parseWS; parseWSOpt; parseStringLit; parseNewline;
         parseIdentifier; parseNatural; isHSpace)
open import Aletheia.DBC.TextParser.Topology using (buildCANId)

open import Aletheia.DBC.TextFormatter.Emitter
  using (quoteStringLit-chars; showDecRat-dec-chars; showInt-chars;
         showℕ-dec-chars; digitChar)
open import Aletheia.DBC.TextFormatter.Topology using (rawCanIdℕ)

open import Aletheia.DBC.TextParser.Properties.Primitives using
  ( parseWS-one-space; parseStringLit-roundtrip; parseIdentifier-roundtrip
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
open import Aletheia.DBC.TextParser.Properties.Attributes.Assign.Node using
  ( IdentNameStop)

-- ============================================================================
-- wrapSigTarget-roundtrip
-- ============================================================================

wrapSigTarget-roundtrip :
  ∀ (cid : CANId) (sig : Identifier) (pos : Position) (input : List Char)
  → wrapSigTarget (rawCanIdℕ cid) sig pos input
    ≡ just (mkResult (ATgtSignal cid sig) pos input)
wrapSigTarget-roundtrip cid sig pos input
  with buildCANId (rawCanIdℕ cid) | buildCANId-rawCanIdℕ cid
... | just .cid | refl = refl

-- ============================================================================
-- parseSigTgt-roundtrip
-- ============================================================================

private
  ws-stops-isIdentCont : ∀ rest → SuffixStops isIdentCont (' ' ∷ rest)
  ws-stops-isIdentCont _ = ∷-stop refl

  ident-name-stops-isHSpace :
    ∀ (n : Identifier) (rest : List Char)
    → IdentNameStop n
    → SuffixStops isHSpace (toList (Identifier.name n) ++ₗ rest)
  ident-name-stops-isHSpace n rest (c , cs , cs-eq , c-not-hsp) =
    subst (λ chars → SuffixStops isHSpace (chars ++ₗ rest))
          (sym cs-eq) (∷-stop c-not-hsp)

parseSigTgt-roundtrip :
  ∀ pos (cid : CANId) (sig : Identifier) (suffix : List Char)
  → IdentNameStop sig
  → SuffixStops isHSpace suffix
  → parseSigTgt pos
      ('S' ∷ 'G' ∷ '_' ∷ ' ' ∷ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
        ' ' ∷ toList (Identifier.name sig) ++ₗ ' ' ∷ suffix)
    ≡ just (mkResult (ATgtSignal cid sig)
              (advancePosition
                (advancePositions
                  (advancePosition
                    (advancePositions
                      (advancePosition
                        (advancePositions pos (toList "SG_"))
                        ' ')
                      (showℕ-dec-chars (rawCanIdℕ cid)))
                    ' ')
                  (toList (Identifier.name sig)))
                ' ')
              suffix)
parseSigTgt-roundtrip pos cid sig suffix sig-stop ss-suffix =
  trans (bind-just-step (string "SG_")
           (λ _ → parseWS >>= λ _ →
                  parseNatural >>= λ r →
                  parseWS >>= λ _ →
                  parseIdentifier >>= λ s →
                  parseWS >>= λ _ →
                  wrapSigTarget r s)
           pos
           ('S' ∷ 'G' ∷ '_' ∷ ' ' ∷ digits ++ₗ ' ' ∷ sig-chars ++ₗ ' ' ∷ suffix)
           "SG_" pos1 (' ' ∷ digits ++ₗ ' ' ∷ sig-chars ++ₗ ' ' ∷ suffix)
           (string-success pos "SG_" _))
  (trans (bind-just-step parseWS
            (λ _ → parseNatural >>= λ r →
                   parseWS >>= λ _ →
                   parseIdentifier >>= λ s →
                   parseWS >>= λ _ →
                   wrapSigTarget r s)
            pos1 (' ' ∷ digits ++ₗ ' ' ∷ sig-chars ++ₗ ' ' ∷ suffix)
            (' ' ∷ []) pos2 (digits ++ₗ ' ' ∷ sig-chars ++ₗ ' ' ∷ suffix)
            (parseWS-one-space pos1
               (digits ++ₗ ' ' ∷ sig-chars ++ₗ ' ' ∷ suffix)
               (showNat-chars-head-stop-isHSpace (rawCanIdℕ cid)
                  (' ' ∷ sig-chars ++ₗ ' ' ∷ suffix))))
  (trans (bind-just-step parseNatural
            (λ r → parseWS >>= λ _ →
                   parseIdentifier >>= λ s →
                   parseWS >>= λ _ →
                   wrapSigTarget r s)
            pos2 (digits ++ₗ ' ' ∷ sig-chars ++ₗ ' ' ∷ suffix)
            (rawCanIdℕ cid) pos3 (' ' ∷ sig-chars ++ₗ ' ' ∷ suffix)
            (parseNatural-showNat-chars pos2 (rawCanIdℕ cid)
               (' ' ∷ sig-chars ++ₗ ' ' ∷ suffix) (∷-stop refl)))
  (trans (bind-just-step parseWS
            (λ _ → parseIdentifier >>= λ s →
                   parseWS >>= λ _ →
                   wrapSigTarget (rawCanIdℕ cid) s)
            pos3 (' ' ∷ sig-chars ++ₗ ' ' ∷ suffix)
            (' ' ∷ []) pos4 (sig-chars ++ₗ ' ' ∷ suffix)
            (parseWS-one-space pos3 (sig-chars ++ₗ ' ' ∷ suffix)
               (ident-name-stops-isHSpace sig (' ' ∷ suffix) sig-stop)))
  (trans (bind-just-step parseIdentifier
            (λ s → parseWS >>= λ _ →
                   wrapSigTarget (rawCanIdℕ cid) s)
            pos4 (sig-chars ++ₗ ' ' ∷ suffix)
            sig pos5 (' ' ∷ suffix)
            (parseIdentifier-roundtrip pos4 sig (' ' ∷ suffix)
               (ws-stops-isIdentCont suffix)))
  (trans (bind-just-step parseWS
            (λ _ → wrapSigTarget (rawCanIdℕ cid) sig)
            pos5 (' ' ∷ suffix)
            (' ' ∷ []) pos6 suffix
            (parseWS-one-space pos5 suffix ss-suffix))
    (wrapSigTarget-roundtrip cid sig pos6 suffix))))))
  where
    digits : List Char
    digits = showℕ-dec-chars (rawCanIdℕ cid)
    sig-chars : List Char
    sig-chars = toList (Identifier.name sig)
    pos1 : Position
    pos1 = advancePositions pos (toList "SG_")
    pos2 : Position
    pos2 = advancePosition pos1 ' '
    pos3 : Position
    pos3 = advancePositions pos2 digits
    pos4 : Position
    pos4 = advancePosition pos3 ' '
    pos5 : Position
    pos5 = advancePositions pos4 sig-chars
    pos6 : Position
    pos6 = advancePosition pos5 ' '

-- ============================================================================
-- parseStandardAttrTarget composition for ATgtSignal
-- ============================================================================

private
  parseNodeTgt-fails-on-S :
    ∀ pos rest → parseNodeTgt pos ('S' ∷ rest) ≡ nothing
  parseNodeTgt-fails-on-S _ _ = refl

  parseMsgTgt-fails-on-S :
    ∀ pos rest → parseMsgTgt pos ('S' ∷ rest) ≡ nothing
  parseMsgTgt-fails-on-S _ _ = refl

  parseStandardAttrTarget-on-Signal :
    ∀ pos (cid : CANId) (sig : Identifier) (suffix : List Char)
    → IdentNameStop sig
    → SuffixStops isHSpace suffix
    → parseStandardAttrTarget pos
        ('S' ∷ 'G' ∷ '_' ∷ ' ' ∷ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
          ' ' ∷ toList (Identifier.name sig) ++ₗ ' ' ∷ suffix)
      ≡ just (mkResult (ATgtSignal cid sig)
                (advancePosition
                  (advancePositions
                    (advancePosition
                      (advancePositions
                        (advancePosition
                          (advancePositions pos (toList "SG_"))
                          ' ')
                        (showℕ-dec-chars (rawCanIdℕ cid)))
                      ' ')
                    (toList (Identifier.name sig)))
                  ' ')
                suffix)
  parseStandardAttrTarget-on-Signal pos cid sig suffix sig-stop ss-suffix =
    alt-left-just
      ((parseNodeTgt <|> parseMsgTgt) <|> parseSigTgt) parseEvTgt pos
      sig-input
      _
      (trans (alt-right-nothing
               (parseNodeTgt <|> parseMsgTgt) parseSigTgt pos
               sig-input
               (trans (alt-right-nothing parseNodeTgt parseMsgTgt pos
                        sig-input
                        (parseNodeTgt-fails-on-S pos
                          ('G' ∷ '_' ∷ ' ' ∷ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
                            ' ' ∷ toList (Identifier.name sig) ++ₗ ' ' ∷ suffix)))
                      (parseMsgTgt-fails-on-S pos
                        ('G' ∷ '_' ∷ ' ' ∷ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
                          ' ' ∷ toList (Identifier.name sig) ++ₗ ' ' ∷ suffix))))
             (parseSigTgt-roundtrip pos cid sig suffix sig-stop ss-suffix))
    where
      sig-input : List Char
      sig-input =
        'S' ∷ 'G' ∷ '_' ∷ ' ' ∷ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
          ' ' ∷ toList (Identifier.name sig) ++ₗ ' ' ∷ suffix

  optStandardScope-on-Signal :
    ∀ pos (cid : CANId) (sig : Identifier) (suffix : List Char)
    → IdentNameStop sig
    → SuffixStops isHSpace suffix
    → (parseStandardAttrTarget <|> pure ATgtNetwork) pos
        ('S' ∷ 'G' ∷ '_' ∷ ' ' ∷ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
          ' ' ∷ toList (Identifier.name sig) ++ₗ ' ' ∷ suffix)
      ≡ just (mkResult (ATgtSignal cid sig)
                (advancePosition
                  (advancePositions
                    (advancePosition
                      (advancePositions
                        (advancePosition
                          (advancePositions pos (toList "SG_"))
                          ' ')
                        (showℕ-dec-chars (rawCanIdℕ cid)))
                      ' ')
                    (toList (Identifier.name sig)))
                  ' ')
                suffix)
  optStandardScope-on-Signal pos cid sig suffix sig-stop ss-suffix =
    alt-left-just parseStandardAttrTarget (pure ATgtNetwork) pos
      ('S' ∷ 'G' ∷ '_' ∷ ' ' ∷ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
        ' ' ∷ toList (Identifier.name sig) ++ₗ ' ' ∷ suffix)
      _
      (parseStandardAttrTarget-on-Signal pos cid sig suffix sig-stop ss-suffix)

-- ============================================================================
-- TraceSignal
-- ============================================================================

module TraceSignal (pos : Position) (name : String) (cid : CANId) (sig : Identifier)
                   (value-chars : List Char) (outer-suffix : List Char) where
  cs-name = quoteStringLit-chars name
  cs-id = showℕ-dec-chars (rawCanIdℕ cid)
  cs-sig = toList (Identifier.name sig)

  pos1 : Position
  pos1 = advancePositions pos (toList "BA_")
  pos2 : Position
  pos2 = advancePosition pos1 ' '
  pos3 : Position
  pos3 = advancePositions pos2 cs-name
  pos4 : Position
  pos4 = advancePosition pos3 ' '
  pos4a : Position
  pos4a = advancePositions pos4 (toList "SG_")
  pos4b : Position
  pos4b = advancePosition pos4a ' '
  pos4c : Position
  pos4c = advancePositions pos4b cs-id
  pos4d : Position
  pos4d = advancePosition pos4c ' '
  pos4e : Position
  pos4e = advancePositions pos4d cs-sig
  pos5 : Position
  pos5 = advancePosition pos4e ' '
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
    ' ' ∷ cs-name ++ₗ ' ' ∷ 'S' ∷ 'G' ∷ '_' ∷ ' ' ∷ cs-id ++ₗ
      ' ' ∷ cs-sig ++ₗ ' ' ∷ value-chars ++ₗ rest-tail

  body-after-WS1 : List Char
  body-after-WS1 =
    cs-name ++ₗ ' ' ∷ 'S' ∷ 'G' ∷ '_' ∷ ' ' ∷ cs-id ++ₗ
      ' ' ∷ cs-sig ++ₗ ' ' ∷ value-chars ++ₗ rest-tail

  body-after-name : List Char
  body-after-name =
    ' ' ∷ 'S' ∷ 'G' ∷ '_' ∷ ' ' ∷ cs-id ++ₗ
      ' ' ∷ cs-sig ++ₗ ' ' ∷ value-chars ++ₗ rest-tail

  body-after-WS2 : List Char
  body-after-WS2 =
    'S' ∷ 'G' ∷ '_' ∷ ' ' ∷ cs-id ++ₗ
      ' ' ∷ cs-sig ++ₗ ' ' ∷ value-chars ++ₗ rest-tail

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
-- Parameterised after-keyword for ATgtSignal
-- ============================================================================

parseRawAttrAssign-after-keyword-Signal :
  ∀ pos (name : String) (cid : CANId) (sig : Identifier) (raw-value : RawAttrValue)
    (value-chars : List Char) (outer-suffix : List Char)
  → IdentNameStop sig
  → SuffixStops isNewlineStart outer-suffix
  → SuffixStops isHSpace (value-chars ++ₗ ';' ∷ '\n' ∷ outer-suffix)
  → let open TraceSignal pos name cid sig value-chars outer-suffix in
    parseRawAttrValue pos5 body-after-target
      ≡ just (mkResult raw-value pos6 body-after-value)
  → parseRawAttrAssign pos
      ('B' ∷ 'A' ∷ '_' ∷
        TraceSignal.body-after-keyword pos name cid sig value-chars outer-suffix)
    ≡ just (mkResult (mkRawAttrAssign name (ATgtSignal cid sig) raw-value)
              (TraceSignal.pos9 pos name cid sig value-chars outer-suffix)
              outer-suffix)
parseRawAttrAssign-after-keyword-Signal pos name cid sig raw-value value-chars outer-suffix
  sig-stop ss-NL value-stops-isHSpace value-eq =
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
              (ATgtSignal cid sig) pos5 body-after-target
              (optStandardScope-on-Signal pos4 cid sig
                 (value-chars ++ₗ rest-tail) sig-stop value-stops-isHSpace))
    (trans (bind-just-step parseRawAttrValue
              (λ v → parseWSOpt >>= λ _ →
                     char ';' >>= λ _ →
                     parseNewline >>= λ _ →
                     many parseNewline >>= λ _ →
                     pure (mkRawAttrAssign name (ATgtSignal cid sig) v))
              pos5 body-after-target
              raw-value pos6 body-after-value
              value-eq)
    (trans (bind-just-step parseWSOpt
              (λ _ → char ';' >>= λ _ →
                     parseNewline >>= λ _ →
                     many parseNewline >>= λ _ →
                     pure (mkRawAttrAssign name (ATgtSignal cid sig) raw-value))
              pos6 body-after-value
              [] pos6 body-after-WSOpt
              (parseWSOpt-empty pos6 outer-suffix))
    (trans (bind-just-step (char ';')
              (λ _ → parseNewline >>= λ _ →
                     many parseNewline >>= λ _ →
                     pure (mkRawAttrAssign name (ATgtSignal cid sig) raw-value))
              pos6 body-after-WSOpt
              ';' pos8 body-after-semi
              refl)
    (trans (bind-just-step parseNewline
              (λ _ → many parseNewline >>= λ _ →
                     pure (mkRawAttrAssign name (ATgtSignal cid sig) raw-value))
              pos8 body-after-semi
              '\n' pos9 body-after-NL
              (parseNewline-match-LF pos8 outer-suffix))
    (trans (bind-just-step (many parseNewline)
              (λ _ → pure (mkRawAttrAssign name (ATgtSignal cid sig) raw-value))
              pos9 body-after-NL
              [] pos9 outer-suffix
              (manyHelper-parseNewline-exhaust pos9 outer-suffix
                (length outer-suffix) ss-NL))
      refl)))))))))
  where
    open TraceSignal pos name cid sig value-chars outer-suffix

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
-- Top-level dispatchers: ATgtSignal × {RavString, frac, bareInt}
-- ============================================================================

parseRawAttrAssign-roundtrip-ATgtSignal-RavString :
  ∀ pos (name : String) (cid : CANId) (sig : Identifier) (s : String)
    (outer-suffix : List Char)
  → IdentNameStop sig
  → SuffixStops isNewlineStart outer-suffix
  → parseRawAttrAssign pos
      (toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
        toList " SG_ " ++ₗ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
        ' ' ∷ toList (Identifier.name sig) ++ₗ
        ' ' ∷ quoteStringLit-chars s ++ₗ toList ";\n" ++ₗ outer-suffix)
    ≡ just (mkResult
              (mkRawAttrAssign name (ATgtSignal cid sig) (RavString s))
              (TraceSignal.pos9 pos name cid sig (quoteStringLit-chars s) outer-suffix)
              outer-suffix)
parseRawAttrAssign-roundtrip-ATgtSignal-RavString pos name cid sig s outer-suffix sig-stop ss-NL =
  trans input-eq
    (parseRawAttrAssign-after-keyword-Signal pos name cid sig (RavString s)
      (quoteStringLit-chars s) outer-suffix sig-stop ss-NL
      (value-stops-isHSpace-RavString s outer-suffix)
      value-eq)
  where
    open TraceSignal pos name cid sig (quoteStringLit-chars s) outer-suffix

    input-eq :
      parseRawAttrAssign pos
        (toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
          toList " SG_ " ++ₗ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
          ' ' ∷ toList (Identifier.name sig) ++ₗ
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

parseRawAttrAssign-roundtrip-ATgtSignal-RavDecRatFrac :
  ∀ pos (name : String) (cid : CANId) (sig : Identifier) (d : DecRat)
    (outer-suffix : List Char)
  → IdentNameStop sig
  → SuffixStops isNewlineStart outer-suffix
  → parseRawAttrAssign pos
      (toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
        toList " SG_ " ++ₗ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
        ' ' ∷ toList (Identifier.name sig) ++ₗ
        ' ' ∷ showDecRat-dec-chars d ++ₗ toList ";\n" ++ₗ outer-suffix)
    ≡ just (mkResult
              (mkRawAttrAssign name (ATgtSignal cid sig) (RavDecRat d))
              (TraceSignal.pos9 pos name cid sig (showDecRat-dec-chars d) outer-suffix)
              outer-suffix)
parseRawAttrAssign-roundtrip-ATgtSignal-RavDecRatFrac pos name cid sig d outer-suffix sig-stop ss-NL
  with showDecRat-chars-head-classify d
... | c , tail , head-eq , c-not-quote , _ , _ =
  trans input-eq
    (parseRawAttrAssign-after-keyword-Signal pos name cid sig (RavDecRat d)
      (showDecRat-dec-chars d) outer-suffix sig-stop ss-NL
      (value-stops-isHSpace-RavDecRatFrac d outer-suffix)
      value-eq)
  where
    open TraceSignal pos name cid sig (showDecRat-dec-chars d) outer-suffix

    input-eq :
      parseRawAttrAssign pos
        (toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
          toList " SG_ " ++ₗ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
          ' ' ∷ toList (Identifier.name sig) ++ₗ
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

parseRawAttrAssign-roundtrip-ATgtSignal-RavDecRatBareInt :
  ∀ pos (name : String) (cid : CANId) (sig : Identifier) (z : ℤ)
    (outer-suffix : List Char)
  → IdentNameStop sig
  → SuffixStops isNewlineStart outer-suffix
  → parseRawAttrAssign pos
      (toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
        toList " SG_ " ++ₗ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
        ' ' ∷ toList (Identifier.name sig) ++ₗ
        ' ' ∷ showInt-chars z ++ₗ toList ";\n" ++ₗ outer-suffix)
    ≡ just (mkResult
              (mkRawAttrAssign name (ATgtSignal cid sig) (RavDecRat (fromℤ z)))
              (TraceSignal.pos9 pos name cid sig (showInt-chars z) outer-suffix)
              outer-suffix)
parseRawAttrAssign-roundtrip-ATgtSignal-RavDecRatBareInt pos name cid sig z outer-suffix sig-stop ss-NL
  with showInt-chars-head-classify z
... | c , tail , head-eq , c-not-quote , _ , _ =
  trans input-eq
    (parseRawAttrAssign-after-keyword-Signal pos name cid sig (RavDecRat (fromℤ z))
      (showInt-chars z) outer-suffix sig-stop ss-NL
      (value-stops-isHSpace-RavDecRatBareInt z outer-suffix)
      value-eq)
  where
    open TraceSignal pos name cid sig (showInt-chars z) outer-suffix

    input-eq :
      parseRawAttrAssign pos
        (toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
          toList " SG_ " ++ₗ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
          ' ' ∷ toList (Identifier.name sig) ++ₗ
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
