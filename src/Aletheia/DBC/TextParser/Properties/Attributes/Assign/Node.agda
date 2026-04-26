{-# OPTIONS --without-K #-}

-- B.3.d Layer 3 Commit 3c.3 — `parseRawAttrAssign` × ATgtNode
-- per-line construct roundtrips (3 emit shapes).
--
-- ATgtNode is the `parseNodeTgt` branch of `parseStandardAttrTarget`.
-- The line-shape differs from ATgtNetwork: between qname's trailing
-- space and the value, the formatter emits `BU_<sp>NodeName<sp>`.
--   parseNodeTgt: `string "BU_" *> ws *> parseIdentifier *> ws *>
--                  pure (ATgtNode n)`.
-- Composition lifts result via `alt-left-just` through the 4-fold
-- `<|>` chain in `parseStandardAttrTarget`, then through the outer
-- `<|> pure ATgtNetwork` (another `alt-left-just`).
--
-- Per-call precondition `IdentNameStop`: identifier's first char is
-- non-isHSpace.  Owed at Layer 4 universally from `validIdentifierᵇ`
-- via the `isIdentStart c → isHSpace c ≡ false` bridge (mirrors
-- `Topology/Nodes.agda`'s `NodeNameStop`).

module Aletheia.DBC.TextParser.Properties.Attributes.Assign.Node where

open import Data.Bool using (Bool; true; false; T)
open import Data.Char using (Char)
open import Data.Char.Base using (_≈ᵇ_)
open import Data.Integer using (ℤ; +_; -[1+_])
open import Data.List using (List; []; _∷_; length) renaming (_++_ to _++ₗ_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_)
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
open import Aletheia.DBC.Identifier using (Identifier; isIdentCont)

open import Aletheia.DBC.TextParser.Attributes
  using (parseRawAttrAssign; parseRawAttrValue;
         RawAttrAssign; mkRawAttrAssign;
         RawAttrValue; RavString; RavDecRat;
         parseStandardAttrTarget;
         parseNodeTgt; parseMsgTgt; parseSigTgt; parseEvTgt)
open import Aletheia.DBC.TextParser.Lexer
  using (parseWS; parseWSOpt; parseStringLit; parseNewline; parseIdentifier;
         isHSpace)

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

-- ============================================================================
-- IdentNameStop precondition: identifier's first char is non-isHSpace
-- ============================================================================
--
-- Owed at Layer 4 universally from `validIdentifierᵇ` (mirrors
-- `Topology/Nodes.agda`'s `NodeNameStop`).

IdentNameStop : Identifier → Set
IdentNameStop n =
  Σ[ c ∈ Char ] Σ[ cs ∈ List Char ]
    (toList (Identifier.name n) ≡ c ∷ cs) × (isHSpace c ≡ false)

-- ============================================================================
-- parseNodeTgt-roundtrip
-- ============================================================================

private
  ws-stops-isIdentCont : ∀ rest → SuffixStops isIdentCont (' ' ∷ rest)
  ws-stops-isIdentCont _ = ∷-stop refl

  -- Identifier-name-prefix stop using IdentNameStop witness.
  ident-name-stops-isHSpace :
    ∀ (n : Identifier) (rest : List Char)
    → IdentNameStop n
    → SuffixStops isHSpace (toList (Identifier.name n) ++ₗ rest)
  ident-name-stops-isHSpace n rest (c , cs , cs-eq , c-not-hsp) =
    subst (λ chars → SuffixStops isHSpace (chars ++ₗ rest))
          (sym cs-eq) (∷-stop c-not-hsp)

parseNodeTgt-roundtrip :
  ∀ pos (n : Identifier) (suffix : List Char)
  → IdentNameStop n
  → SuffixStops isHSpace suffix
  → parseNodeTgt pos
      ('B' ∷ 'U' ∷ '_' ∷ ' ' ∷ toList (Identifier.name n) ++ₗ ' ' ∷ suffix)
    ≡ just (mkResult (ATgtNode n)
              (advancePosition
                (advancePositions
                  (advancePosition
                    (advancePositions pos (toList "BU_"))
                    ' ')
                  (toList (Identifier.name n)))
                ' ')
              suffix)
parseNodeTgt-roundtrip pos n suffix ident-stop ss-suffix =
  trans (bind-just-step (string "BU_")
           (λ _ → parseWS >>= λ _ →
                  parseIdentifier >>= λ ident →
                  parseWS >>= λ _ →
                  pure (ATgtNode ident))
           pos
           ('B' ∷ 'U' ∷ '_' ∷ ' ' ∷ toList (Identifier.name n) ++ₗ ' ' ∷ suffix)
           "BU_" pos1 (' ' ∷ toList (Identifier.name n) ++ₗ ' ' ∷ suffix)
           (string-success pos "BU_"
              (' ' ∷ toList (Identifier.name n) ++ₗ ' ' ∷ suffix)))
  (trans (bind-just-step parseWS
            (λ _ → parseIdentifier >>= λ ident →
                   parseWS >>= λ _ →
                   pure (ATgtNode ident))
            pos1 (' ' ∷ toList (Identifier.name n) ++ₗ ' ' ∷ suffix)
            (' ' ∷ []) pos2 (toList (Identifier.name n) ++ₗ ' ' ∷ suffix)
            (parseWS-one-space pos1
               (toList (Identifier.name n) ++ₗ ' ' ∷ suffix)
               (ident-name-stops-isHSpace n (' ' ∷ suffix) ident-stop)))
  (trans (bind-just-step parseIdentifier
            (λ ident → parseWS >>= λ _ →
                       pure (ATgtNode ident))
            pos2 (toList (Identifier.name n) ++ₗ ' ' ∷ suffix)
            n pos3 (' ' ∷ suffix)
            (parseIdentifier-roundtrip pos2 n (' ' ∷ suffix)
               (ws-stops-isIdentCont suffix)))
  (trans (bind-just-step parseWS
            (λ _ → pure (ATgtNode n))
            pos3 (' ' ∷ suffix)
            (' ' ∷ []) pos4 suffix
            (parseWS-one-space pos3 suffix ss-suffix))
    refl)))
  where
    pos1 : Position
    pos1 = advancePositions pos (toList "BU_")
    pos2 : Position
    pos2 = advancePosition pos1 ' '
    pos3 : Position
    pos3 = advancePositions pos2 (toList (Identifier.name n))
    pos4 : Position
    pos4 = advancePosition pos3 ' '

-- ============================================================================
-- target-eq for ATgtNode: lift parseNodeTgt-roundtrip through
-- parseStandardAttrTarget (4-fold <|>) and pure ATgtNetwork (outer <|>).
-- ============================================================================

private
  -- Lift parseNodeTgt success through the 4-fold <|> chain.
  -- parseStandardAttrTarget = ((parseNodeTgt <|> parseMsgTgt) <|>
  --   parseSigTgt) <|> parseEvTgt (left-associative).
  parseStandardAttrTarget-on-Node :
    ∀ pos (n : Identifier) (suffix : List Char)
    → IdentNameStop n
    → SuffixStops isHSpace suffix
    → parseStandardAttrTarget pos
        ('B' ∷ 'U' ∷ '_' ∷ ' ' ∷ toList (Identifier.name n) ++ₗ ' ' ∷ suffix)
      ≡ just (mkResult (ATgtNode n)
                (advancePosition
                  (advancePositions
                    (advancePosition
                      (advancePositions pos (toList "BU_"))
                      ' ')
                    (toList (Identifier.name n)))
                  ' ')
                suffix)
  parseStandardAttrTarget-on-Node pos n suffix ident-stop ss-suffix =
    alt-left-just
      ((parseNodeTgt <|> parseMsgTgt) <|> parseSigTgt)
      parseEvTgt pos
      ('B' ∷ 'U' ∷ '_' ∷ ' ' ∷ toList (Identifier.name n) ++ₗ ' ' ∷ suffix)
      _
      (alt-left-just
         (parseNodeTgt <|> parseMsgTgt)
         parseSigTgt pos
         ('B' ∷ 'U' ∷ '_' ∷ ' ' ∷ toList (Identifier.name n) ++ₗ ' ' ∷ suffix)
         _
         (alt-left-just
            parseNodeTgt parseMsgTgt pos
            ('B' ∷ 'U' ∷ '_' ∷ ' ' ∷ toList (Identifier.name n) ++ₗ ' ' ∷ suffix)
            _
            (parseNodeTgt-roundtrip pos n suffix ident-stop ss-suffix)))

  -- Outer fall-through to pure ATgtNetwork.
  optStandardScope-on-Node :
    ∀ pos (n : Identifier) (suffix : List Char)
    → IdentNameStop n
    → SuffixStops isHSpace suffix
    → (parseStandardAttrTarget <|> pure ATgtNetwork) pos
        ('B' ∷ 'U' ∷ '_' ∷ ' ' ∷ toList (Identifier.name n) ++ₗ ' ' ∷ suffix)
      ≡ just (mkResult (ATgtNode n)
                (advancePosition
                  (advancePositions
                    (advancePosition
                      (advancePositions pos (toList "BU_"))
                      ' ')
                    (toList (Identifier.name n)))
                  ' ')
                suffix)
  optStandardScope-on-Node pos n suffix ident-stop ss-suffix =
    alt-left-just parseStandardAttrTarget (pure ATgtNetwork) pos
      ('B' ∷ 'U' ∷ '_' ∷ ' ' ∷ toList (Identifier.name n) ++ₗ ' ' ∷ suffix)
      _
      (parseStandardAttrTarget-on-Node pos n suffix ident-stop ss-suffix)

-- ============================================================================
-- TraceNode: position trace for parseRawAttrAssign × ATgtNode
-- ============================================================================

module TraceNode (pos : Position) (name : String) (n : Identifier)
                 (value-chars : List Char) (outer-suffix : List Char) where
  cs-name = quoteStringLit-chars name
  cs-node = toList (Identifier.name n)

  pos1 : Position  -- after string "BA_"
  pos1 = advancePositions pos (toList "BA_")

  pos2 : Position  -- after parseWS
  pos2 = advancePosition pos1 ' '

  pos3 : Position  -- after parseStringLit (qname)
  pos3 = advancePositions pos2 cs-name

  pos4 : Position  -- after parseWS (space before BU_)
  pos4 = advancePosition pos3 ' '

  -- pos5 = pos4 + advancePositions over BU_<sp>NodeName<sp>
  pos4a : Position  -- after string "BU_"
  pos4a = advancePositions pos4 (toList "BU_")

  pos4b : Position  -- after parseWS (space after BU_)
  pos4b = advancePosition pos4a ' '

  pos4c : Position  -- after parseIdentifier (NodeName)
  pos4c = advancePositions pos4b cs-node

  pos5 : Position  -- after parseWS (space after NodeName)
  pos5 = advancePosition pos4c ' '

  pos6 : Position  -- after parseRawAttrValue
  pos6 = advancePositions pos5 value-chars

  -- pos7 = pos6 (parseWSOpt 0 iter on ';' head)
  pos8 : Position  -- after char ';'
  pos8 = advancePosition pos6 ';'

  pos9 : Position  -- after parseNewline
  pos9 = advancePosition pos8 '\n'

  rest-tail : List Char
  rest-tail = ';' ∷ '\n' ∷ outer-suffix

  body-after-keyword : List Char
  body-after-keyword =
    ' ' ∷ cs-name ++ₗ ' ' ∷ 'B' ∷ 'U' ∷ '_' ∷ ' ' ∷ cs-node ++ₗ
      ' ' ∷ value-chars ++ₗ rest-tail

  body-after-WS1 : List Char
  body-after-WS1 =
    cs-name ++ₗ ' ' ∷ 'B' ∷ 'U' ∷ '_' ∷ ' ' ∷ cs-node ++ₗ
      ' ' ∷ value-chars ++ₗ rest-tail

  body-after-name : List Char
  body-after-name =
    ' ' ∷ 'B' ∷ 'U' ∷ '_' ∷ ' ' ∷ cs-node ++ₗ
      ' ' ∷ value-chars ++ₗ rest-tail

  body-after-WS2 : List Char
  body-after-WS2 =
    'B' ∷ 'U' ∷ '_' ∷ ' ' ∷ cs-node ++ₗ ' ' ∷ value-chars ++ₗ rest-tail

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
-- Parameterised after-keyword for ATgtNode case
-- ============================================================================

parseRawAttrAssign-after-keyword-Node :
  ∀ pos (name : String) (n : Identifier) (raw-value : RawAttrValue)
    (value-chars : List Char) (outer-suffix : List Char)
  → IdentNameStop n
  → SuffixStops isNewlineStart outer-suffix
  → SuffixStops isHSpace (value-chars ++ₗ ';' ∷ '\n' ∷ outer-suffix)
  → let open TraceNode pos name n value-chars outer-suffix in
    parseRawAttrValue pos5 body-after-target
      ≡ just (mkResult raw-value pos6 body-after-value)
  → parseRawAttrAssign pos
      ('B' ∷ 'A' ∷ '_' ∷ TraceNode.body-after-keyword pos name n value-chars outer-suffix)
    ≡ just (mkResult (mkRawAttrAssign name (ATgtNode n) raw-value)
              (TraceNode.pos9 pos name n value-chars outer-suffix)
              outer-suffix)
parseRawAttrAssign-after-keyword-Node pos name n raw-value value-chars outer-suffix
  ident-stop ss-NL value-stops-isHSpace value-eq =
    -- Step 1: string "BA_"
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
    -- Step 2: parseWS consumes ' '.
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
    -- Step 3: parseStringLit reads name.
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
              (parseWS-one-space pos3 body-after-WS2 (∷-stop refl)))
    -- Step 5: parseStandardAttrTarget succeeds with ATgtNode n.
    (trans (bind-just-step (parseStandardAttrTarget <|> pure ATgtNetwork)
              (λ t → parseRawAttrValue >>= λ v →
                     parseWSOpt >>= λ _ →
                     char ';' >>= λ _ →
                     parseNewline >>= λ _ →
                     many parseNewline >>= λ _ →
                     pure (mkRawAttrAssign name t v))
              pos4 body-after-WS2
              (ATgtNode n) pos5 body-after-target
              (optStandardScope-on-Node pos4 n
                 (value-chars ++ₗ rest-tail)
                 ident-stop value-stops-isHSpace))
    -- Step 6: parseRawAttrValue.
    (trans (bind-just-step parseRawAttrValue
              (λ v → parseWSOpt >>= λ _ →
                     char ';' >>= λ _ →
                     parseNewline >>= λ _ →
                     many parseNewline >>= λ _ →
                     pure (mkRawAttrAssign name (ATgtNode n) v))
              pos5 body-after-target
              raw-value pos6 body-after-value
              value-eq)
    -- Step 7: parseWSOpt consumes 0 spaces.
    (trans (bind-just-step parseWSOpt
              (λ _ → char ';' >>= λ _ →
                     parseNewline >>= λ _ →
                     many parseNewline >>= λ _ →
                     pure (mkRawAttrAssign name (ATgtNode n) raw-value))
              pos6 body-after-value
              [] pos6 body-after-WSOpt
              (parseWSOpt-empty pos6 outer-suffix))
    -- Step 8: char ';'.
    (trans (bind-just-step (char ';')
              (λ _ → parseNewline >>= λ _ →
                     many parseNewline >>= λ _ →
                     pure (mkRawAttrAssign name (ATgtNode n) raw-value))
              pos6 body-after-WSOpt
              ';' pos8 body-after-semi
              refl)
    -- Step 9: parseNewline.
    (trans (bind-just-step parseNewline
              (λ _ → many parseNewline >>= λ _ →
                     pure (mkRawAttrAssign name (ATgtNode n) raw-value))
              pos8 body-after-semi
              '\n' pos9 body-after-NL
              (parseNewline-match-LF pos8 outer-suffix))
    -- Step 10: many parseNewline 0 iterations.
    (trans (bind-just-step (many parseNewline)
              (λ _ → pure (mkRawAttrAssign name (ATgtNode n) raw-value))
              pos9 body-after-NL
              [] pos9 outer-suffix
              (manyHelper-parseNewline-exhaust pos9 outer-suffix
                (length outer-suffix) ss-NL))
      refl)))))))))
  where
    open TraceNode pos name n value-chars outer-suffix

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
-- Top-level dispatchers: ATgtNode × {RavString, frac, bareInt}
-- ============================================================================

parseRawAttrAssign-roundtrip-ATgtNode-RavString :
  ∀ pos (name : String) (n : Identifier) (s : String) (outer-suffix : List Char)
  → IdentNameStop n
  → SuffixStops isNewlineStart outer-suffix
  → parseRawAttrAssign pos
      (toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
        toList " BU_ " ++ₗ toList (Identifier.name n) ++ₗ
        ' ' ∷ quoteStringLit-chars s ++ₗ toList ";\n" ++ₗ outer-suffix)
    ≡ just (mkResult
              (mkRawAttrAssign name (ATgtNode n) (RavString s))
              (TraceNode.pos9 pos name n (quoteStringLit-chars s) outer-suffix)
              outer-suffix)
parseRawAttrAssign-roundtrip-ATgtNode-RavString pos name n s outer-suffix ident-stop ss-NL =
  trans input-eq
    (parseRawAttrAssign-after-keyword-Node pos name n (RavString s)
      (quoteStringLit-chars s) outer-suffix ident-stop ss-NL
      (value-stops-isHSpace-RavString s outer-suffix)
      value-eq)
  where
    open TraceNode pos name n (quoteStringLit-chars s) outer-suffix

    input-eq :
      parseRawAttrAssign pos
        (toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
          toList " BU_ " ++ₗ toList (Identifier.name n) ++ₗ
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

parseRawAttrAssign-roundtrip-ATgtNode-RavDecRatFrac :
  ∀ pos (name : String) (n : Identifier) (d : DecRat) (outer-suffix : List Char)
  → IdentNameStop n
  → SuffixStops isNewlineStart outer-suffix
  → parseRawAttrAssign pos
      (toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
        toList " BU_ " ++ₗ toList (Identifier.name n) ++ₗ
        ' ' ∷ showDecRat-dec-chars d ++ₗ toList ";\n" ++ₗ outer-suffix)
    ≡ just (mkResult
              (mkRawAttrAssign name (ATgtNode n) (RavDecRat d))
              (TraceNode.pos9 pos name n (showDecRat-dec-chars d) outer-suffix)
              outer-suffix)
parseRawAttrAssign-roundtrip-ATgtNode-RavDecRatFrac pos name n d outer-suffix ident-stop ss-NL
  with showDecRat-chars-head-classify d
... | c , tail , head-eq , c-not-quote , _ , _ =
  trans input-eq
    (parseRawAttrAssign-after-keyword-Node pos name n (RavDecRat d)
      (showDecRat-dec-chars d) outer-suffix ident-stop ss-NL
      (value-stops-isHSpace-RavDecRatFrac d outer-suffix)
      value-eq)
  where
    open TraceNode pos name n (showDecRat-dec-chars d) outer-suffix

    input-eq :
      parseRawAttrAssign pos
        (toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
          toList " BU_ " ++ₗ toList (Identifier.name n) ++ₗ
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

parseRawAttrAssign-roundtrip-ATgtNode-RavDecRatBareInt :
  ∀ pos (name : String) (n : Identifier) (z : ℤ) (outer-suffix : List Char)
  → IdentNameStop n
  → SuffixStops isNewlineStart outer-suffix
  → parseRawAttrAssign pos
      (toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
        toList " BU_ " ++ₗ toList (Identifier.name n) ++ₗ
        ' ' ∷ showInt-chars z ++ₗ toList ";\n" ++ₗ outer-suffix)
    ≡ just (mkResult
              (mkRawAttrAssign name (ATgtNode n) (RavDecRat (fromℤ z)))
              (TraceNode.pos9 pos name n (showInt-chars z) outer-suffix)
              outer-suffix)
parseRawAttrAssign-roundtrip-ATgtNode-RavDecRatBareInt pos name n z outer-suffix ident-stop ss-NL
  with showInt-chars-head-classify z
... | c , tail , head-eq , c-not-quote , _ , _ =
  trans input-eq
    (parseRawAttrAssign-after-keyword-Node pos name n (RavDecRat (fromℤ z))
      (showInt-chars z) outer-suffix ident-stop ss-NL
      (value-stops-isHSpace-RavDecRatBareInt z outer-suffix)
      value-eq)
  where
    open TraceNode pos name n (showInt-chars z) outer-suffix

    input-eq :
      parseRawAttrAssign pos
        (toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
          toList " BU_ " ++ₗ toList (Identifier.name n) ++ₗ
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
