{-# OPTIONS --safe --without-K #-}

-- B.3.d Layer 3 Commit 3c.3 — `parseRawAttrRel` × {ATgtNodeMsg,
-- ATgtNodeSig} per-line construct roundtrips (6 dispatchers).
--
-- `parseRawAttrRel = "BA_REL_" *> ws *> stringLit *> ws *>
--   parseRelTarget *> rawAttrValue *> wsOpt *> ';' *> '\n' *>
--   many '\n'`.  parseRelTarget = parseNodeMsgTgt <|> parseNodeSigTgt.
--
--   parseNodeMsgTgt = string "BU_BO_REL_" *> ws *> parseIdentifier *>
--                     ws *> parseNatural *> ws *> wrapNodeMsgTarget.
--   parseNodeSigTgt = string "BU_SG_REL_" *> ws *> parseIdentifier *>
--                     ws *> string "SG_" *> ws *> parseNatural *> ws *>
--                     parseIdentifier *> ws *> wrapNodeSigTarget.
--
-- For NodeSig case parseNodeMsgTgt fails on input "BU_SG_REL_..." at the
-- 4th char (`'B'` mismatch with `'S'`), so alt-right-nothing through
-- parseNodeMsgTgt is `refl`.

module Aletheia.DBC.TextParser.Properties.Attributes.Assign.Rel where

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
  ( AttrTarget; ATgtNodeMsg; ATgtNodeSig)
open import Aletheia.DBC.Identifier using (Identifier; isIdentCont)
open import Aletheia.CAN.Frame using (CANId)

open import Aletheia.DBC.TextParser.Attributes
  using (parseRawAttrRel; parseRawAttrValue;
         RawAttrAssign; mkRawAttrAssign;
         RawAttrValue; RavString; RavDecRat;
         parseRelTarget;
         parseNodeMsgTgt; parseNodeSigTgt;
         wrapNodeMsgTarget; wrapNodeSigTarget)
open import Aletheia.DBC.TextParser.Lexer
  using (parseWS; parseWSOpt; parseStringLit; parseNewline;
         parseIdentifier; parseNatural; isHSpace)
open import Aletheia.DBC.TextParser.Topology.Foundations using (buildCANId)

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
-- Common helpers
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

-- ============================================================================
-- wrapNodeMsgTarget-roundtrip / wrapNodeSigTarget-roundtrip
-- ============================================================================

wrapNodeMsgTarget-roundtrip :
  ∀ (n : Identifier) (cid : CANId) (pos : Position) (input : List Char)
  → wrapNodeMsgTarget n (rawCanIdℕ cid) pos input
    ≡ just (mkResult (ATgtNodeMsg n cid) pos input)
wrapNodeMsgTarget-roundtrip n cid pos input
  with buildCANId (rawCanIdℕ cid) | buildCANId-rawCanIdℕ cid
... | just .cid | refl = refl

wrapNodeSigTarget-roundtrip :
  ∀ (n : Identifier) (cid : CANId) (sig : Identifier)
    (pos : Position) (input : List Char)
  → wrapNodeSigTarget n (rawCanIdℕ cid) sig pos input
    ≡ just (mkResult (ATgtNodeSig n cid sig) pos input)
wrapNodeSigTarget-roundtrip n cid sig pos input
  with buildCANId (rawCanIdℕ cid) | buildCANId-rawCanIdℕ cid
... | just .cid | refl = refl

-- ============================================================================
-- parseNodeMsgTgt-roundtrip
-- ============================================================================

parseNodeMsgTgt-roundtrip :
  ∀ pos (n : Identifier) (cid : CANId) (suffix : List Char)
  → IdentNameStop n
  → SuffixStops isHSpace suffix
  → parseNodeMsgTgt pos
      ('B' ∷ 'U' ∷ '_' ∷ 'B' ∷ 'O' ∷ '_' ∷ 'R' ∷ 'E' ∷ 'L' ∷ '_' ∷
        ' ' ∷ Identifier.name n ++ₗ
        ' ' ∷ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ ' ' ∷ suffix)
    ≡ just (mkResult (ATgtNodeMsg n cid)
              (advancePosition
                (advancePositions
                  (advancePosition
                    (advancePositions
                      (advancePosition
                        (advancePositions pos (toList "BU_BO_REL_"))
                        ' ')
                      (Identifier.name n))
                    ' ')
                  (showℕ-dec-chars (rawCanIdℕ cid)))
                ' ')
              suffix)
parseNodeMsgTgt-roundtrip pos n cid suffix n-stop ss-suffix =
  trans (bind-just-step (string "BU_BO_REL_")
           (λ _ → parseWS >>= λ _ →
                  parseIdentifier >>= λ ident →
                  parseWS >>= λ _ →
                  parseNatural >>= λ r →
                  parseWS >>= λ _ →
                  wrapNodeMsgTarget ident r)
           pos
           ('B' ∷ 'U' ∷ '_' ∷ 'B' ∷ 'O' ∷ '_' ∷ 'R' ∷ 'E' ∷ 'L' ∷ '_' ∷
            ' ' ∷ n-chars ++ₗ ' ' ∷ id-chars ++ₗ ' ' ∷ suffix)
           "BU_BO_REL_" pos1
           (' ' ∷ n-chars ++ₗ ' ' ∷ id-chars ++ₗ ' ' ∷ suffix)
           (string-success pos "BU_BO_REL_" _))
  (trans (bind-just-step parseWS
            (λ _ → parseIdentifier >>= λ ident →
                   parseWS >>= λ _ →
                   parseNatural >>= λ r →
                   parseWS >>= λ _ →
                   wrapNodeMsgTarget ident r)
            pos1 (' ' ∷ n-chars ++ₗ ' ' ∷ id-chars ++ₗ ' ' ∷ suffix)
            (' ' ∷ []) pos2 (n-chars ++ₗ ' ' ∷ id-chars ++ₗ ' ' ∷ suffix)
            (parseWS-one-space pos1
               (n-chars ++ₗ ' ' ∷ id-chars ++ₗ ' ' ∷ suffix)
               (ident-name-stops-isHSpace n
                  (' ' ∷ id-chars ++ₗ ' ' ∷ suffix) n-stop)))
  (trans (bind-just-step parseIdentifier
            (λ ident → parseWS >>= λ _ →
                       parseNatural >>= λ r →
                       parseWS >>= λ _ →
                       wrapNodeMsgTarget ident r)
            pos2 (n-chars ++ₗ ' ' ∷ id-chars ++ₗ ' ' ∷ suffix)
            n pos3 (' ' ∷ id-chars ++ₗ ' ' ∷ suffix)
            (parseIdentifier-roundtrip pos2 n
               (' ' ∷ id-chars ++ₗ ' ' ∷ suffix)
               (ws-stops-isIdentCont (id-chars ++ₗ ' ' ∷ suffix))))
  (trans (bind-just-step parseWS
            (λ _ → parseNatural >>= λ r →
                   parseWS >>= λ _ →
                   wrapNodeMsgTarget n r)
            pos3 (' ' ∷ id-chars ++ₗ ' ' ∷ suffix)
            (' ' ∷ []) pos4 (id-chars ++ₗ ' ' ∷ suffix)
            (parseWS-one-space pos3 (id-chars ++ₗ ' ' ∷ suffix)
               (showNat-chars-head-stop-isHSpace (rawCanIdℕ cid) (' ' ∷ suffix))))
  (trans (bind-just-step parseNatural
            (λ r → parseWS >>= λ _ →
                   wrapNodeMsgTarget n r)
            pos4 (id-chars ++ₗ ' ' ∷ suffix)
            (rawCanIdℕ cid) pos5 (' ' ∷ suffix)
            (parseNatural-showNat-chars pos4 (rawCanIdℕ cid)
               (' ' ∷ suffix) (∷-stop refl)))
  (trans (bind-just-step parseWS
            (λ _ → wrapNodeMsgTarget n (rawCanIdℕ cid))
            pos5 (' ' ∷ suffix)
            (' ' ∷ []) pos6 suffix
            (parseWS-one-space pos5 suffix ss-suffix))
    (wrapNodeMsgTarget-roundtrip n cid pos6 suffix))))))
  where
    n-chars : List Char
    n-chars = Identifier.name n
    id-chars : List Char
    id-chars = showℕ-dec-chars (rawCanIdℕ cid)

    pos1 : Position
    pos1 = advancePositions pos (toList "BU_BO_REL_")
    pos2 : Position
    pos2 = advancePosition pos1 ' '
    pos3 : Position
    pos3 = advancePositions pos2 n-chars
    pos4 : Position
    pos4 = advancePosition pos3 ' '
    pos5 : Position
    pos5 = advancePositions pos4 id-chars
    pos6 : Position
    pos6 = advancePosition pos5 ' '

-- ============================================================================
-- parseNodeSigTgt-roundtrip
-- ============================================================================

parseNodeSigTgt-roundtrip :
  ∀ pos (n : Identifier) (cid : CANId) (sig : Identifier) (suffix : List Char)
  → IdentNameStop n → IdentNameStop sig
  → SuffixStops isHSpace suffix
  → parseNodeSigTgt pos
      ('B' ∷ 'U' ∷ '_' ∷ 'S' ∷ 'G' ∷ '_' ∷ 'R' ∷ 'E' ∷ 'L' ∷ '_' ∷
        ' ' ∷ Identifier.name n ++ₗ
        ' ' ∷ 'S' ∷ 'G' ∷ '_' ∷ ' ' ∷ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
        ' ' ∷ Identifier.name sig ++ₗ ' ' ∷ suffix)
    ≡ just (mkResult (ATgtNodeSig n cid sig)
              (advancePosition
                (advancePositions
                  (advancePosition
                    (advancePositions
                      (advancePosition
                        (advancePositions
                          (advancePosition
                            (advancePositions
                              (advancePosition
                                (advancePositions pos (toList "BU_SG_REL_"))
                                ' ')
                              (Identifier.name n))
                            ' ')
                          (toList "SG_"))
                        ' ')
                      (showℕ-dec-chars (rawCanIdℕ cid)))
                    ' ')
                  (Identifier.name sig))
                ' ')
              suffix)
parseNodeSigTgt-roundtrip pos n cid sig suffix n-stop sig-stop ss-suffix =
  trans (bind-just-step (string "BU_SG_REL_")
           cont1
           pos
           ('B' ∷ 'U' ∷ '_' ∷ 'S' ∷ 'G' ∷ '_' ∷ 'R' ∷ 'E' ∷ 'L' ∷ '_' ∷
            ' ' ∷ n-chars ++ₗ ' ' ∷ 'S' ∷ 'G' ∷ '_' ∷ ' ' ∷ id-chars ++ₗ
            ' ' ∷ sig-chars ++ₗ ' ' ∷ suffix)
           "BU_SG_REL_" pos1
           (' ' ∷ n-chars ++ₗ ' ' ∷ 'S' ∷ 'G' ∷ '_' ∷ ' ' ∷ id-chars ++ₗ
             ' ' ∷ sig-chars ++ₗ ' ' ∷ suffix)
           (string-success pos "BU_SG_REL_" _))
  (trans (bind-just-step parseWS
            cont2
            pos1 (' ' ∷ n-chars ++ₗ ' ' ∷ 'S' ∷ 'G' ∷ '_' ∷ ' ' ∷ id-chars ++ₗ
                   ' ' ∷ sig-chars ++ₗ ' ' ∷ suffix)
            (' ' ∷ []) pos2 (n-chars ++ₗ ' ' ∷ 'S' ∷ 'G' ∷ '_' ∷ ' ' ∷ id-chars
                              ++ₗ ' ' ∷ sig-chars ++ₗ ' ' ∷ suffix)
            (parseWS-one-space pos1
               (n-chars ++ₗ ' ' ∷ 'S' ∷ 'G' ∷ '_' ∷ ' ' ∷ id-chars
                  ++ₗ ' ' ∷ sig-chars ++ₗ ' ' ∷ suffix)
               (ident-name-stops-isHSpace n
                  (' ' ∷ 'S' ∷ 'G' ∷ '_' ∷ ' ' ∷ id-chars
                    ++ₗ ' ' ∷ sig-chars ++ₗ ' ' ∷ suffix)
                  n-stop)))
  (trans (bind-just-step parseIdentifier
            cont3
            pos2 (n-chars ++ₗ ' ' ∷ 'S' ∷ 'G' ∷ '_' ∷ ' ' ∷ id-chars
                   ++ₗ ' ' ∷ sig-chars ++ₗ ' ' ∷ suffix)
            n pos3 (' ' ∷ 'S' ∷ 'G' ∷ '_' ∷ ' ' ∷ id-chars
                     ++ₗ ' ' ∷ sig-chars ++ₗ ' ' ∷ suffix)
            (parseIdentifier-roundtrip pos2 n
               (' ' ∷ 'S' ∷ 'G' ∷ '_' ∷ ' ' ∷ id-chars
                 ++ₗ ' ' ∷ sig-chars ++ₗ ' ' ∷ suffix)
               (ws-stops-isIdentCont _)))
  (trans (bind-just-step parseWS
            cont4
            pos3 (' ' ∷ 'S' ∷ 'G' ∷ '_' ∷ ' ' ∷ id-chars
                   ++ₗ ' ' ∷ sig-chars ++ₗ ' ' ∷ suffix)
            (' ' ∷ []) pos4 ('S' ∷ 'G' ∷ '_' ∷ ' ' ∷ id-chars
                              ++ₗ ' ' ∷ sig-chars ++ₗ ' ' ∷ suffix)
            (parseWS-one-space pos3
               ('S' ∷ 'G' ∷ '_' ∷ ' ' ∷ id-chars ++ₗ ' ' ∷ sig-chars ++ₗ ' ' ∷ suffix)
               (∷-stop refl)))
  (trans (bind-just-step (string "SG_")
            cont5
            pos4 ('S' ∷ 'G' ∷ '_' ∷ ' ' ∷ id-chars ++ₗ ' ' ∷ sig-chars
                   ++ₗ ' ' ∷ suffix)
            "SG_" pos5 (' ' ∷ id-chars ++ₗ ' ' ∷ sig-chars ++ₗ ' ' ∷ suffix)
            (string-success pos4 "SG_" _))
  (trans (bind-just-step parseWS
            cont6
            pos5 (' ' ∷ id-chars ++ₗ ' ' ∷ sig-chars ++ₗ ' ' ∷ suffix)
            (' ' ∷ []) pos6 (id-chars ++ₗ ' ' ∷ sig-chars ++ₗ ' ' ∷ suffix)
            (parseWS-one-space pos5
               (id-chars ++ₗ ' ' ∷ sig-chars ++ₗ ' ' ∷ suffix)
               (showNat-chars-head-stop-isHSpace (rawCanIdℕ cid)
                  (' ' ∷ sig-chars ++ₗ ' ' ∷ suffix))))
  (trans (bind-just-step parseNatural
            cont7
            pos6 (id-chars ++ₗ ' ' ∷ sig-chars ++ₗ ' ' ∷ suffix)
            (rawCanIdℕ cid) pos7 (' ' ∷ sig-chars ++ₗ ' ' ∷ suffix)
            (parseNatural-showNat-chars pos6 (rawCanIdℕ cid)
               (' ' ∷ sig-chars ++ₗ ' ' ∷ suffix) (∷-stop refl)))
  (trans (bind-just-step parseWS
            cont8
            pos7 (' ' ∷ sig-chars ++ₗ ' ' ∷ suffix)
            (' ' ∷ []) pos8 (sig-chars ++ₗ ' ' ∷ suffix)
            (parseWS-one-space pos7 (sig-chars ++ₗ ' ' ∷ suffix)
               (ident-name-stops-isHSpace sig (' ' ∷ suffix) sig-stop)))
  (trans (bind-just-step parseIdentifier
            cont9
            pos8 (sig-chars ++ₗ ' ' ∷ suffix)
            sig pos9 (' ' ∷ suffix)
            (parseIdentifier-roundtrip pos8 sig (' ' ∷ suffix)
               (ws-stops-isIdentCont suffix)))
  (trans (bind-just-step parseWS
            cont10
            pos9 (' ' ∷ suffix)
            (' ' ∷ []) pos10 suffix
            (parseWS-one-space pos9 suffix ss-suffix))
    (wrapNodeSigTarget-roundtrip n cid sig pos10 suffix))))))))))
  where
    n-chars : List Char
    n-chars = Identifier.name n
    sig-chars : List Char
    sig-chars = Identifier.name sig
    id-chars : List Char
    id-chars = showℕ-dec-chars (rawCanIdℕ cid)

    pos1 : Position
    pos1 = advancePositions pos (toList "BU_SG_REL_")
    pos2 : Position
    pos2 = advancePosition pos1 ' '
    pos3 : Position
    pos3 = advancePositions pos2 n-chars
    pos4 : Position
    pos4 = advancePosition pos3 ' '
    pos5 : Position
    pos5 = advancePositions pos4 (toList "SG_")
    pos6 : Position
    pos6 = advancePosition pos5 ' '
    pos7 : Position
    pos7 = advancePositions pos6 id-chars
    pos8 : Position
    pos8 = advancePosition pos7 ' '
    pos9 : Position
    pos9 = advancePositions pos8 sig-chars
    pos10 : Position
    pos10 = advancePosition pos9 ' '

    cont1 : String → Parser AttrTarget
    cont1 _ = parseWS >>= λ _ →
              parseIdentifier >>= λ ident →
              parseWS >>= λ _ →
              string "SG_" >>= λ _ →
              parseWS >>= λ _ →
              parseNatural >>= λ r →
              parseWS >>= λ _ →
              parseIdentifier >>= λ s →
              parseWS >>= λ _ →
              wrapNodeSigTarget ident r s

    cont2 : List Char → Parser AttrTarget
    cont2 _ = parseIdentifier >>= λ ident →
              parseWS >>= λ _ →
              string "SG_" >>= λ _ →
              parseWS >>= λ _ →
              parseNatural >>= λ r →
              parseWS >>= λ _ →
              parseIdentifier >>= λ s →
              parseWS >>= λ _ →
              wrapNodeSigTarget ident r s

    cont3 : Identifier → Parser AttrTarget
    cont3 ident = parseWS >>= λ _ →
                  string "SG_" >>= λ _ →
                  parseWS >>= λ _ →
                  parseNatural >>= λ r →
                  parseWS >>= λ _ →
                  parseIdentifier >>= λ s →
                  parseWS >>= λ _ →
                  wrapNodeSigTarget ident r s

    cont4 : List Char → Parser AttrTarget
    cont4 _ = string "SG_" >>= λ _ →
              parseWS >>= λ _ →
              parseNatural >>= λ r →
              parseWS >>= λ _ →
              parseIdentifier >>= λ s →
              parseWS >>= λ _ →
              wrapNodeSigTarget n r s

    cont5 : String → Parser AttrTarget
    cont5 _ = parseWS >>= λ _ →
              parseNatural >>= λ r →
              parseWS >>= λ _ →
              parseIdentifier >>= λ s →
              parseWS >>= λ _ →
              wrapNodeSigTarget n r s

    cont6 : List Char → Parser AttrTarget
    cont6 _ = parseNatural >>= λ r →
              parseWS >>= λ _ →
              parseIdentifier >>= λ s →
              parseWS >>= λ _ →
              wrapNodeSigTarget n r s

    cont7 : ℕ → Parser AttrTarget
    cont7 r = parseWS >>= λ _ →
              parseIdentifier >>= λ s →
              parseWS >>= λ _ →
              wrapNodeSigTarget n r s

    cont8 : List Char → Parser AttrTarget
    cont8 _ = parseIdentifier >>= λ s →
              parseWS >>= λ _ →
              wrapNodeSigTarget n (rawCanIdℕ cid) s

    cont9 : Identifier → Parser AttrTarget
    cont9 s = parseWS >>= λ _ →
              wrapNodeSigTarget n (rawCanIdℕ cid) s

    cont10 : List Char → Parser AttrTarget
    cont10 _ = wrapNodeSigTarget n (rawCanIdℕ cid) sig

-- ============================================================================
-- parseRelTarget composition
-- ============================================================================

private
  parseNodeMsgTgt-fails-on-BUSG :
    ∀ pos rest →
    parseNodeMsgTgt pos ('B' ∷ 'U' ∷ '_' ∷ 'S' ∷ rest) ≡ nothing
  parseNodeMsgTgt-fails-on-BUSG _ _ = refl

  parseRelTarget-on-NodeMsg :
    ∀ pos (n : Identifier) (cid : CANId) (suffix : List Char)
    → IdentNameStop n
    → SuffixStops isHSpace suffix
    → parseRelTarget pos
        ('B' ∷ 'U' ∷ '_' ∷ 'B' ∷ 'O' ∷ '_' ∷ 'R' ∷ 'E' ∷ 'L' ∷ '_' ∷
          ' ' ∷ Identifier.name n ++ₗ
          ' ' ∷ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ ' ' ∷ suffix)
      ≡ just (mkResult (ATgtNodeMsg n cid)
                (advancePosition
                  (advancePositions
                    (advancePosition
                      (advancePositions
                        (advancePosition
                          (advancePositions pos (toList "BU_BO_REL_"))
                          ' ')
                        (Identifier.name n))
                      ' ')
                    (showℕ-dec-chars (rawCanIdℕ cid)))
                  ' ')
                suffix)
  parseRelTarget-on-NodeMsg pos n cid suffix n-stop ss-suffix =
    alt-left-just parseNodeMsgTgt parseNodeSigTgt pos
      ('B' ∷ 'U' ∷ '_' ∷ 'B' ∷ 'O' ∷ '_' ∷ 'R' ∷ 'E' ∷ 'L' ∷ '_' ∷
        ' ' ∷ Identifier.name n ++ₗ
        ' ' ∷ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ ' ' ∷ suffix)
      _
      (parseNodeMsgTgt-roundtrip pos n cid suffix n-stop ss-suffix)

  parseRelTarget-on-NodeSig :
    ∀ pos (n : Identifier) (cid : CANId) (sig : Identifier) (suffix : List Char)
    → IdentNameStop n → IdentNameStop sig
    → SuffixStops isHSpace suffix
    → parseRelTarget pos
        ('B' ∷ 'U' ∷ '_' ∷ 'S' ∷ 'G' ∷ '_' ∷ 'R' ∷ 'E' ∷ 'L' ∷ '_' ∷
          ' ' ∷ Identifier.name n ++ₗ
          ' ' ∷ 'S' ∷ 'G' ∷ '_' ∷ ' ' ∷ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
          ' ' ∷ Identifier.name sig ++ₗ ' ' ∷ suffix)
      ≡ just (mkResult (ATgtNodeSig n cid sig)
                (advancePosition
                  (advancePositions
                    (advancePosition
                      (advancePositions
                        (advancePosition
                          (advancePositions
                            (advancePosition
                              (advancePositions
                                (advancePosition
                                  (advancePositions pos (toList "BU_SG_REL_"))
                                  ' ')
                                (Identifier.name n))
                              ' ')
                            (toList "SG_"))
                          ' ')
                        (showℕ-dec-chars (rawCanIdℕ cid)))
                      ' ')
                    (Identifier.name sig))
                  ' ')
                suffix)
  parseRelTarget-on-NodeSig pos n cid sig suffix n-stop sig-stop ss-suffix =
    trans (alt-right-nothing parseNodeMsgTgt parseNodeSigTgt pos
            ('B' ∷ 'U' ∷ '_' ∷ 'S' ∷ 'G' ∷ '_' ∷ 'R' ∷ 'E' ∷ 'L' ∷ '_' ∷
              ' ' ∷ Identifier.name n ++ₗ
              ' ' ∷ 'S' ∷ 'G' ∷ '_' ∷ ' ' ∷ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
              ' ' ∷ Identifier.name sig ++ₗ ' ' ∷ suffix)
            (parseNodeMsgTgt-fails-on-BUSG pos
              ('G' ∷ '_' ∷ 'R' ∷ 'E' ∷ 'L' ∷ '_' ∷
                ' ' ∷ Identifier.name n ++ₗ
                ' ' ∷ 'S' ∷ 'G' ∷ '_' ∷ ' ' ∷ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
                ' ' ∷ Identifier.name sig ++ₗ ' ' ∷ suffix)))
          (parseNodeSigTgt-roundtrip pos n cid sig suffix n-stop sig-stop ss-suffix)

-- ============================================================================
-- TraceNodeMsg
-- ============================================================================

module TraceNodeMsg (pos : Position) (name : List Char) (n : Identifier) (cid : CANId)
                    (value-chars : List Char) (outer-suffix : List Char) where
  cs-name = quoteStringLit-chars name
  cs-n = Identifier.name n
  cs-id = showℕ-dec-chars (rawCanIdℕ cid)

  pos1 : Position
  pos1 = advancePositions pos (toList "BA_REL_")
  pos2 : Position
  pos2 = advancePosition pos1 ' '
  pos3 : Position
  pos3 = advancePositions pos2 cs-name
  pos4 : Position
  pos4 = advancePosition pos3 ' '
  pos4a : Position
  pos4a = advancePositions pos4 (toList "BU_BO_REL_")
  pos4b : Position
  pos4b = advancePosition pos4a ' '
  pos4c : Position
  pos4c = advancePositions pos4b cs-n
  pos4d : Position
  pos4d = advancePosition pos4c ' '
  pos4e : Position
  pos4e = advancePositions pos4d cs-id
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
    ' ' ∷ cs-name ++ₗ ' ' ∷ 'B' ∷ 'U' ∷ '_' ∷ 'B' ∷ 'O' ∷ '_' ∷ 'R' ∷ 'E' ∷ 'L' ∷ '_' ∷
      ' ' ∷ cs-n ++ₗ ' ' ∷ cs-id ++ₗ ' ' ∷ value-chars ++ₗ rest-tail

  body-after-WS1 : List Char
  body-after-WS1 =
    cs-name ++ₗ ' ' ∷ 'B' ∷ 'U' ∷ '_' ∷ 'B' ∷ 'O' ∷ '_' ∷ 'R' ∷ 'E' ∷ 'L' ∷ '_' ∷
      ' ' ∷ cs-n ++ₗ ' ' ∷ cs-id ++ₗ ' ' ∷ value-chars ++ₗ rest-tail

  body-after-name : List Char
  body-after-name =
    ' ' ∷ 'B' ∷ 'U' ∷ '_' ∷ 'B' ∷ 'O' ∷ '_' ∷ 'R' ∷ 'E' ∷ 'L' ∷ '_' ∷
      ' ' ∷ cs-n ++ₗ ' ' ∷ cs-id ++ₗ ' ' ∷ value-chars ++ₗ rest-tail

  body-after-WS2 : List Char
  body-after-WS2 =
    'B' ∷ 'U' ∷ '_' ∷ 'B' ∷ 'O' ∷ '_' ∷ 'R' ∷ 'E' ∷ 'L' ∷ '_' ∷
      ' ' ∷ cs-n ++ₗ ' ' ∷ cs-id ++ₗ ' ' ∷ value-chars ++ₗ rest-tail

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
-- TraceNodeSig
-- ============================================================================

module TraceNodeSig (pos : Position) (name : List Char) (n : Identifier) (cid : CANId)
                    (sig : Identifier) (value-chars : List Char) (outer-suffix : List Char) where
  cs-name = quoteStringLit-chars name
  cs-n = Identifier.name n
  cs-id = showℕ-dec-chars (rawCanIdℕ cid)
  cs-sig = Identifier.name sig

  pos1 : Position
  pos1 = advancePositions pos (toList "BA_REL_")
  pos2 : Position
  pos2 = advancePosition pos1 ' '
  pos3 : Position
  pos3 = advancePositions pos2 cs-name
  pos4 : Position
  pos4 = advancePosition pos3 ' '
  pos4a : Position
  pos4a = advancePositions pos4 (toList "BU_SG_REL_")
  pos4b : Position
  pos4b = advancePosition pos4a ' '
  pos4c : Position
  pos4c = advancePositions pos4b cs-n
  pos4d : Position
  pos4d = advancePosition pos4c ' '
  pos4e : Position
  pos4e = advancePositions pos4d (toList "SG_")
  pos4f : Position
  pos4f = advancePosition pos4e ' '
  pos4g : Position
  pos4g = advancePositions pos4f cs-id
  pos4h : Position
  pos4h = advancePosition pos4g ' '
  pos4i : Position
  pos4i = advancePositions pos4h cs-sig
  pos5 : Position
  pos5 = advancePosition pos4i ' '
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
    ' ' ∷ cs-name ++ₗ ' ' ∷ 'B' ∷ 'U' ∷ '_' ∷ 'S' ∷ 'G' ∷ '_' ∷ 'R' ∷ 'E' ∷ 'L' ∷ '_' ∷
      ' ' ∷ cs-n ++ₗ ' ' ∷ 'S' ∷ 'G' ∷ '_' ∷ ' ' ∷ cs-id ++ₗ
      ' ' ∷ cs-sig ++ₗ ' ' ∷ value-chars ++ₗ rest-tail

  body-after-WS1 : List Char
  body-after-WS1 =
    cs-name ++ₗ ' ' ∷ 'B' ∷ 'U' ∷ '_' ∷ 'S' ∷ 'G' ∷ '_' ∷ 'R' ∷ 'E' ∷ 'L' ∷ '_' ∷
      ' ' ∷ cs-n ++ₗ ' ' ∷ 'S' ∷ 'G' ∷ '_' ∷ ' ' ∷ cs-id ++ₗ
      ' ' ∷ cs-sig ++ₗ ' ' ∷ value-chars ++ₗ rest-tail

  body-after-name : List Char
  body-after-name =
    ' ' ∷ 'B' ∷ 'U' ∷ '_' ∷ 'S' ∷ 'G' ∷ '_' ∷ 'R' ∷ 'E' ∷ 'L' ∷ '_' ∷
      ' ' ∷ cs-n ++ₗ ' ' ∷ 'S' ∷ 'G' ∷ '_' ∷ ' ' ∷ cs-id ++ₗ
      ' ' ∷ cs-sig ++ₗ ' ' ∷ value-chars ++ₗ rest-tail

  body-after-WS2 : List Char
  body-after-WS2 =
    'B' ∷ 'U' ∷ '_' ∷ 'S' ∷ 'G' ∷ '_' ∷ 'R' ∷ 'E' ∷ 'L' ∷ '_' ∷
      ' ' ∷ cs-n ++ₗ ' ' ∷ 'S' ∷ 'G' ∷ '_' ∷ ' ' ∷ cs-id ++ₗ
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
-- Parameterised after-keyword for ATgtNodeMsg
-- ============================================================================

parseRawAttrRel-after-keyword-NodeMsg :
  ∀ pos (name : List Char) (n : Identifier) (cid : CANId) (raw-value : RawAttrValue)
    (value-chars : List Char) (outer-suffix : List Char)
  → IdentNameStop n
  → SuffixStops isNewlineStart outer-suffix
  → SuffixStops isHSpace (value-chars ++ₗ ';' ∷ '\n' ∷ outer-suffix)
  → let open TraceNodeMsg pos name n cid value-chars outer-suffix in
    parseRawAttrValue pos5 body-after-target
      ≡ just (mkResult raw-value pos6 body-after-value)
  → parseRawAttrRel pos
      ('B' ∷ 'A' ∷ '_' ∷ 'R' ∷ 'E' ∷ 'L' ∷ '_' ∷
        TraceNodeMsg.body-after-keyword pos name n cid value-chars outer-suffix)
    ≡ just (mkResult (mkRawAttrAssign name (ATgtNodeMsg n cid) raw-value)
              (TraceNodeMsg.pos9 pos name n cid value-chars outer-suffix)
              outer-suffix)
parseRawAttrRel-after-keyword-NodeMsg pos name n cid raw-value value-chars outer-suffix
  n-stop ss-NL value-stops-isHSpace value-eq =
    trans (bind-just-step (string "BA_REL_")
           (λ _ → parseWS >>= λ _ →
                  parseStringLit >>= λ qn →
                  parseWS >>= λ _ →
                  parseRelTarget >>= λ t →
                  parseRawAttrValue >>= λ v →
                  parseWSOpt >>= λ _ →
                  char ';' >>= λ _ →
                  parseNewline >>= λ _ →
                  many parseNewline >>= λ _ →
                  pure (mkRawAttrAssign qn t v))
           pos
           ('B' ∷ 'A' ∷ '_' ∷ 'R' ∷ 'E' ∷ 'L' ∷ '_' ∷ body-after-keyword)
           "BA_REL_" pos1 body-after-keyword
           (string-success pos "BA_REL_" body-after-keyword))
    (trans (bind-just-step parseWS
              (λ _ → parseStringLit >>= λ qn →
                     parseWS >>= λ _ →
                     parseRelTarget >>= λ t →
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
                     parseRelTarget >>= λ t →
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
              (λ _ → parseRelTarget >>= λ t →
                     parseRawAttrValue >>= λ v →
                     parseWSOpt >>= λ _ →
                     char ';' >>= λ _ →
                     parseNewline >>= λ _ →
                     many parseNewline >>= λ _ →
                     pure (mkRawAttrAssign name t v))
              pos3 body-after-name
              (' ' ∷ []) pos4 body-after-WS2
              (parseWS-one-space pos3 body-after-WS2 (∷-stop refl)))
    (trans (bind-just-step parseRelTarget
              (λ t → parseRawAttrValue >>= λ v →
                     parseWSOpt >>= λ _ →
                     char ';' >>= λ _ →
                     parseNewline >>= λ _ →
                     many parseNewline >>= λ _ →
                     pure (mkRawAttrAssign name t v))
              pos4 body-after-WS2
              (ATgtNodeMsg n cid) pos5 body-after-target
              (parseRelTarget-on-NodeMsg pos4 n cid
                 (value-chars ++ₗ rest-tail) n-stop value-stops-isHSpace))
    (trans (bind-just-step parseRawAttrValue
              (λ v → parseWSOpt >>= λ _ →
                     char ';' >>= λ _ →
                     parseNewline >>= λ _ →
                     many parseNewline >>= λ _ →
                     pure (mkRawAttrAssign name (ATgtNodeMsg n cid) v))
              pos5 body-after-target
              raw-value pos6 body-after-value
              value-eq)
    (trans (bind-just-step parseWSOpt
              (λ _ → char ';' >>= λ _ →
                     parseNewline >>= λ _ →
                     many parseNewline >>= λ _ →
                     pure (mkRawAttrAssign name (ATgtNodeMsg n cid) raw-value))
              pos6 body-after-value
              [] pos6 body-after-WSOpt
              (parseWSOpt-empty pos6 outer-suffix))
    (trans (bind-just-step (char ';')
              (λ _ → parseNewline >>= λ _ →
                     many parseNewline >>= λ _ →
                     pure (mkRawAttrAssign name (ATgtNodeMsg n cid) raw-value))
              pos6 body-after-WSOpt
              ';' pos8 body-after-semi
              refl)
    (trans (bind-just-step parseNewline
              (λ _ → many parseNewline >>= λ _ →
                     pure (mkRawAttrAssign name (ATgtNodeMsg n cid) raw-value))
              pos8 body-after-semi
              '\n' pos9 body-after-NL
              (parseNewline-match-LF pos8 outer-suffix))
    (trans (bind-just-step (many parseNewline)
              (λ _ → pure (mkRawAttrAssign name (ATgtNodeMsg n cid) raw-value))
              pos9 body-after-NL
              [] pos9 outer-suffix
              (manyHelper-parseNewline-exhaust pos9 outer-suffix
                (length outer-suffix) ss-NL))
      refl)))))))))
  where
    open TraceNodeMsg pos name n cid value-chars outer-suffix

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
-- Parameterised after-keyword for ATgtNodeSig
-- ============================================================================

parseRawAttrRel-after-keyword-NodeSig :
  ∀ pos (name : List Char) (n : Identifier) (cid : CANId) (sig : Identifier)
    (raw-value : RawAttrValue)
    (value-chars : List Char) (outer-suffix : List Char)
  → IdentNameStop n → IdentNameStop sig
  → SuffixStops isNewlineStart outer-suffix
  → SuffixStops isHSpace (value-chars ++ₗ ';' ∷ '\n' ∷ outer-suffix)
  → let open TraceNodeSig pos name n cid sig value-chars outer-suffix in
    parseRawAttrValue pos5 body-after-target
      ≡ just (mkResult raw-value pos6 body-after-value)
  → parseRawAttrRel pos
      ('B' ∷ 'A' ∷ '_' ∷ 'R' ∷ 'E' ∷ 'L' ∷ '_' ∷
        TraceNodeSig.body-after-keyword pos name n cid sig value-chars outer-suffix)
    ≡ just (mkResult (mkRawAttrAssign name (ATgtNodeSig n cid sig) raw-value)
              (TraceNodeSig.pos9 pos name n cid sig value-chars outer-suffix)
              outer-suffix)
parseRawAttrRel-after-keyword-NodeSig pos name n cid sig raw-value value-chars outer-suffix
  n-stop sig-stop ss-NL value-stops-isHSpace value-eq =
    trans (bind-just-step (string "BA_REL_")
           (λ _ → parseWS >>= λ _ →
                  parseStringLit >>= λ qn →
                  parseWS >>= λ _ →
                  parseRelTarget >>= λ t →
                  parseRawAttrValue >>= λ v →
                  parseWSOpt >>= λ _ →
                  char ';' >>= λ _ →
                  parseNewline >>= λ _ →
                  many parseNewline >>= λ _ →
                  pure (mkRawAttrAssign qn t v))
           pos
           ('B' ∷ 'A' ∷ '_' ∷ 'R' ∷ 'E' ∷ 'L' ∷ '_' ∷ body-after-keyword)
           "BA_REL_" pos1 body-after-keyword
           (string-success pos "BA_REL_" body-after-keyword))
    (trans (bind-just-step parseWS
              (λ _ → parseStringLit >>= λ qn →
                     parseWS >>= λ _ →
                     parseRelTarget >>= λ t →
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
                     parseRelTarget >>= λ t →
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
              (λ _ → parseRelTarget >>= λ t →
                     parseRawAttrValue >>= λ v →
                     parseWSOpt >>= λ _ →
                     char ';' >>= λ _ →
                     parseNewline >>= λ _ →
                     many parseNewline >>= λ _ →
                     pure (mkRawAttrAssign name t v))
              pos3 body-after-name
              (' ' ∷ []) pos4 body-after-WS2
              (parseWS-one-space pos3 body-after-WS2 (∷-stop refl)))
    (trans (bind-just-step parseRelTarget
              (λ t → parseRawAttrValue >>= λ v →
                     parseWSOpt >>= λ _ →
                     char ';' >>= λ _ →
                     parseNewline >>= λ _ →
                     many parseNewline >>= λ _ →
                     pure (mkRawAttrAssign name t v))
              pos4 body-after-WS2
              (ATgtNodeSig n cid sig) pos5 body-after-target
              (parseRelTarget-on-NodeSig pos4 n cid sig
                 (value-chars ++ₗ rest-tail) n-stop sig-stop value-stops-isHSpace))
    (trans (bind-just-step parseRawAttrValue
              (λ v → parseWSOpt >>= λ _ →
                     char ';' >>= λ _ →
                     parseNewline >>= λ _ →
                     many parseNewline >>= λ _ →
                     pure (mkRawAttrAssign name (ATgtNodeSig n cid sig) v))
              pos5 body-after-target
              raw-value pos6 body-after-value
              value-eq)
    (trans (bind-just-step parseWSOpt
              (λ _ → char ';' >>= λ _ →
                     parseNewline >>= λ _ →
                     many parseNewline >>= λ _ →
                     pure (mkRawAttrAssign name (ATgtNodeSig n cid sig) raw-value))
              pos6 body-after-value
              [] pos6 body-after-WSOpt
              (parseWSOpt-empty pos6 outer-suffix))
    (trans (bind-just-step (char ';')
              (λ _ → parseNewline >>= λ _ →
                     many parseNewline >>= λ _ →
                     pure (mkRawAttrAssign name (ATgtNodeSig n cid sig) raw-value))
              pos6 body-after-WSOpt
              ';' pos8 body-after-semi
              refl)
    (trans (bind-just-step parseNewline
              (λ _ → many parseNewline >>= λ _ →
                     pure (mkRawAttrAssign name (ATgtNodeSig n cid sig) raw-value))
              pos8 body-after-semi
              '\n' pos9 body-after-NL
              (parseNewline-match-LF pos8 outer-suffix))
    (trans (bind-just-step (many parseNewline)
              (λ _ → pure (mkRawAttrAssign name (ATgtNodeSig n cid sig) raw-value))
              pos9 body-after-NL
              [] pos9 outer-suffix
              (manyHelper-parseNewline-exhaust pos9 outer-suffix
                (length outer-suffix) ss-NL))
      refl)))))))))
  where
    open TraceNodeSig pos name n cid sig value-chars outer-suffix

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
-- Top-level dispatchers: ATgtNodeMsg × {RavString, frac, bareInt}
-- ============================================================================

parseRawAttrRel-roundtrip-ATgtNodeMsg-RavString :
  ∀ pos (name : List Char) (n : Identifier) (cid : CANId) (s : List Char)
    (outer-suffix : List Char)
  → IdentNameStop n
  → SuffixStops isNewlineStart outer-suffix
  → parseRawAttrRel pos
      (toList "BA_REL_ " ++ₗ quoteStringLit-chars name ++ₗ
        toList " BU_BO_REL_ " ++ₗ Identifier.name n ++ₗ
        ' ' ∷ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
        ' ' ∷ quoteStringLit-chars s ++ₗ toList ";\n" ++ₗ outer-suffix)
    ≡ just (mkResult
              (mkRawAttrAssign name (ATgtNodeMsg n cid) (RavString s))
              (TraceNodeMsg.pos9 pos name n cid (quoteStringLit-chars s) outer-suffix)
              outer-suffix)
parseRawAttrRel-roundtrip-ATgtNodeMsg-RavString pos name n cid s outer-suffix n-stop ss-NL =
  trans input-eq
    (parseRawAttrRel-after-keyword-NodeMsg pos name n cid (RavString s)
      (quoteStringLit-chars s) outer-suffix n-stop ss-NL
      (value-stops-isHSpace-RavString s outer-suffix)
      value-eq)
  where
    open TraceNodeMsg pos name n cid (quoteStringLit-chars s) outer-suffix

    input-eq :
      parseRawAttrRel pos
        (toList "BA_REL_ " ++ₗ quoteStringLit-chars name ++ₗ
          toList " BU_BO_REL_ " ++ₗ Identifier.name n ++ₗ
          ' ' ∷ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
          ' ' ∷ quoteStringLit-chars s ++ₗ toList ";\n" ++ₗ outer-suffix)
      ≡ parseRawAttrRel pos
        ('B' ∷ 'A' ∷ '_' ∷ 'R' ∷ 'E' ∷ 'L' ∷ '_' ∷ body-after-keyword)
    input-eq = refl

    value-eq :
      parseRawAttrValue pos5
        (quoteStringLit-chars s ++ₗ ';' ∷ '\n' ∷ outer-suffix)
      ≡ just (mkResult (RavString s) pos6 (';' ∷ '\n' ∷ outer-suffix))
    value-eq = parseRawAttrValue-roundtrip-RavString pos5 s
                 (';' ∷ '\n' ∷ outer-suffix) (∷-stop refl)

parseRawAttrRel-roundtrip-ATgtNodeMsg-RavDecRatFrac :
  ∀ pos (name : List Char) (n : Identifier) (cid : CANId) (d : DecRat)
    (outer-suffix : List Char)
  → IdentNameStop n
  → SuffixStops isNewlineStart outer-suffix
  → parseRawAttrRel pos
      (toList "BA_REL_ " ++ₗ quoteStringLit-chars name ++ₗ
        toList " BU_BO_REL_ " ++ₗ Identifier.name n ++ₗ
        ' ' ∷ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
        ' ' ∷ showDecRat-dec-chars d ++ₗ toList ";\n" ++ₗ outer-suffix)
    ≡ just (mkResult
              (mkRawAttrAssign name (ATgtNodeMsg n cid) (RavDecRat d))
              (TraceNodeMsg.pos9 pos name n cid (showDecRat-dec-chars d) outer-suffix)
              outer-suffix)
parseRawAttrRel-roundtrip-ATgtNodeMsg-RavDecRatFrac pos name n cid d outer-suffix n-stop ss-NL
  with showDecRat-chars-head-classify d
... | c , tail , head-eq , c-not-quote , _ , _ =
  trans input-eq
    (parseRawAttrRel-after-keyword-NodeMsg pos name n cid (RavDecRat d)
      (showDecRat-dec-chars d) outer-suffix n-stop ss-NL
      (value-stops-isHSpace-RavDecRatFrac d outer-suffix)
      value-eq)
  where
    open TraceNodeMsg pos name n cid (showDecRat-dec-chars d) outer-suffix

    input-eq :
      parseRawAttrRel pos
        (toList "BA_REL_ " ++ₗ quoteStringLit-chars name ++ₗ
          toList " BU_BO_REL_ " ++ₗ Identifier.name n ++ₗ
          ' ' ∷ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
          ' ' ∷ showDecRat-dec-chars d ++ₗ toList ";\n" ++ₗ outer-suffix)
      ≡ parseRawAttrRel pos
        ('B' ∷ 'A' ∷ '_' ∷ 'R' ∷ 'E' ∷ 'L' ∷ '_' ∷ body-after-keyword)
    input-eq = refl

    value-eq :
      parseRawAttrValue pos5
        (showDecRat-dec-chars d ++ₗ ';' ∷ '\n' ∷ outer-suffix)
      ≡ just (mkResult (RavDecRat d) pos6 (';' ∷ '\n' ∷ outer-suffix))
    value-eq = parseRawAttrValue-roundtrip-RavDecRatFrac pos5 d
                 (';' ∷ '\n' ∷ outer-suffix) (∷-stop refl)
                 c tail head-eq c-not-quote

parseRawAttrRel-roundtrip-ATgtNodeMsg-RavDecRatBareInt :
  ∀ pos (name : List Char) (n : Identifier) (cid : CANId) (z : ℤ)
    (outer-suffix : List Char)
  → IdentNameStop n
  → SuffixStops isNewlineStart outer-suffix
  → parseRawAttrRel pos
      (toList "BA_REL_ " ++ₗ quoteStringLit-chars name ++ₗ
        toList " BU_BO_REL_ " ++ₗ Identifier.name n ++ₗ
        ' ' ∷ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
        ' ' ∷ showInt-chars z ++ₗ toList ";\n" ++ₗ outer-suffix)
    ≡ just (mkResult
              (mkRawAttrAssign name (ATgtNodeMsg n cid) (RavDecRat (fromℤ z)))
              (TraceNodeMsg.pos9 pos name n cid (showInt-chars z) outer-suffix)
              outer-suffix)
parseRawAttrRel-roundtrip-ATgtNodeMsg-RavDecRatBareInt pos name n cid z outer-suffix n-stop ss-NL
  with showInt-chars-head-classify z
... | c , tail , head-eq , c-not-quote , _ , _ =
  trans input-eq
    (parseRawAttrRel-after-keyword-NodeMsg pos name n cid (RavDecRat (fromℤ z))
      (showInt-chars z) outer-suffix n-stop ss-NL
      (value-stops-isHSpace-RavDecRatBareInt z outer-suffix)
      value-eq)
  where
    open TraceNodeMsg pos name n cid (showInt-chars z) outer-suffix

    input-eq :
      parseRawAttrRel pos
        (toList "BA_REL_ " ++ₗ quoteStringLit-chars name ++ₗ
          toList " BU_BO_REL_ " ++ₗ Identifier.name n ++ₗ
          ' ' ∷ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
          ' ' ∷ showInt-chars z ++ₗ toList ";\n" ++ₗ outer-suffix)
      ≡ parseRawAttrRel pos
        ('B' ∷ 'A' ∷ '_' ∷ 'R' ∷ 'E' ∷ 'L' ∷ '_' ∷ body-after-keyword)
    input-eq = refl

    value-eq :
      parseRawAttrValue pos5
        (showInt-chars z ++ₗ ';' ∷ '\n' ∷ outer-suffix)
      ≡ just (mkResult (RavDecRat (fromℤ z)) pos6 (';' ∷ '\n' ∷ outer-suffix))
    value-eq = parseRawAttrValue-roundtrip-RavDecRatBareInt pos5 z
                 (';' ∷ '\n' ∷ outer-suffix) (∷-stop refl) (λ ())
                 c tail head-eq c-not-quote

-- ============================================================================
-- Top-level dispatchers: ATgtNodeSig × {RavString, frac, bareInt}
-- ============================================================================

parseRawAttrRel-roundtrip-ATgtNodeSig-RavString :
  ∀ pos (name : List Char) (n : Identifier) (cid : CANId) (sig : Identifier) (s : List Char)
    (outer-suffix : List Char)
  → IdentNameStop n → IdentNameStop sig
  → SuffixStops isNewlineStart outer-suffix
  → parseRawAttrRel pos
      (toList "BA_REL_ " ++ₗ quoteStringLit-chars name ++ₗ
        toList " BU_SG_REL_ " ++ₗ Identifier.name n ++ₗ
        toList " SG_ " ++ₗ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
        ' ' ∷ Identifier.name sig ++ₗ
        ' ' ∷ quoteStringLit-chars s ++ₗ toList ";\n" ++ₗ outer-suffix)
    ≡ just (mkResult
              (mkRawAttrAssign name (ATgtNodeSig n cid sig) (RavString s))
              (TraceNodeSig.pos9 pos name n cid sig (quoteStringLit-chars s) outer-suffix)
              outer-suffix)
parseRawAttrRel-roundtrip-ATgtNodeSig-RavString pos name n cid sig s outer-suffix
  n-stop sig-stop ss-NL =
  trans input-eq
    (parseRawAttrRel-after-keyword-NodeSig pos name n cid sig (RavString s)
      (quoteStringLit-chars s) outer-suffix n-stop sig-stop ss-NL
      (value-stops-isHSpace-RavString s outer-suffix)
      value-eq)
  where
    open TraceNodeSig pos name n cid sig (quoteStringLit-chars s) outer-suffix

    input-eq :
      parseRawAttrRel pos
        (toList "BA_REL_ " ++ₗ quoteStringLit-chars name ++ₗ
          toList " BU_SG_REL_ " ++ₗ Identifier.name n ++ₗ
          toList " SG_ " ++ₗ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
          ' ' ∷ Identifier.name sig ++ₗ
          ' ' ∷ quoteStringLit-chars s ++ₗ toList ";\n" ++ₗ outer-suffix)
      ≡ parseRawAttrRel pos
        ('B' ∷ 'A' ∷ '_' ∷ 'R' ∷ 'E' ∷ 'L' ∷ '_' ∷ body-after-keyword)
    input-eq = refl

    value-eq :
      parseRawAttrValue pos5
        (quoteStringLit-chars s ++ₗ ';' ∷ '\n' ∷ outer-suffix)
      ≡ just (mkResult (RavString s) pos6 (';' ∷ '\n' ∷ outer-suffix))
    value-eq = parseRawAttrValue-roundtrip-RavString pos5 s
                 (';' ∷ '\n' ∷ outer-suffix) (∷-stop refl)

parseRawAttrRel-roundtrip-ATgtNodeSig-RavDecRatFrac :
  ∀ pos (name : List Char) (n : Identifier) (cid : CANId) (sig : Identifier) (d : DecRat)
    (outer-suffix : List Char)
  → IdentNameStop n → IdentNameStop sig
  → SuffixStops isNewlineStart outer-suffix
  → parseRawAttrRel pos
      (toList "BA_REL_ " ++ₗ quoteStringLit-chars name ++ₗ
        toList " BU_SG_REL_ " ++ₗ Identifier.name n ++ₗ
        toList " SG_ " ++ₗ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
        ' ' ∷ Identifier.name sig ++ₗ
        ' ' ∷ showDecRat-dec-chars d ++ₗ toList ";\n" ++ₗ outer-suffix)
    ≡ just (mkResult
              (mkRawAttrAssign name (ATgtNodeSig n cid sig) (RavDecRat d))
              (TraceNodeSig.pos9 pos name n cid sig (showDecRat-dec-chars d) outer-suffix)
              outer-suffix)
parseRawAttrRel-roundtrip-ATgtNodeSig-RavDecRatFrac pos name n cid sig d outer-suffix
  n-stop sig-stop ss-NL
  with showDecRat-chars-head-classify d
... | c , tail , head-eq , c-not-quote , _ , _ =
  trans input-eq
    (parseRawAttrRel-after-keyword-NodeSig pos name n cid sig (RavDecRat d)
      (showDecRat-dec-chars d) outer-suffix n-stop sig-stop ss-NL
      (value-stops-isHSpace-RavDecRatFrac d outer-suffix)
      value-eq)
  where
    open TraceNodeSig pos name n cid sig (showDecRat-dec-chars d) outer-suffix

    input-eq :
      parseRawAttrRel pos
        (toList "BA_REL_ " ++ₗ quoteStringLit-chars name ++ₗ
          toList " BU_SG_REL_ " ++ₗ Identifier.name n ++ₗ
          toList " SG_ " ++ₗ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
          ' ' ∷ Identifier.name sig ++ₗ
          ' ' ∷ showDecRat-dec-chars d ++ₗ toList ";\n" ++ₗ outer-suffix)
      ≡ parseRawAttrRel pos
        ('B' ∷ 'A' ∷ '_' ∷ 'R' ∷ 'E' ∷ 'L' ∷ '_' ∷ body-after-keyword)
    input-eq = refl

    value-eq :
      parseRawAttrValue pos5
        (showDecRat-dec-chars d ++ₗ ';' ∷ '\n' ∷ outer-suffix)
      ≡ just (mkResult (RavDecRat d) pos6 (';' ∷ '\n' ∷ outer-suffix))
    value-eq = parseRawAttrValue-roundtrip-RavDecRatFrac pos5 d
                 (';' ∷ '\n' ∷ outer-suffix) (∷-stop refl)
                 c tail head-eq c-not-quote

parseRawAttrRel-roundtrip-ATgtNodeSig-RavDecRatBareInt :
  ∀ pos (name : List Char) (n : Identifier) (cid : CANId) (sig : Identifier) (z : ℤ)
    (outer-suffix : List Char)
  → IdentNameStop n → IdentNameStop sig
  → SuffixStops isNewlineStart outer-suffix
  → parseRawAttrRel pos
      (toList "BA_REL_ " ++ₗ quoteStringLit-chars name ++ₗ
        toList " BU_SG_REL_ " ++ₗ Identifier.name n ++ₗ
        toList " SG_ " ++ₗ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
        ' ' ∷ Identifier.name sig ++ₗ
        ' ' ∷ showInt-chars z ++ₗ toList ";\n" ++ₗ outer-suffix)
    ≡ just (mkResult
              (mkRawAttrAssign name (ATgtNodeSig n cid sig) (RavDecRat (fromℤ z)))
              (TraceNodeSig.pos9 pos name n cid sig (showInt-chars z) outer-suffix)
              outer-suffix)
parseRawAttrRel-roundtrip-ATgtNodeSig-RavDecRatBareInt pos name n cid sig z outer-suffix
  n-stop sig-stop ss-NL
  with showInt-chars-head-classify z
... | c , tail , head-eq , c-not-quote , _ , _ =
  trans input-eq
    (parseRawAttrRel-after-keyword-NodeSig pos name n cid sig (RavDecRat (fromℤ z))
      (showInt-chars z) outer-suffix n-stop sig-stop ss-NL
      (value-stops-isHSpace-RavDecRatBareInt z outer-suffix)
      value-eq)
  where
    open TraceNodeSig pos name n cid sig (showInt-chars z) outer-suffix

    input-eq :
      parseRawAttrRel pos
        (toList "BA_REL_ " ++ₗ quoteStringLit-chars name ++ₗ
          toList " BU_SG_REL_ " ++ₗ Identifier.name n ++ₗ
          toList " SG_ " ++ₗ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
          ' ' ∷ Identifier.name sig ++ₗ
          ' ' ∷ showInt-chars z ++ₗ toList ";\n" ++ₗ outer-suffix)
      ≡ parseRawAttrRel pos
        ('B' ∷ 'A' ∷ '_' ∷ 'R' ∷ 'E' ∷ 'L' ∷ '_' ∷ body-after-keyword)
    input-eq = refl

    value-eq :
      parseRawAttrValue pos5
        (showInt-chars z ++ₗ ';' ∷ '\n' ∷ outer-suffix)
      ≡ just (mkResult (RavDecRat (fromℤ z)) pos6 (';' ∷ '\n' ∷ outer-suffix))
    value-eq = parseRawAttrValue-roundtrip-RavDecRatBareInt pos5 z
                 (';' ∷ '\n' ∷ outer-suffix) (∷-stop refl) (λ ())
                 c tail head-eq c-not-quote
