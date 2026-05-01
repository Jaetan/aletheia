{-# OPTIONS --safe --without-K #-}

-- B.3.d Layer 3 3d.5.d 3c-B — `parseRawAttrRel` × {ATgtNodeMsg, ATgtNodeSig}
-- per-line construct roundtrips (6 dispatchers), η-style migration onto the
-- universal `parseAttrRel-format-roundtrip` lemma.
--
-- ATgtNodeMsg / ATgtNodeSig are the two arms of `RawRelTargetWire`, routed
-- through the `nodeMsgArm` / `nodeSigArm` of `relTargetWireFmt`'s 2-way
-- altSum.  buildAttrRelP discharges `with buildCANId raw |
-- buildCANId-rawCanIdℕ cid` on `raw = rawCanIdℕ cid`.
--
-- Both targets carry an `IdentNameStop` precondition for the node identifier;
-- NodeSig additionally requires it for the signal identifier.  Layer 4 owes
-- both from `validIdentifierᵇ`.

module Aletheia.DBC.TextParser.Properties.Attributes.Assign.Rel where

open import Data.Bool using (Bool; true; false; T)
open import Data.Char using (Char)
open import Data.Char.Base using (_≈ᵇ_; isDigit)
open import Data.Integer using (ℤ; +_; -[1+_])
open import Data.List using (List; []; _∷_; length) renaming (_++_ to _++ₗ_)
open import Data.List.Properties using () renaming (++-assoc to ++ₗ-assoc; length-++ to length-++ₗ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (∃₂; _,_; Σ; Σ-syntax; _×_; proj₁; proj₂)
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
open import Aletheia.DBC.DecRat.Refinement using
  (IntDecRat; mkIntDecRatFromℤ; intDecRatToℤ;
   intDecRatToℤ-mkIntDecRatFromℤ)
open import Aletheia.DBC.Types using
  ( AttrTarget; ATgtNetwork; ATgtNode; ATgtMessage; ATgtSignal; ATgtEnvVar
  ; ATgtNodeMsg; ATgtNodeSig)
open import Aletheia.DBC.Identifier using (Identifier)
open import Aletheia.CAN.Frame using (CANId)

open import Aletheia.DBC.TextParser.Attributes
  using (parseRawAttrRel;
         RawAttrAssign; mkRawAttrAssign;
         RawAttrValue; RavString; RavDecRat;
         liftRavw; buildAttrRelP)
open import Aletheia.DBC.TextParser.Lexer
  using (parseWS; parseWSOpt; parseStringLit; parseNewline;
         isHSpace)
open import Aletheia.DBC.TextParser.Topology.Foundations using (buildCANId)

open import Aletheia.DBC.TextFormatter.Emitter
  using (quoteStringLit-chars; showDecRat-dec-chars; showInt-chars;
         showℕ-dec-chars; digitChar)
open import Aletheia.DBC.TextFormatter.Topology using (rawCanIdℕ)

open import Aletheia.DBC.TextParser.DecRatParse.Properties using
  ( bind-just-step
  ; SuffixStops; ∷-stop; []-stop)
open import Aletheia.DBC.TextParser.Properties.Preamble.Newline using
  ( isNewlineStart
  ; manyHelper-parseNewline-exhaust)
open import Aletheia.DBC.TextParser.Properties.Comments.Comment using
  ( buildCANId-rawCanIdℕ)
open import Aletheia.DBC.TextParser.Properties.Attributes.Assign.Common using
  ( value-stops-isHSpace-RavString
  ; value-stops-isHSpace-RavDecRatFrac
  ; value-stops-isHSpace-RavDecRatBareInt)
open import Aletheia.DBC.TextParser.Properties.Attributes.Assign.Node using
  ( IdentNameStop)

open import Aletheia.DBC.TextParser.Format using
  (Format; emit; parse; EmitsOK; nat)
open import Aletheia.DBC.TextParser.Format.AttrValue using
  (RawAttrValueWire; RavwString; RavwFrac; RavwBareInt;
   attrValueWireFmt;
   build-EmitsOK-RavwString;
   build-EmitsOK-RavwFrac;
   build-EmitsOK-RavwBareInt)
open import Aletheia.DBC.TextParser.Format.AttrLine using
  (attrRelFmt; AttrRelCarrier;
   relTargetWireFmt; RrtNodeMsg; RrtNodeSig;
   parseAttrRel-format-roundtrip;
   emit-attrRelFmt-RrtNodeMsg;
   emit-attrRelFmt-RrtNodeMsg-with-outer;
   emit-attrRelFmt-RrtNodeSig;
   emit-attrRelFmt-RrtNodeSig-with-outer;
   build-EmitsOK-relTargetWireFmt-RrtNodeMsg;
   build-EmitsOK-relTargetWireFmt-RrtNodeSig)

-- ============================================================================
-- TRACE MODULES — kept for `Properties/Attributes/Line.agda` compatibility
-- ============================================================================

module TraceNodeMsg (pos : Position) (name : List Char) (n : Identifier) (cid : CANId)
                    (value-chars : List Char) (outer-suffix : List Char) where
  cs-name : List Char
  cs-name = quoteStringLit-chars name

  cs-n : List Char
  cs-n = Identifier.name n

  cs-id : List Char
  cs-id = showℕ-dec-chars (rawCanIdℕ cid)

  pos9 : Position
  pos9 = advancePositions pos
           (toList "BA_REL_ " ++ₗ cs-name ++ₗ
            toList " BU_BO_REL_ " ++ₗ cs-n ++ₗ
            ' ' ∷ cs-id ++ₗ
            ' ' ∷ value-chars ++ₗ ';' ∷ '\n' ∷ [])

module TraceNodeSig (pos : Position) (name : List Char) (n : Identifier) (cid : CANId)
                    (sig : Identifier)
                    (value-chars : List Char) (outer-suffix : List Char) where
  cs-name : List Char
  cs-name = quoteStringLit-chars name

  cs-n : List Char
  cs-n = Identifier.name n

  cs-id : List Char
  cs-id = showℕ-dec-chars (rawCanIdℕ cid)

  cs-sig : List Char
  cs-sig = Identifier.name sig

  pos9 : Position
  pos9 = advancePositions pos
           (toList "BA_REL_ " ++ₗ cs-name ++ₗ
            toList " BU_SG_REL_ " ++ₗ cs-n ++ₗ
            ' ' ∷ toList "SG_ " ++ₗ cs-id ++ₗ
            ' ' ∷ cs-sig ++ₗ
            ' ' ∷ value-chars ++ₗ ';' ∷ '\n' ∷ [])

-- ============================================================================
-- BRIDGES — emit form ↔ inline-input shape
-- ============================================================================

private
  bridge-NodeMsg-emit :
    ∀ (name : List Char) (idn : Identifier) (raw : ℕ)
      (wireVal : RawAttrValueWire) (outer-suffix : List Char)
    → emit attrRelFmt (name , RrtNodeMsg idn raw , wireVal , tt) ++ₗ outer-suffix
      ≡ toList "BA_REL_ " ++ₗ quoteStringLit-chars name ++ₗ
          toList " BU_BO_REL_ " ++ₗ Identifier.name idn ++ₗ
          ' ' ∷ emit nat raw ++ₗ
          ' ' ∷ emit attrValueWireFmt wireVal ++ₗ ';' ∷ '\n' ∷ outer-suffix
  bridge-NodeMsg-emit = emit-attrRelFmt-RrtNodeMsg-with-outer

  bridge-NodeSig-emit :
    ∀ (name : List Char) (idn : Identifier) (raw : ℕ) (sig : Identifier)
      (wireVal : RawAttrValueWire) (outer-suffix : List Char)
    → emit attrRelFmt (name , RrtNodeSig idn raw sig , wireVal , tt) ++ₗ outer-suffix
      ≡ toList "BA_REL_ " ++ₗ quoteStringLit-chars name ++ₗ
          toList " BU_SG_REL_ " ++ₗ Identifier.name idn ++ₗ
          ' ' ∷ toList "SG_ " ++ₗ emit nat raw ++ₗ
          ' ' ∷ Identifier.name sig ++ₗ
          ' ' ∷ emit attrValueWireFmt wireVal ++ₗ ';' ∷ '\n' ∷ outer-suffix
  bridge-NodeSig-emit = emit-attrRelFmt-RrtNodeSig-with-outer

-- ============================================================================
-- COMMON RAW-LEVEL ROUNDTRIPS — {NodeMsg, NodeSig}
-- ============================================================================

private
  parseRawAttrRel-format-roundtrip-NodeMsg-raw :
    ∀ (pos : Position) (name : List Char) (idn : Identifier) (cid : CANId)
      (wireVal : RawAttrValueWire) (outer-suffix : List Char)
    → IdentNameStop idn
    → SuffixStops isNewlineStart outer-suffix
    → SuffixStops isHSpace
        (emit attrValueWireFmt wireVal ++ₗ ';' ∷ '\n' ∷ outer-suffix)
    → EmitsOK attrValueWireFmt wireVal (';' ∷ '\n' ∷ outer-suffix)
    → parseRawAttrRel pos
        (emit attrRelFmt (name , RrtNodeMsg idn (rawCanIdℕ cid) , wireVal , tt) ++ₗ outer-suffix)
      ≡ just (mkResult (mkRawAttrAssign name (ATgtNodeMsg idn cid) (liftRavw wireVal))
                (advancePositions pos
                  (emit attrRelFmt (name , RrtNodeMsg idn (rawCanIdℕ cid) , wireVal , tt)))
                outer-suffix)
  parseRawAttrRel-format-roundtrip-NodeMsg-raw pos name idn cid wireVal outer-suffix
                                                (c , cs , cs-eq , c-not-hsp)
                                                ss-NL val-stop l6 =
    trans step-format
      (trans step-many-newline step-buildP)
    where
      raw : ℕ
      raw = rawCanIdℕ cid

      pos-line : Position
      pos-line = advancePositions pos
                   (emit attrRelFmt (name , RrtNodeMsg idn raw , wireVal , tt))

      cont-line : AttrRelCarrier → Parser RawAttrAssign
      cont-line c = many parseNewline >>= λ _ →
                    buildAttrRelP (proj₁ c)
                                  (proj₁ (proj₂ c))
                                  (proj₁ (proj₂ (proj₂ c)))

      cont-blanks : List Char → Parser RawAttrAssign
      cont-blanks _ = buildAttrRelP name (RrtNodeMsg idn raw) wireVal

      l4 : SuffixStops isHSpace
            (emit relTargetWireFmt (RrtNodeMsg idn raw) ++ₗ
             emit attrValueWireFmt wireVal ++ₗ ';' ∷ '\n' ∷ outer-suffix)
      l4 = ∷-stop refl

      idn-stop : SuffixStops isHSpace
        ((Identifier.name idn ++ₗ
           ' ' ∷ ((emit nat raw ++ₗ ' ' ∷ []))) ++ₗ
         (emit attrValueWireFmt wireVal ++ₗ ';' ∷ '\n' ∷ outer-suffix))
      idn-stop = subst (λ chars → SuffixStops isHSpace
                            ((chars ++ₗ
                               ' ' ∷ ((emit nat raw ++ₗ ' ' ∷ []))) ++ₗ
                             (emit attrValueWireFmt wireVal ++ₗ ';' ∷ '\n' ∷ outer-suffix)))
                        (sym cs-eq) (∷-stop c-not-hsp)

      l5 : EmitsOK relTargetWireFmt (RrtNodeMsg idn raw)
            (emit attrValueWireFmt wireVal ++ₗ ';' ∷ '\n' ∷ outer-suffix)
      l5 = build-EmitsOK-relTargetWireFmt-RrtNodeMsg idn raw
            (emit attrValueWireFmt wireVal ++ₗ ';' ∷ '\n' ∷ outer-suffix)
            idn-stop val-stop

      step-format :
        parseRawAttrRel pos
          (emit attrRelFmt (name , RrtNodeMsg idn raw , wireVal , tt) ++ₗ outer-suffix)
        ≡ cont-line (name , RrtNodeMsg idn raw , wireVal , tt) pos-line outer-suffix
      step-format =
        bind-just-step (parse attrRelFmt) cont-line
          pos
          (emit attrRelFmt (name , RrtNodeMsg idn raw , wireVal , tt) ++ₗ outer-suffix)
          (name , RrtNodeMsg idn raw , wireVal , tt) pos-line outer-suffix
          (parseAttrRel-format-roundtrip pos name (RrtNodeMsg idn raw) wireVal
            outer-suffix l4 l5 l6)

      step-many-newline :
        cont-line (name , RrtNodeMsg idn raw , wireVal , tt) pos-line outer-suffix
        ≡ cont-blanks [] pos-line outer-suffix
      step-many-newline =
        bind-just-step (many parseNewline) cont-blanks
          pos-line outer-suffix
          [] pos-line outer-suffix
          (manyHelper-parseNewline-exhaust pos-line outer-suffix
            (length outer-suffix) ss-NL)

      step-buildP :
        cont-blanks [] pos-line outer-suffix
        ≡ just (mkResult (mkRawAttrAssign name (ATgtNodeMsg idn cid) (liftRavw wireVal))
                  pos-line outer-suffix)
      step-buildP with buildCANId raw | buildCANId-rawCanIdℕ cid
      ... | just .cid | refl = refl

  parseRawAttrRel-format-roundtrip-NodeSig-raw :
    ∀ (pos : Position) (name : List Char) (idn : Identifier) (cid : CANId)
      (sig : Identifier) (wireVal : RawAttrValueWire) (outer-suffix : List Char)
    → IdentNameStop idn
    → IdentNameStop sig
    → SuffixStops isNewlineStart outer-suffix
    → SuffixStops isHSpace
        (emit attrValueWireFmt wireVal ++ₗ ';' ∷ '\n' ∷ outer-suffix)
    → EmitsOK attrValueWireFmt wireVal (';' ∷ '\n' ∷ outer-suffix)
    → parseRawAttrRel pos
        (emit attrRelFmt (name , RrtNodeSig idn (rawCanIdℕ cid) sig , wireVal , tt) ++ₗ outer-suffix)
      ≡ just (mkResult (mkRawAttrAssign name (ATgtNodeSig idn cid sig) (liftRavw wireVal))
                (advancePositions pos
                  (emit attrRelFmt (name , RrtNodeSig idn (rawCanIdℕ cid) sig , wireVal , tt)))
                outer-suffix)
  parseRawAttrRel-format-roundtrip-NodeSig-raw pos name idn cid sig wireVal outer-suffix
                                                (cI , csI , csI-eq , cI-not-hsp)
                                                (cS , csS , csS-eq , cS-not-hsp)
                                                ss-NL val-stop l6 =
    trans step-format
      (trans step-many-newline step-buildP)
    where
      raw : ℕ
      raw = rawCanIdℕ cid

      pos-line : Position
      pos-line = advancePositions pos
                   (emit attrRelFmt (name , RrtNodeSig idn raw sig , wireVal , tt))

      cont-line : AttrRelCarrier → Parser RawAttrAssign
      cont-line c = many parseNewline >>= λ _ →
                    buildAttrRelP (proj₁ c)
                                  (proj₁ (proj₂ c))
                                  (proj₁ (proj₂ (proj₂ c)))

      cont-blanks : List Char → Parser RawAttrAssign
      cont-blanks _ = buildAttrRelP name (RrtNodeSig idn raw sig) wireVal

      l4 : SuffixStops isHSpace
            (emit relTargetWireFmt (RrtNodeSig idn raw sig) ++ₗ
             emit attrValueWireFmt wireVal ++ₗ ';' ∷ '\n' ∷ outer-suffix)
      l4 = ∷-stop refl

      idn-stop : SuffixStops isHSpace
        ((Identifier.name idn ++ₗ
            ' ' ∷ ((toList "SG_" ++ₗ
              ' ' ∷ ((emit nat raw ++ₗ
                ' ' ∷ ((Identifier.name sig ++ₗ ' ' ∷ []))))))) ++ₗ
         (emit attrValueWireFmt wireVal ++ₗ ';' ∷ '\n' ∷ outer-suffix))
      idn-stop = subst (λ chars → SuffixStops isHSpace
                            ((chars ++ₗ
                                ' ' ∷ ((toList "SG_" ++ₗ
                                  ' ' ∷ ((emit nat raw ++ₗ
                                    ' ' ∷ ((Identifier.name sig ++ₗ ' ' ∷ []))))))) ++ₗ
                             (emit attrValueWireFmt wireVal ++ₗ ';' ∷ '\n' ∷ outer-suffix)))
                        (sym csI-eq) (∷-stop cI-not-hsp)

      sig-stop : SuffixStops isHSpace
        ((Identifier.name sig ++ₗ ' ' ∷ []) ++ₗ
         (emit attrValueWireFmt wireVal ++ₗ ';' ∷ '\n' ∷ outer-suffix))
      sig-stop = subst (λ chars → SuffixStops isHSpace
                            ((chars ++ₗ ' ' ∷ []) ++ₗ
                             (emit attrValueWireFmt wireVal ++ₗ ';' ∷ '\n' ∷ outer-suffix)))
                        (sym csS-eq) (∷-stop cS-not-hsp)

      l5 : EmitsOK relTargetWireFmt (RrtNodeSig idn raw sig)
            (emit attrValueWireFmt wireVal ++ₗ ';' ∷ '\n' ∷ outer-suffix)
      l5 = build-EmitsOK-relTargetWireFmt-RrtNodeSig idn raw sig
            (emit attrValueWireFmt wireVal ++ₗ ';' ∷ '\n' ∷ outer-suffix)
            idn-stop sig-stop val-stop

      step-format :
        parseRawAttrRel pos
          (emit attrRelFmt (name , RrtNodeSig idn raw sig , wireVal , tt) ++ₗ outer-suffix)
        ≡ cont-line (name , RrtNodeSig idn raw sig , wireVal , tt) pos-line outer-suffix
      step-format =
        bind-just-step (parse attrRelFmt) cont-line
          pos
          (emit attrRelFmt (name , RrtNodeSig idn raw sig , wireVal , tt) ++ₗ outer-suffix)
          (name , RrtNodeSig idn raw sig , wireVal , tt) pos-line outer-suffix
          (parseAttrRel-format-roundtrip pos name (RrtNodeSig idn raw sig) wireVal
            outer-suffix l4 l5 l6)

      step-many-newline :
        cont-line (name , RrtNodeSig idn raw sig , wireVal , tt) pos-line outer-suffix
        ≡ cont-blanks [] pos-line outer-suffix
      step-many-newline =
        bind-just-step (many parseNewline) cont-blanks
          pos-line outer-suffix
          [] pos-line outer-suffix
          (manyHelper-parseNewline-exhaust pos-line outer-suffix
            (length outer-suffix) ss-NL)

      step-buildP :
        cont-blanks [] pos-line outer-suffix
        ≡ just (mkResult (mkRawAttrAssign name (ATgtNodeSig idn cid sig) (liftRavw wireVal))
                  pos-line outer-suffix)
      step-buildP with buildCANId raw | buildCANId-rawCanIdℕ cid
      ... | just .cid | refl = refl

-- ============================================================================
-- pos-eq helpers: emit-attrRelFmt-Rrt* RHS ↔ Trace*.pos9 chars
-- ============================================================================
--
-- Bridges between the inner kw-body chunk shape (from emit-eq) and the
-- canonical " <KW>_ " ++ ... unfolded form Trace*.pos9 uses.

private
  -- NodeMsg: 2 ++ₗ-assoc steps (over name idn, then over emit nat raw).
  pos-eq-chars-NodeMsg :
    ∀ (n : List Char) (idn : Identifier) (cid : CANId) (value-chars : List Char) →
    toList "BA_REL_ " ++ₗ quoteStringLit-chars n ++ₗ
      ' ' ∷ (toList "BU_BO_REL_" ++ₗ ' ' ∷ (Identifier.name idn ++ₗ
        ' ' ∷ emit nat (rawCanIdℕ cid) ++ₗ ' ' ∷ [])) ++ₗ
        (value-chars ++ₗ ';' ∷ '\n' ∷ [])
    ≡ toList "BA_REL_ " ++ₗ quoteStringLit-chars n ++ₗ
        toList " BU_BO_REL_ " ++ₗ Identifier.name idn ++ₗ
        ' ' ∷ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
        ' ' ∷ value-chars ++ₗ ';' ∷ '\n' ∷ []
  pos-eq-chars-NodeMsg n idn cid value-chars =
    cong (λ z → toList "BA_REL_ " ++ₗ quoteStringLit-chars n ++ₗ
                   ' ' ∷ 'B' ∷ 'U' ∷ '_' ∷ 'B' ∷ 'O' ∷ '_' ∷
                     'R' ∷ 'E' ∷ 'L' ∷ '_' ∷ ' ' ∷ z)
         (trans
           (++ₗ-assoc (Identifier.name idn)
                      (' ' ∷ emit nat (rawCanIdℕ cid) ++ₗ ' ' ∷ [])
                      (value-chars ++ₗ ';' ∷ '\n' ∷ []))
           (cong (λ z → Identifier.name idn ++ₗ ' ' ∷ z)
                 (++ₗ-assoc (emit nat (rawCanIdℕ cid)) (' ' ∷ [])
                            (value-chars ++ₗ ';' ∷ '\n' ∷ []))))

  -- NodeSig: 3 ++ₗ-assoc steps (over name idn, over emit nat raw, over name sig).
  pos-eq-chars-NodeSig :
    ∀ (n : List Char) (idn : Identifier) (cid : CANId) (sig : Identifier)
      (value-chars : List Char) →
    toList "BA_REL_ " ++ₗ quoteStringLit-chars n ++ₗ
      ' ' ∷ (toList "BU_SG_REL_" ++ₗ ' ' ∷ (Identifier.name idn ++ₗ
        ' ' ∷ (toList "SG_" ++ₗ ' ' ∷ (emit nat (rawCanIdℕ cid) ++ₗ
          ' ' ∷ Identifier.name sig ++ₗ ' ' ∷ [])))) ++ₗ
        (value-chars ++ₗ ';' ∷ '\n' ∷ [])
    ≡ toList "BA_REL_ " ++ₗ quoteStringLit-chars n ++ₗ
        toList " BU_SG_REL_ " ++ₗ Identifier.name idn ++ₗ
        ' ' ∷ toList "SG_ " ++ₗ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
        ' ' ∷ Identifier.name sig ++ₗ
        ' ' ∷ value-chars ++ₗ ';' ∷ '\n' ∷ []
  pos-eq-chars-NodeSig n idn cid sig value-chars =
    cong (λ z → toList "BA_REL_ " ++ₗ quoteStringLit-chars n ++ₗ
                   ' ' ∷ 'B' ∷ 'U' ∷ '_' ∷ 'S' ∷ 'G' ∷ '_' ∷
                     'R' ∷ 'E' ∷ 'L' ∷ '_' ∷ ' ' ∷ z)
         (trans
           (++ₗ-assoc (Identifier.name idn)
                      (' ' ∷ (toList "SG_" ++ₗ ' ' ∷ (emit nat (rawCanIdℕ cid) ++ₗ
                        ' ' ∷ Identifier.name sig ++ₗ ' ' ∷ [])))
                      (value-chars ++ₗ ';' ∷ '\n' ∷ []))
           (cong (λ z → Identifier.name idn ++ₗ
                          ' ' ∷ 'S' ∷ 'G' ∷ '_' ∷ ' ' ∷ z)
                 (trans
                   (++ₗ-assoc (emit nat (rawCanIdℕ cid))
                              (' ' ∷ Identifier.name sig ++ₗ ' ' ∷ [])
                              (value-chars ++ₗ ';' ∷ '\n' ∷ []))
                   (cong (λ z → emit nat (rawCanIdℕ cid) ++ₗ ' ' ∷ z)
                         (++ₗ-assoc (Identifier.name sig) (' ' ∷ [])
                                    (value-chars ++ₗ ';' ∷ '\n' ∷ []))))))

-- ============================================================================
-- Top-level dispatchers: ATgtNodeMsg × {RavString, frac, bareInt}
-- ============================================================================

parseRawAttrRel-roundtrip-ATgtNodeMsg-RavString :
  ∀ pos (name : List Char) (n : Identifier) (cid : CANId)
    (s : List Char) (outer-suffix : List Char)
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
parseRawAttrRel-roundtrip-ATgtNodeMsg-RavString pos name n cid s outer-suffix
                                                ident-stop ss-NL =
  trans
    (cong (parseRawAttrRel pos)
          (sym (bridge-NodeMsg-emit name n (rawCanIdℕ cid) (RavwString s) outer-suffix)))
    (trans
      (parseRawAttrRel-format-roundtrip-NodeMsg-raw pos name n cid
        (RavwString s) outer-suffix ident-stop ss-NL
        (value-stops-isHSpace-RavString s outer-suffix)
        (build-EmitsOK-RavwString s (';' ∷ '\n' ∷ outer-suffix) (∷-stop refl)))
      result-eq)
  where
    result-eq :
      just (mkResult (mkRawAttrAssign name (ATgtNodeMsg n cid)
                       (liftRavw (RavwString s)))
              (advancePositions pos
                (emit attrRelFmt (name , RrtNodeMsg n (rawCanIdℕ cid) , RavwString s , tt)))
              outer-suffix)
      ≡ just (mkResult
                (mkRawAttrAssign name (ATgtNodeMsg n cid) (RavString s))
                (TraceNodeMsg.pos9 pos name n cid (quoteStringLit-chars s) outer-suffix)
                outer-suffix)
    result-eq = cong (λ p → just (mkResult
                                    (mkRawAttrAssign name (ATgtNodeMsg n cid) (RavString s))
                                    p outer-suffix))
                     (cong (advancePositions pos)
                           (trans (emit-attrRelFmt-RrtNodeMsg name n (rawCanIdℕ cid) (RavwString s))
                                  (pos-eq-chars-NodeMsg name n cid (quoteStringLit-chars s))))

parseRawAttrRel-roundtrip-ATgtNodeMsg-RavDecRatFrac :
  ∀ pos (name : List Char) (n : Identifier) (cid : CANId)
    (d : DecRat) (outer-suffix : List Char)
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
parseRawAttrRel-roundtrip-ATgtNodeMsg-RavDecRatFrac pos name n cid d outer-suffix
                                                    ident-stop ss-NL =
  trans
    (cong (parseRawAttrRel pos)
          (sym (bridge-NodeMsg-emit name n (rawCanIdℕ cid) (RavwFrac d) outer-suffix)))
    (trans
      (parseRawAttrRel-format-roundtrip-NodeMsg-raw pos name n cid
        (RavwFrac d) outer-suffix ident-stop ss-NL
        (value-stops-isHSpace-RavDecRatFrac d outer-suffix)
        (build-EmitsOK-RavwFrac d (';' ∷ '\n' ∷ outer-suffix) (∷-stop refl)))
      result-eq)
  where
    result-eq :
      just (mkResult (mkRawAttrAssign name (ATgtNodeMsg n cid)
                       (liftRavw (RavwFrac d)))
              (advancePositions pos
                (emit attrRelFmt (name , RrtNodeMsg n (rawCanIdℕ cid) , RavwFrac d , tt)))
              outer-suffix)
      ≡ just (mkResult
                (mkRawAttrAssign name (ATgtNodeMsg n cid) (RavDecRat d))
                (TraceNodeMsg.pos9 pos name n cid (showDecRat-dec-chars d) outer-suffix)
                outer-suffix)
    result-eq = cong (λ p → just (mkResult
                                    (mkRawAttrAssign name (ATgtNodeMsg n cid) (RavDecRat d))
                                    p outer-suffix))
                     (cong (advancePositions pos)
                           (trans (emit-attrRelFmt-RrtNodeMsg name n (rawCanIdℕ cid) (RavwFrac d))
                                  (pos-eq-chars-NodeMsg name n cid (showDecRat-dec-chars d))))

parseRawAttrRel-roundtrip-ATgtNodeMsg-RavDecRatBareInt :
  ∀ pos (name : List Char) (n : Identifier) (cid : CANId)
    (z : ℤ) (outer-suffix : List Char)
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
parseRawAttrRel-roundtrip-ATgtNodeMsg-RavDecRatBareInt pos name n cid z outer-suffix
                                                       ident-stop ss-NL =
  trans
    (cong (parseRawAttrRel pos) reshape-input)
    (trans
      (parseRawAttrRel-format-roundtrip-NodeMsg-raw pos name n cid
        (RavwBareInt z') outer-suffix ident-stop ss-NL
        l4-rebuilt
        (build-EmitsOK-RavwBareInt z' (';' ∷ '\n' ∷ outer-suffix) (∷-stop refl) (λ ())))
      result-eq)
  where
    z' : IntDecRat
    z' = mkIntDecRatFromℤ z

    showInt-eq : showInt-chars (intDecRatToℤ z') ≡ showInt-chars z
    showInt-eq = cong showInt-chars (intDecRatToℤ-mkIntDecRatFromℤ z)

    reshape-input :
      toList "BA_REL_ " ++ₗ quoteStringLit-chars name ++ₗ
        toList " BU_BO_REL_ " ++ₗ Identifier.name n ++ₗ
        ' ' ∷ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
        ' ' ∷ showInt-chars z ++ₗ toList ";\n" ++ₗ outer-suffix
      ≡ emit attrRelFmt (name , RrtNodeMsg n (rawCanIdℕ cid) , RavwBareInt z' , tt) ++ₗ outer-suffix
    reshape-input =
      trans (cong (λ chars →
              toList "BA_REL_ " ++ₗ quoteStringLit-chars name ++ₗ
                toList " BU_BO_REL_ " ++ₗ Identifier.name n ++ₗ
                ' ' ∷ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
                ' ' ∷ chars ++ₗ toList ";\n" ++ₗ outer-suffix)
              (sym showInt-eq))
        (sym (bridge-NodeMsg-emit name n (rawCanIdℕ cid) (RavwBareInt z') outer-suffix))

    l4-rebuilt : SuffixStops isHSpace
      (emit attrValueWireFmt (RavwBareInt z') ++ₗ ';' ∷ '\n' ∷ outer-suffix)
    l4-rebuilt = subst (λ chars → SuffixStops isHSpace (chars ++ₗ ';' ∷ '\n' ∷ outer-suffix))
                       (sym showInt-eq)
                       (value-stops-isHSpace-RavDecRatBareInt z outer-suffix)

    result-eq :
      just (mkResult (mkRawAttrAssign name (ATgtNodeMsg n cid)
                       (liftRavw (RavwBareInt z')))
              (advancePositions pos
                (emit attrRelFmt (name , RrtNodeMsg n (rawCanIdℕ cid) , RavwBareInt z' , tt)))
              outer-suffix)
      ≡ just (mkResult
                (mkRawAttrAssign name (ATgtNodeMsg n cid) (RavDecRat (fromℤ z)))
                (TraceNodeMsg.pos9 pos name n cid (showInt-chars z) outer-suffix)
                outer-suffix)
    result-eq =
      cong₂ (λ rav fp → just (mkResult (mkRawAttrAssign name (ATgtNodeMsg n cid) rav)
                                       fp outer-suffix))
            value-eq pos-eq
      where
        value-eq : liftRavw (RavwBareInt z') ≡ RavDecRat (fromℤ z)
        value-eq = refl

        pos-eq : advancePositions pos
                   (emit attrRelFmt (name , RrtNodeMsg n (rawCanIdℕ cid) , RavwBareInt z' , tt))
               ≡ TraceNodeMsg.pos9 pos name n cid (showInt-chars z) outer-suffix
        pos-eq = cong (advancePositions pos)
          (trans (emit-attrRelFmt-RrtNodeMsg name n (rawCanIdℕ cid) (RavwBareInt z'))
                 (trans
                   (pos-eq-chars-NodeMsg name n cid (showInt-chars (intDecRatToℤ z')))
                   (cong (λ chars →
                           toList "BA_REL_ " ++ₗ quoteStringLit-chars name ++ₗ
                             toList " BU_BO_REL_ " ++ₗ Identifier.name n ++ₗ
                             ' ' ∷ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
                             ' ' ∷ chars ++ₗ ';' ∷ '\n' ∷ [])
                         showInt-eq)))

-- ============================================================================
-- Top-level dispatchers: ATgtNodeSig × {RavString, frac, bareInt}
-- ============================================================================

parseRawAttrRel-roundtrip-ATgtNodeSig-RavString :
  ∀ pos (name : List Char) (n : Identifier) (cid : CANId) (sig : Identifier)
    (s : List Char) (outer-suffix : List Char)
  → IdentNameStop n
  → IdentNameStop sig
  → SuffixStops isNewlineStart outer-suffix
  → parseRawAttrRel pos
      (toList "BA_REL_ " ++ₗ quoteStringLit-chars name ++ₗ
        toList " BU_SG_REL_ " ++ₗ Identifier.name n ++ₗ
        ' ' ∷ toList "SG_ " ++ₗ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
        ' ' ∷ Identifier.name sig ++ₗ
        ' ' ∷ quoteStringLit-chars s ++ₗ toList ";\n" ++ₗ outer-suffix)
    ≡ just (mkResult
              (mkRawAttrAssign name (ATgtNodeSig n cid sig) (RavString s))
              (TraceNodeSig.pos9 pos name n cid sig (quoteStringLit-chars s) outer-suffix)
              outer-suffix)
parseRawAttrRel-roundtrip-ATgtNodeSig-RavString pos name n cid sig s outer-suffix
                                                idn-stop sig-stop ss-NL =
  trans
    (cong (parseRawAttrRel pos)
          (sym (bridge-NodeSig-emit name n (rawCanIdℕ cid) sig (RavwString s) outer-suffix)))
    (trans
      (parseRawAttrRel-format-roundtrip-NodeSig-raw pos name n cid sig
        (RavwString s) outer-suffix idn-stop sig-stop ss-NL
        (value-stops-isHSpace-RavString s outer-suffix)
        (build-EmitsOK-RavwString s (';' ∷ '\n' ∷ outer-suffix) (∷-stop refl)))
      result-eq)
  where
    result-eq :
      just (mkResult (mkRawAttrAssign name (ATgtNodeSig n cid sig)
                       (liftRavw (RavwString s)))
              (advancePositions pos
                (emit attrRelFmt (name , RrtNodeSig n (rawCanIdℕ cid) sig , RavwString s , tt)))
              outer-suffix)
      ≡ just (mkResult
                (mkRawAttrAssign name (ATgtNodeSig n cid sig) (RavString s))
                (TraceNodeSig.pos9 pos name n cid sig (quoteStringLit-chars s) outer-suffix)
                outer-suffix)
    result-eq = cong (λ p → just (mkResult
                                    (mkRawAttrAssign name (ATgtNodeSig n cid sig) (RavString s))
                                    p outer-suffix))
                     (cong (advancePositions pos)
                           (trans (emit-attrRelFmt-RrtNodeSig name n (rawCanIdℕ cid) sig (RavwString s))
                                  (pos-eq-chars-NodeSig name n cid sig (quoteStringLit-chars s))))

parseRawAttrRel-roundtrip-ATgtNodeSig-RavDecRatFrac :
  ∀ pos (name : List Char) (n : Identifier) (cid : CANId) (sig : Identifier)
    (d : DecRat) (outer-suffix : List Char)
  → IdentNameStop n
  → IdentNameStop sig
  → SuffixStops isNewlineStart outer-suffix
  → parseRawAttrRel pos
      (toList "BA_REL_ " ++ₗ quoteStringLit-chars name ++ₗ
        toList " BU_SG_REL_ " ++ₗ Identifier.name n ++ₗ
        ' ' ∷ toList "SG_ " ++ₗ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
        ' ' ∷ Identifier.name sig ++ₗ
        ' ' ∷ showDecRat-dec-chars d ++ₗ toList ";\n" ++ₗ outer-suffix)
    ≡ just (mkResult
              (mkRawAttrAssign name (ATgtNodeSig n cid sig) (RavDecRat d))
              (TraceNodeSig.pos9 pos name n cid sig (showDecRat-dec-chars d) outer-suffix)
              outer-suffix)
parseRawAttrRel-roundtrip-ATgtNodeSig-RavDecRatFrac pos name n cid sig d outer-suffix
                                                    idn-stop sig-stop ss-NL =
  trans
    (cong (parseRawAttrRel pos)
          (sym (bridge-NodeSig-emit name n (rawCanIdℕ cid) sig (RavwFrac d) outer-suffix)))
    (trans
      (parseRawAttrRel-format-roundtrip-NodeSig-raw pos name n cid sig
        (RavwFrac d) outer-suffix idn-stop sig-stop ss-NL
        (value-stops-isHSpace-RavDecRatFrac d outer-suffix)
        (build-EmitsOK-RavwFrac d (';' ∷ '\n' ∷ outer-suffix) (∷-stop refl)))
      result-eq)
  where
    result-eq :
      just (mkResult (mkRawAttrAssign name (ATgtNodeSig n cid sig)
                       (liftRavw (RavwFrac d)))
              (advancePositions pos
                (emit attrRelFmt (name , RrtNodeSig n (rawCanIdℕ cid) sig , RavwFrac d , tt)))
              outer-suffix)
      ≡ just (mkResult
                (mkRawAttrAssign name (ATgtNodeSig n cid sig) (RavDecRat d))
                (TraceNodeSig.pos9 pos name n cid sig (showDecRat-dec-chars d) outer-suffix)
                outer-suffix)
    result-eq = cong (λ p → just (mkResult
                                    (mkRawAttrAssign name (ATgtNodeSig n cid sig) (RavDecRat d))
                                    p outer-suffix))
                     (cong (advancePositions pos)
                           (trans (emit-attrRelFmt-RrtNodeSig name n (rawCanIdℕ cid) sig (RavwFrac d))
                                  (pos-eq-chars-NodeSig name n cid sig (showDecRat-dec-chars d))))

parseRawAttrRel-roundtrip-ATgtNodeSig-RavDecRatBareInt :
  ∀ pos (name : List Char) (n : Identifier) (cid : CANId) (sig : Identifier)
    (z : ℤ) (outer-suffix : List Char)
  → IdentNameStop n
  → IdentNameStop sig
  → SuffixStops isNewlineStart outer-suffix
  → parseRawAttrRel pos
      (toList "BA_REL_ " ++ₗ quoteStringLit-chars name ++ₗ
        toList " BU_SG_REL_ " ++ₗ Identifier.name n ++ₗ
        ' ' ∷ toList "SG_ " ++ₗ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
        ' ' ∷ Identifier.name sig ++ₗ
        ' ' ∷ showInt-chars z ++ₗ toList ";\n" ++ₗ outer-suffix)
    ≡ just (mkResult
              (mkRawAttrAssign name (ATgtNodeSig n cid sig) (RavDecRat (fromℤ z)))
              (TraceNodeSig.pos9 pos name n cid sig (showInt-chars z) outer-suffix)
              outer-suffix)
parseRawAttrRel-roundtrip-ATgtNodeSig-RavDecRatBareInt pos name n cid sig z outer-suffix
                                                       idn-stop sig-stop ss-NL =
  trans
    (cong (parseRawAttrRel pos) reshape-input)
    (trans
      (parseRawAttrRel-format-roundtrip-NodeSig-raw pos name n cid sig
        (RavwBareInt z') outer-suffix idn-stop sig-stop ss-NL
        l4-rebuilt
        (build-EmitsOK-RavwBareInt z' (';' ∷ '\n' ∷ outer-suffix) (∷-stop refl) (λ ())))
      result-eq)
  where
    z' : IntDecRat
    z' = mkIntDecRatFromℤ z

    showInt-eq : showInt-chars (intDecRatToℤ z') ≡ showInt-chars z
    showInt-eq = cong showInt-chars (intDecRatToℤ-mkIntDecRatFromℤ z)

    reshape-input :
      toList "BA_REL_ " ++ₗ quoteStringLit-chars name ++ₗ
        toList " BU_SG_REL_ " ++ₗ Identifier.name n ++ₗ
        ' ' ∷ toList "SG_ " ++ₗ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
        ' ' ∷ Identifier.name sig ++ₗ
        ' ' ∷ showInt-chars z ++ₗ toList ";\n" ++ₗ outer-suffix
      ≡ emit attrRelFmt (name , RrtNodeSig n (rawCanIdℕ cid) sig , RavwBareInt z' , tt) ++ₗ outer-suffix
    reshape-input =
      trans (cong (λ chars →
              toList "BA_REL_ " ++ₗ quoteStringLit-chars name ++ₗ
                toList " BU_SG_REL_ " ++ₗ Identifier.name n ++ₗ
                ' ' ∷ toList "SG_ " ++ₗ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
                ' ' ∷ Identifier.name sig ++ₗ
                ' ' ∷ chars ++ₗ toList ";\n" ++ₗ outer-suffix)
              (sym showInt-eq))
        (sym (bridge-NodeSig-emit name n (rawCanIdℕ cid) sig (RavwBareInt z') outer-suffix))

    l4-rebuilt : SuffixStops isHSpace
      (emit attrValueWireFmt (RavwBareInt z') ++ₗ ';' ∷ '\n' ∷ outer-suffix)
    l4-rebuilt = subst (λ chars → SuffixStops isHSpace (chars ++ₗ ';' ∷ '\n' ∷ outer-suffix))
                       (sym showInt-eq)
                       (value-stops-isHSpace-RavDecRatBareInt z outer-suffix)

    result-eq :
      just (mkResult (mkRawAttrAssign name (ATgtNodeSig n cid sig)
                       (liftRavw (RavwBareInt z')))
              (advancePositions pos
                (emit attrRelFmt (name , RrtNodeSig n (rawCanIdℕ cid) sig , RavwBareInt z' , tt)))
              outer-suffix)
      ≡ just (mkResult
                (mkRawAttrAssign name (ATgtNodeSig n cid sig) (RavDecRat (fromℤ z)))
                (TraceNodeSig.pos9 pos name n cid sig (showInt-chars z) outer-suffix)
                outer-suffix)
    result-eq =
      cong₂ (λ rav fp → just (mkResult (mkRawAttrAssign name (ATgtNodeSig n cid sig) rav)
                                       fp outer-suffix))
            value-eq pos-eq
      where
        value-eq : liftRavw (RavwBareInt z') ≡ RavDecRat (fromℤ z)
        value-eq = refl

        pos-eq : advancePositions pos
                   (emit attrRelFmt (name , RrtNodeSig n (rawCanIdℕ cid) sig , RavwBareInt z' , tt))
               ≡ TraceNodeSig.pos9 pos name n cid sig (showInt-chars z) outer-suffix
        pos-eq = cong (advancePositions pos)
          (trans (emit-attrRelFmt-RrtNodeSig name n (rawCanIdℕ cid) sig (RavwBareInt z'))
                 (trans
                   (pos-eq-chars-NodeSig name n cid sig (showInt-chars (intDecRatToℤ z')))
                   (cong (λ chars →
                           toList "BA_REL_ " ++ₗ quoteStringLit-chars name ++ₗ
                             toList " BU_SG_REL_ " ++ₗ Identifier.name n ++ₗ
                             ' ' ∷ toList "SG_ " ++ₗ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
                             ' ' ∷ Identifier.name sig ++ₗ
                             ' ' ∷ chars ++ₗ ';' ∷ '\n' ∷ [])
                         showInt-eq)))
