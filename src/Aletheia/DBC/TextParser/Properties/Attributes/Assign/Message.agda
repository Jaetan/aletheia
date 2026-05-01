{-# OPTIONS --safe --without-K #-}

-- B.3.d Layer 3 3d.5.d 3c-B — `parseRawAttrAssign` × ATgtMessage per-line
-- construct roundtrips (3 emit shapes), η-style migration onto the
-- universal `parseAttrAssign-format-roundtrip` lemma.
--
-- ATgtMessage is the `RatwMsg raw : ℕ` constructor of `RawAttrTargetWire`,
-- routed through the `msgArm` (`"BO_" ++ ws + nat + ws`) of `stdTarget-
-- WireFmt`'s 5-way altSum.  Top-level disjointness against `nodeArm`
-- (closed via build-EmitsOK-stdTargetWireFmt-RatwMsg).  The build-P step
-- discharges the `with buildCANId raw | buildCANId-rawCanIdℕ cid` aux on
-- `raw = rawCanIdℕ cid` via `... | just .cid | refl = refl`.
--
-- TraceMessage module preserved for `Properties/Attributes/Line.agda`'s
-- per-target-shape line dispatchers.

module Aletheia.DBC.TextParser.Properties.Attributes.Assign.Message where

open import Data.Bool using (Bool; true; false; T)
open import Data.Char using (Char)
open import Data.Char.Base using (_≈ᵇ_; isDigit)
open import Data.Integer using (ℤ; +_; -[1+_])
open import Data.List using (List; []; _∷_; length) renaming (_++_ to _++ₗ_)
open import Data.List.Properties using () renaming (++-assoc to ++ₗ-assoc; length-++ to length-++ₗ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (∃₂; _,_; Σ; _×_; proj₁; proj₂)
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
  using (parseRawAttrAssign;
         RawAttrAssign; mkRawAttrAssign;
         RawAttrValue; RavString; RavDecRat;
         liftRavw; buildAttrAssignP)
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

open import Aletheia.DBC.TextParser.Format using
  (Format; emit; parse; EmitsOK; nat)
open import Aletheia.DBC.TextParser.Format.AttrValue using
  (RawAttrValueWire; RavwString; RavwFrac; RavwBareInt;
   attrValueWireFmt;
   build-EmitsOK-RavwString;
   build-EmitsOK-RavwFrac;
   build-EmitsOK-RavwBareInt)
open import Aletheia.DBC.TextParser.Format.AttrLine using
  (attrAssignFmt; AttrAssignCarrier;
   stdTargetWireFmt; RatwMsg;
   parseAttrAssign-format-roundtrip;
   emit-attrAssignFmt-RatwMsg;
   emit-attrAssignFmt-RatwMsg-with-outer;
   build-EmitsOK-stdTargetWireFmt-RatwMsg)

-- ============================================================================
-- TRACE MODULE — kept for `Properties/Attributes/Line.agda` compatibility
-- ============================================================================

module TraceMessage (pos : Position) (name : List Char) (cid : CANId)
                    (value-chars : List Char) (outer-suffix : List Char) where
  cs-name : List Char
  cs-name = quoteStringLit-chars name

  cs-id : List Char
  cs-id = showℕ-dec-chars (rawCanIdℕ cid)

  -- Single advancePositions call over the full inline-line shape.
  pos9 : Position
  pos9 = advancePositions pos
           (toList "BA_ " ++ₗ cs-name ++ₗ
            toList " BO_ " ++ₗ cs-id ++ₗ
            ' ' ∷ value-chars ++ₗ ';' ∷ '\n' ∷ [])

-- ============================================================================
-- BRIDGES — emit form ↔ inline-input shape
-- ============================================================================

private
  -- Per-shape bridge: emit attrAssignFmt (n, RatwMsg raw, wireVal, tt) ++
  -- outer-suffix ≡ canonical spec shape.  Direct alias of
  -- `emit-attrAssignFmt-RatwMsg-with-outer` (Format/AttrLine.agda).
  bridge-Message-emit :
    ∀ (name : List Char) (raw : ℕ)
      (wireVal : RawAttrValueWire) (outer-suffix : List Char)
    → emit attrAssignFmt (name , RatwMsg raw , wireVal , tt) ++ₗ outer-suffix
      ≡ toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
          toList " BO_ " ++ₗ emit nat raw ++ₗ
          ' ' ∷ emit attrValueWireFmt wireVal ++ₗ ';' ∷ '\n' ∷ outer-suffix
  bridge-Message-emit = emit-attrAssignFmt-RatwMsg-with-outer

-- ============================================================================
-- COMMON RAW-LEVEL ROUNDTRIP — Message arm
-- ============================================================================

private
  parseRawAttrAssign-format-roundtrip-Message-raw :
    ∀ (pos : Position) (name : List Char) (cid : CANId)
      (wireVal : RawAttrValueWire) (outer-suffix : List Char)
    → SuffixStops isNewlineStart outer-suffix
    → SuffixStops isHSpace
        (emit attrValueWireFmt wireVal ++ₗ ';' ∷ '\n' ∷ outer-suffix)
    → EmitsOK attrValueWireFmt wireVal (';' ∷ '\n' ∷ outer-suffix)
    → parseRawAttrAssign pos
        (emit attrAssignFmt (name , RatwMsg (rawCanIdℕ cid) , wireVal , tt) ++ₗ outer-suffix)
      ≡ just (mkResult (mkRawAttrAssign name (ATgtMessage cid) (liftRavw wireVal))
                (advancePositions pos
                  (emit attrAssignFmt (name , RatwMsg (rawCanIdℕ cid) , wireVal , tt)))
                outer-suffix)
  parseRawAttrAssign-format-roundtrip-Message-raw pos name cid wireVal outer-suffix
                                                  ss-NL val-stop l6 =
    trans step-format
      (trans step-many-newline step-buildP)
    where
      raw : ℕ
      raw = rawCanIdℕ cid

      pos-line : Position
      pos-line = advancePositions pos
                   (emit attrAssignFmt (name , RatwMsg raw , wireVal , tt))

      cont-line : AttrAssignCarrier → Parser RawAttrAssign
      cont-line c = many parseNewline >>= λ _ →
                    buildAttrAssignP (proj₁ c)
                                     (proj₁ (proj₂ c))
                                     (proj₁ (proj₂ (proj₂ c)))

      cont-blanks : List Char → Parser RawAttrAssign
      cont-blanks _ = buildAttrAssignP name (RatwMsg raw) wireVal

      l4 : SuffixStops isHSpace
            (emit stdTargetWireFmt (RatwMsg raw) ++ₗ
             emit attrValueWireFmt wireVal ++ₗ ';' ∷ '\n' ∷ outer-suffix)
      l4 = ∷-stop refl

      l5 : EmitsOK stdTargetWireFmt (RatwMsg raw)
            (emit attrValueWireFmt wireVal ++ₗ ';' ∷ '\n' ∷ outer-suffix)
      l5 = build-EmitsOK-stdTargetWireFmt-RatwMsg raw
            (emit attrValueWireFmt wireVal ++ₗ ';' ∷ '\n' ∷ outer-suffix) val-stop

      step-format :
        parseRawAttrAssign pos
          (emit attrAssignFmt (name , RatwMsg raw , wireVal , tt) ++ₗ outer-suffix)
        ≡ cont-line (name , RatwMsg raw , wireVal , tt) pos-line outer-suffix
      step-format =
        bind-just-step (parse attrAssignFmt) cont-line
          pos
          (emit attrAssignFmt (name , RatwMsg raw , wireVal , tt) ++ₗ outer-suffix)
          (name , RatwMsg raw , wireVal , tt) pos-line outer-suffix
          (parseAttrAssign-format-roundtrip pos name (RatwMsg raw) wireVal
            outer-suffix l4 l5 l6)

      step-many-newline :
        cont-line (name , RatwMsg raw , wireVal , tt) pos-line outer-suffix
        ≡ cont-blanks [] pos-line outer-suffix
      step-many-newline =
        bind-just-step (many parseNewline) cont-blanks
          pos-line outer-suffix
          [] pos-line outer-suffix
          (manyHelper-parseNewline-exhaust pos-line outer-suffix
            (length outer-suffix) ss-NL)

      step-buildP :
        cont-blanks [] pos-line outer-suffix
        ≡ just (mkResult (mkRawAttrAssign name (ATgtMessage cid) (liftRavw wireVal))
                  pos-line outer-suffix)
      step-buildP with buildCANId raw | buildCANId-rawCanIdℕ cid
      ... | just .cid | refl = refl

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
  trans
    (cong (parseRawAttrAssign pos)
          (sym (bridge-Message-emit name (rawCanIdℕ cid) (RavwString s) outer-suffix)))
    (trans
      (parseRawAttrAssign-format-roundtrip-Message-raw pos name cid
        (RavwString s) outer-suffix ss-NL
        (value-stops-isHSpace-RavString s outer-suffix)
        (build-EmitsOK-RavwString s (';' ∷ '\n' ∷ outer-suffix) (∷-stop refl)))
      result-eq)
  where
    result-eq :
      just (mkResult (mkRawAttrAssign name (ATgtMessage cid)
                       (liftRavw (RavwString s)))
              (advancePositions pos
                (emit attrAssignFmt (name , RatwMsg (rawCanIdℕ cid) , RavwString s , tt)))
              outer-suffix)
      ≡ just (mkResult
                (mkRawAttrAssign name (ATgtMessage cid) (RavString s))
                (TraceMessage.pos9 pos name cid (quoteStringLit-chars s) outer-suffix)
                outer-suffix)
    result-eq = cong (λ p → just (mkResult
                                    (mkRawAttrAssign name (ATgtMessage cid) (RavString s))
                                    p outer-suffix))
                     (cong (advancePositions pos)
                           (trans (emit-attrAssignFmt-RatwMsg name (rawCanIdℕ cid) (RavwString s))
                                  (cong (λ z → toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
                                                  ' ' ∷ 'B' ∷ 'O' ∷ '_' ∷ ' ' ∷ z)
                                        (++ₗ-assoc (emit nat (rawCanIdℕ cid)) (' ' ∷ [])
                                                   (quoteStringLit-chars s ++ₗ
                                                      ';' ∷ '\n' ∷ [])))))

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
parseRawAttrAssign-roundtrip-ATgtMessage-RavDecRatFrac pos name cid d outer-suffix ss-NL =
  trans
    (cong (parseRawAttrAssign pos)
          (sym (bridge-Message-emit name (rawCanIdℕ cid) (RavwFrac d) outer-suffix)))
    (trans
      (parseRawAttrAssign-format-roundtrip-Message-raw pos name cid
        (RavwFrac d) outer-suffix ss-NL
        (value-stops-isHSpace-RavDecRatFrac d outer-suffix)
        (build-EmitsOK-RavwFrac d (';' ∷ '\n' ∷ outer-suffix) (∷-stop refl)))
      result-eq)
  where
    result-eq :
      just (mkResult (mkRawAttrAssign name (ATgtMessage cid)
                       (liftRavw (RavwFrac d)))
              (advancePositions pos
                (emit attrAssignFmt (name , RatwMsg (rawCanIdℕ cid) , RavwFrac d , tt)))
              outer-suffix)
      ≡ just (mkResult
                (mkRawAttrAssign name (ATgtMessage cid) (RavDecRat d))
                (TraceMessage.pos9 pos name cid (showDecRat-dec-chars d) outer-suffix)
                outer-suffix)
    result-eq = cong (λ p → just (mkResult
                                    (mkRawAttrAssign name (ATgtMessage cid) (RavDecRat d))
                                    p outer-suffix))
                     (cong (advancePositions pos)
                           (trans (emit-attrAssignFmt-RatwMsg name (rawCanIdℕ cid) (RavwFrac d))
                                  (cong (λ z → toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
                                                  ' ' ∷ 'B' ∷ 'O' ∷ '_' ∷ ' ' ∷ z)
                                        (++ₗ-assoc (emit nat (rawCanIdℕ cid)) (' ' ∷ [])
                                                   (showDecRat-dec-chars d ++ₗ
                                                      ';' ∷ '\n' ∷ [])))))

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
parseRawAttrAssign-roundtrip-ATgtMessage-RavDecRatBareInt pos name cid z outer-suffix ss-NL =
  trans
    (cong (parseRawAttrAssign pos) reshape-input)
    (trans
      (parseRawAttrAssign-format-roundtrip-Message-raw pos name cid
        (RavwBareInt z') outer-suffix ss-NL
        l4-rebuilt
        (build-EmitsOK-RavwBareInt z' (';' ∷ '\n' ∷ outer-suffix) (∷-stop refl) (λ ())))
      result-eq)
  where
    z' : IntDecRat
    z' = mkIntDecRatFromℤ z

    showInt-eq : showInt-chars (intDecRatToℤ z') ≡ showInt-chars z
    showInt-eq = cong showInt-chars (intDecRatToℤ-mkIntDecRatFromℤ z)

    reshape-input :
      toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
        toList " BO_ " ++ₗ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
        ' ' ∷ showInt-chars z ++ₗ toList ";\n" ++ₗ outer-suffix
      ≡ emit attrAssignFmt (name , RatwMsg (rawCanIdℕ cid) , RavwBareInt z' , tt) ++ₗ outer-suffix
    reshape-input =
      trans (cong (λ chars →
              toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
                toList " BO_ " ++ₗ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
                ' ' ∷ chars ++ₗ toList ";\n" ++ₗ outer-suffix)
              (sym showInt-eq))
        (sym (bridge-Message-emit name (rawCanIdℕ cid) (RavwBareInt z') outer-suffix))

    l4-rebuilt : SuffixStops isHSpace
      (emit attrValueWireFmt (RavwBareInt z') ++ₗ ';' ∷ '\n' ∷ outer-suffix)
    l4-rebuilt = subst (λ chars → SuffixStops isHSpace (chars ++ₗ ';' ∷ '\n' ∷ outer-suffix))
                       (sym showInt-eq)
                       (value-stops-isHSpace-RavDecRatBareInt z outer-suffix)

    result-eq :
      just (mkResult (mkRawAttrAssign name (ATgtMessage cid)
                       (liftRavw (RavwBareInt z')))
              (advancePositions pos
                (emit attrAssignFmt (name , RatwMsg (rawCanIdℕ cid) , RavwBareInt z' , tt)))
              outer-suffix)
      ≡ just (mkResult
                (mkRawAttrAssign name (ATgtMessage cid) (RavDecRat (fromℤ z)))
                (TraceMessage.pos9 pos name cid (showInt-chars z) outer-suffix)
                outer-suffix)
    result-eq =
      cong₂ (λ rav fp → just (mkResult (mkRawAttrAssign name (ATgtMessage cid) rav)
                                       fp outer-suffix))
            value-eq pos-eq
      where
        value-eq : liftRavw (RavwBareInt z') ≡ RavDecRat (fromℤ z)
        value-eq = refl

        pos-eq : advancePositions pos
                   (emit attrAssignFmt (name , RatwMsg (rawCanIdℕ cid) , RavwBareInt z' , tt))
               ≡ TraceMessage.pos9 pos name cid (showInt-chars z) outer-suffix
        pos-eq = cong (advancePositions pos)
          (trans (emit-attrAssignFmt-RatwMsg name (rawCanIdℕ cid) (RavwBareInt z'))
                 (trans
                   (cong (λ z → toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
                                   ' ' ∷ 'B' ∷ 'O' ∷ '_' ∷ ' ' ∷ z)
                         (++ₗ-assoc (emit nat (rawCanIdℕ cid)) (' ' ∷ [])
                                    (showInt-chars (intDecRatToℤ z') ++ₗ
                                       ';' ∷ '\n' ∷ [])))
                   (cong (λ chars →
                           toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
                             toList " BO_ " ++ₗ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
                             ' ' ∷ chars ++ₗ ';' ∷ '\n' ∷ [])
                         showInt-eq)))
