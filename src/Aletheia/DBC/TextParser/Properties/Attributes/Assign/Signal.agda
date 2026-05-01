{-# OPTIONS --safe --without-K #-}

-- B.3.d Layer 3 3d.5.d 3c-B — `parseRawAttrAssign` × ATgtSignal per-line
-- construct roundtrips (3 emit shapes), η-style migration onto the
-- universal `parseAttrAssign-format-roundtrip` lemma.
--
-- ATgtSignal is the `RatwSig raw sig` constructor of `RawAttrTargetWire`,
-- routed through the `sigArm` (`"SG_" ++ ws + nat + ws + ident + ws`) of
-- `stdTargetWireFmt`'s 5-way altSum.  Top-level disjointness against
-- `altSum nodeArm msgArm` (closed via build-EmitsOK-stdTargetWireFmt-
-- RatwSig).  The build-P step discharges `with buildCANId raw |
-- buildCANId-rawCanIdℕ cid` on `raw = rawCanIdℕ cid` via
-- `... | just .cid | refl = refl`.
--
-- Carries an `IdentNameStop` precondition for `sig` (Layer 4 owes it from
-- `validIdentifierᵇ`), used by `build-EmitsOK-stdTargetWireFmt-RatwSig`'s
-- sig-stop input.

module Aletheia.DBC.TextParser.Properties.Attributes.Assign.Signal where

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
   stdTargetWireFmt; RatwSig;
   parseAttrAssign-format-roundtrip;
   emit-attrAssignFmt-RatwSig;
   emit-attrAssignFmt-RatwSig-with-outer;
   build-EmitsOK-stdTargetWireFmt-RatwSig)

-- ============================================================================
-- IDENT-NAME-STOP precondition (owed at Layer 4 universally from validIdentifierᵇ)
-- ============================================================================

IdentNameStop : Identifier → Set
IdentNameStop n =
  Σ[ c ∈ Char ] Σ[ cs ∈ List Char ]
    (Identifier.name n ≡ c ∷ cs) × (isHSpace c ≡ false)

-- ============================================================================
-- TRACE MODULE — kept for `Properties/Attributes/Line.agda` compatibility
-- ============================================================================

module TraceSignal (pos : Position) (name : List Char) (cid : CANId) (sig : Identifier)
                   (value-chars : List Char) (outer-suffix : List Char) where
  cs-name : List Char
  cs-name = quoteStringLit-chars name

  cs-id : List Char
  cs-id = showℕ-dec-chars (rawCanIdℕ cid)

  cs-sig : List Char
  cs-sig = Identifier.name sig

  -- Single advancePositions call over the full inline-line shape.
  pos9 : Position
  pos9 = advancePositions pos
           (toList "BA_ " ++ₗ cs-name ++ₗ
            toList " SG_ " ++ₗ cs-id ++ₗ
            ' ' ∷ cs-sig ++ₗ
            ' ' ∷ value-chars ++ₗ ';' ∷ '\n' ∷ [])

-- ============================================================================
-- BRIDGES — emit form ↔ inline-input shape
-- ============================================================================

private
  -- Per-shape bridge: emit attrAssignFmt (n, RatwSig raw sig, wireVal, tt) ++
  -- outer-suffix ≡ canonical spec shape.  Direct alias of
  -- `emit-attrAssignFmt-RatwSig-with-outer` (Format/AttrLine.agda).
  bridge-Signal-emit :
    ∀ (name : List Char) (raw : ℕ) (sig : Identifier)
      (wireVal : RawAttrValueWire) (outer-suffix : List Char)
    → emit attrAssignFmt (name , RatwSig raw sig , wireVal , tt) ++ₗ outer-suffix
      ≡ toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
          toList " SG_ " ++ₗ emit nat raw ++ₗ
          ' ' ∷ Identifier.name sig ++ₗ
          ' ' ∷ emit attrValueWireFmt wireVal ++ₗ ';' ∷ '\n' ∷ outer-suffix
  bridge-Signal-emit = emit-attrAssignFmt-RatwSig-with-outer

-- ============================================================================
-- COMMON RAW-LEVEL ROUNDTRIP — Signal arm
-- ============================================================================

private
  parseRawAttrAssign-format-roundtrip-Signal-raw :
    ∀ (pos : Position) (name : List Char) (cid : CANId) (sig : Identifier)
      (wireVal : RawAttrValueWire) (outer-suffix : List Char)
    → IdentNameStop sig
    → SuffixStops isNewlineStart outer-suffix
    → SuffixStops isHSpace
        (emit attrValueWireFmt wireVal ++ₗ ';' ∷ '\n' ∷ outer-suffix)
    → EmitsOK attrValueWireFmt wireVal (';' ∷ '\n' ∷ outer-suffix)
    → parseRawAttrAssign pos
        (emit attrAssignFmt (name , RatwSig (rawCanIdℕ cid) sig , wireVal , tt) ++ₗ outer-suffix)
      ≡ just (mkResult (mkRawAttrAssign name (ATgtSignal cid sig) (liftRavw wireVal))
                (advancePositions pos
                  (emit attrAssignFmt (name , RatwSig (rawCanIdℕ cid) sig , wireVal , tt)))
                outer-suffix)
  parseRawAttrAssign-format-roundtrip-Signal-raw pos name cid sig wireVal outer-suffix
                                                 (c , cs , cs-eq , c-not-hsp)
                                                 ss-NL val-stop l6 =
    trans step-format
      (trans step-many-newline step-buildP)
    where
      raw : ℕ
      raw = rawCanIdℕ cid

      pos-line : Position
      pos-line = advancePositions pos
                   (emit attrAssignFmt (name , RatwSig raw sig , wireVal , tt))

      cont-line : AttrAssignCarrier → Parser RawAttrAssign
      cont-line c = many parseNewline >>= λ _ →
                    buildAttrAssignP (proj₁ c)
                                     (proj₁ (proj₂ c))
                                     (proj₁ (proj₂ (proj₂ c)))

      cont-blanks : List Char → Parser RawAttrAssign
      cont-blanks _ = buildAttrAssignP name (RatwSig raw sig) wireVal

      l4 : SuffixStops isHSpace
            (emit stdTargetWireFmt (RatwSig raw sig) ++ₗ
             emit attrValueWireFmt wireVal ++ₗ ';' ∷ '\n' ∷ outer-suffix)
      l4 = ∷-stop refl

      sig-stop : SuffixStops isHSpace
        ((Identifier.name sig ++ₗ ' ' ∷ []) ++ₗ
         (emit attrValueWireFmt wireVal ++ₗ ';' ∷ '\n' ∷ outer-suffix))
      sig-stop = subst (λ chars → SuffixStops isHSpace
                            ((chars ++ₗ ' ' ∷ []) ++ₗ
                             (emit attrValueWireFmt wireVal ++ₗ ';' ∷ '\n' ∷ outer-suffix)))
                        (sym cs-eq) (∷-stop c-not-hsp)

      l5 : EmitsOK stdTargetWireFmt (RatwSig raw sig)
            (emit attrValueWireFmt wireVal ++ₗ ';' ∷ '\n' ∷ outer-suffix)
      l5 = build-EmitsOK-stdTargetWireFmt-RatwSig raw sig
            (emit attrValueWireFmt wireVal ++ₗ ';' ∷ '\n' ∷ outer-suffix)
            sig-stop val-stop

      step-format :
        parseRawAttrAssign pos
          (emit attrAssignFmt (name , RatwSig raw sig , wireVal , tt) ++ₗ outer-suffix)
        ≡ cont-line (name , RatwSig raw sig , wireVal , tt) pos-line outer-suffix
      step-format =
        bind-just-step (parse attrAssignFmt) cont-line
          pos
          (emit attrAssignFmt (name , RatwSig raw sig , wireVal , tt) ++ₗ outer-suffix)
          (name , RatwSig raw sig , wireVal , tt) pos-line outer-suffix
          (parseAttrAssign-format-roundtrip pos name (RatwSig raw sig) wireVal
            outer-suffix l4 l5 l6)

      step-many-newline :
        cont-line (name , RatwSig raw sig , wireVal , tt) pos-line outer-suffix
        ≡ cont-blanks [] pos-line outer-suffix
      step-many-newline =
        bind-just-step (many parseNewline) cont-blanks
          pos-line outer-suffix
          [] pos-line outer-suffix
          (manyHelper-parseNewline-exhaust pos-line outer-suffix
            (length outer-suffix) ss-NL)

      step-buildP :
        cont-blanks [] pos-line outer-suffix
        ≡ just (mkResult (mkRawAttrAssign name (ATgtSignal cid sig) (liftRavw wireVal))
                  pos-line outer-suffix)
      step-buildP with buildCANId raw | buildCANId-rawCanIdℕ cid
      ... | just .cid | refl = refl

-- ============================================================================
-- pos-eq helper: emit-attrAssignFmt-RatwSig RHS ↔ TraceSignal.pos9 chars
-- ============================================================================
--
-- emit-attrAssignFmt-RatwSig produces the inner SG_ chunk shape; TraceSignal.
-- pos9 has the unfolded " SG_ " ++ raw ++ ' ∷ name sig ++ ' ∷ value-chars
-- form.  Two ++ₗ-assoc steps bridge: one over (emit nat raw ++ ' ∷ name sig
-- ++ ' ∷ []), one over (name sig ++ ' ∷ []).

private
  pos-eq-chars :
    ∀ (n : List Char) (cid : CANId) (sig : Identifier) (value-chars : List Char) →
    toList "BA_ " ++ₗ quoteStringLit-chars n ++ₗ
      ' ' ∷ (toList "SG_" ++ₗ ' ' ∷ (emit nat (rawCanIdℕ cid) ++ₗ
        ' ' ∷ Identifier.name sig ++ₗ ' ' ∷ [])) ++ₗ
        (value-chars ++ₗ ';' ∷ '\n' ∷ [])
    ≡ toList "BA_ " ++ₗ quoteStringLit-chars n ++ₗ
        toList " SG_ " ++ₗ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
        ' ' ∷ Identifier.name sig ++ₗ
        ' ' ∷ value-chars ++ₗ ';' ∷ '\n' ∷ []
  pos-eq-chars n cid sig value-chars =
    cong (λ z → toList "BA_ " ++ₗ quoteStringLit-chars n ++ₗ
                   ' ' ∷ 'S' ∷ 'G' ∷ '_' ∷ ' ' ∷ z)
         (trans
           (++ₗ-assoc (emit nat (rawCanIdℕ cid))
                      (' ' ∷ Identifier.name sig ++ₗ ' ' ∷ [])
                      (value-chars ++ₗ ';' ∷ '\n' ∷ []))
           (cong (λ z → emit nat (rawCanIdℕ cid) ++ₗ ' ' ∷ z)
                 (++ₗ-assoc (Identifier.name sig) (' ' ∷ [])
                            (value-chars ++ₗ ';' ∷ '\n' ∷ []))))

-- ============================================================================
-- Top-level dispatchers: ATgtSignal × {RavString, frac, bareInt}
-- ============================================================================

parseRawAttrAssign-roundtrip-ATgtSignal-RavString :
  ∀ pos (name : List Char) (cid : CANId) (sig : Identifier)
    (s : List Char) (outer-suffix : List Char)
  → IdentNameStop sig
  → SuffixStops isNewlineStart outer-suffix
  → parseRawAttrAssign pos
      (toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
        toList " SG_ " ++ₗ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
        ' ' ∷ Identifier.name sig ++ₗ
        ' ' ∷ quoteStringLit-chars s ++ₗ toList ";\n" ++ₗ outer-suffix)
    ≡ just (mkResult
              (mkRawAttrAssign name (ATgtSignal cid sig) (RavString s))
              (TraceSignal.pos9 pos name cid sig (quoteStringLit-chars s) outer-suffix)
              outer-suffix)
parseRawAttrAssign-roundtrip-ATgtSignal-RavString pos name cid sig s outer-suffix
                                                  ident-stop ss-NL =
  trans
    (cong (parseRawAttrAssign pos)
          (sym (bridge-Signal-emit name (rawCanIdℕ cid) sig (RavwString s) outer-suffix)))
    (trans
      (parseRawAttrAssign-format-roundtrip-Signal-raw pos name cid sig
        (RavwString s) outer-suffix ident-stop ss-NL
        (value-stops-isHSpace-RavString s outer-suffix)
        (build-EmitsOK-RavwString s (';' ∷ '\n' ∷ outer-suffix) (∷-stop refl)))
      result-eq)
  where
    result-eq :
      just (mkResult (mkRawAttrAssign name (ATgtSignal cid sig)
                       (liftRavw (RavwString s)))
              (advancePositions pos
                (emit attrAssignFmt (name , RatwSig (rawCanIdℕ cid) sig , RavwString s , tt)))
              outer-suffix)
      ≡ just (mkResult
                (mkRawAttrAssign name (ATgtSignal cid sig) (RavString s))
                (TraceSignal.pos9 pos name cid sig (quoteStringLit-chars s) outer-suffix)
                outer-suffix)
    result-eq = cong (λ p → just (mkResult
                                    (mkRawAttrAssign name (ATgtSignal cid sig) (RavString s))
                                    p outer-suffix))
                     (cong (advancePositions pos)
                           (trans (emit-attrAssignFmt-RatwSig name (rawCanIdℕ cid) sig (RavwString s))
                                  (pos-eq-chars name cid sig (quoteStringLit-chars s))))

parseRawAttrAssign-roundtrip-ATgtSignal-RavDecRatFrac :
  ∀ pos (name : List Char) (cid : CANId) (sig : Identifier)
    (d : DecRat) (outer-suffix : List Char)
  → IdentNameStop sig
  → SuffixStops isNewlineStart outer-suffix
  → parseRawAttrAssign pos
      (toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
        toList " SG_ " ++ₗ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
        ' ' ∷ Identifier.name sig ++ₗ
        ' ' ∷ showDecRat-dec-chars d ++ₗ toList ";\n" ++ₗ outer-suffix)
    ≡ just (mkResult
              (mkRawAttrAssign name (ATgtSignal cid sig) (RavDecRat d))
              (TraceSignal.pos9 pos name cid sig (showDecRat-dec-chars d) outer-suffix)
              outer-suffix)
parseRawAttrAssign-roundtrip-ATgtSignal-RavDecRatFrac pos name cid sig d outer-suffix
                                                      ident-stop ss-NL =
  trans
    (cong (parseRawAttrAssign pos)
          (sym (bridge-Signal-emit name (rawCanIdℕ cid) sig (RavwFrac d) outer-suffix)))
    (trans
      (parseRawAttrAssign-format-roundtrip-Signal-raw pos name cid sig
        (RavwFrac d) outer-suffix ident-stop ss-NL
        (value-stops-isHSpace-RavDecRatFrac d outer-suffix)
        (build-EmitsOK-RavwFrac d (';' ∷ '\n' ∷ outer-suffix) (∷-stop refl)))
      result-eq)
  where
    result-eq :
      just (mkResult (mkRawAttrAssign name (ATgtSignal cid sig)
                       (liftRavw (RavwFrac d)))
              (advancePositions pos
                (emit attrAssignFmt (name , RatwSig (rawCanIdℕ cid) sig , RavwFrac d , tt)))
              outer-suffix)
      ≡ just (mkResult
                (mkRawAttrAssign name (ATgtSignal cid sig) (RavDecRat d))
                (TraceSignal.pos9 pos name cid sig (showDecRat-dec-chars d) outer-suffix)
                outer-suffix)
    result-eq = cong (λ p → just (mkResult
                                    (mkRawAttrAssign name (ATgtSignal cid sig) (RavDecRat d))
                                    p outer-suffix))
                     (cong (advancePositions pos)
                           (trans (emit-attrAssignFmt-RatwSig name (rawCanIdℕ cid) sig (RavwFrac d))
                                  (pos-eq-chars name cid sig (showDecRat-dec-chars d))))

parseRawAttrAssign-roundtrip-ATgtSignal-RavDecRatBareInt :
  ∀ pos (name : List Char) (cid : CANId) (sig : Identifier)
    (z : ℤ) (outer-suffix : List Char)
  → IdentNameStop sig
  → SuffixStops isNewlineStart outer-suffix
  → parseRawAttrAssign pos
      (toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
        toList " SG_ " ++ₗ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
        ' ' ∷ Identifier.name sig ++ₗ
        ' ' ∷ showInt-chars z ++ₗ toList ";\n" ++ₗ outer-suffix)
    ≡ just (mkResult
              (mkRawAttrAssign name (ATgtSignal cid sig) (RavDecRat (fromℤ z)))
              (TraceSignal.pos9 pos name cid sig (showInt-chars z) outer-suffix)
              outer-suffix)
parseRawAttrAssign-roundtrip-ATgtSignal-RavDecRatBareInt pos name cid sig z outer-suffix
                                                         ident-stop ss-NL =
  trans
    (cong (parseRawAttrAssign pos) reshape-input)
    (trans
      (parseRawAttrAssign-format-roundtrip-Signal-raw pos name cid sig
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
      toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
        toList " SG_ " ++ₗ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
        ' ' ∷ Identifier.name sig ++ₗ
        ' ' ∷ showInt-chars z ++ₗ toList ";\n" ++ₗ outer-suffix
      ≡ emit attrAssignFmt (name , RatwSig (rawCanIdℕ cid) sig , RavwBareInt z' , tt) ++ₗ outer-suffix
    reshape-input =
      trans (cong (λ chars →
              toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
                toList " SG_ " ++ₗ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
                ' ' ∷ Identifier.name sig ++ₗ
                ' ' ∷ chars ++ₗ toList ";\n" ++ₗ outer-suffix)
              (sym showInt-eq))
        (sym (bridge-Signal-emit name (rawCanIdℕ cid) sig (RavwBareInt z') outer-suffix))

    l4-rebuilt : SuffixStops isHSpace
      (emit attrValueWireFmt (RavwBareInt z') ++ₗ ';' ∷ '\n' ∷ outer-suffix)
    l4-rebuilt = subst (λ chars → SuffixStops isHSpace (chars ++ₗ ';' ∷ '\n' ∷ outer-suffix))
                       (sym showInt-eq)
                       (value-stops-isHSpace-RavDecRatBareInt z outer-suffix)

    result-eq :
      just (mkResult (mkRawAttrAssign name (ATgtSignal cid sig)
                       (liftRavw (RavwBareInt z')))
              (advancePositions pos
                (emit attrAssignFmt (name , RatwSig (rawCanIdℕ cid) sig , RavwBareInt z' , tt)))
              outer-suffix)
      ≡ just (mkResult
                (mkRawAttrAssign name (ATgtSignal cid sig) (RavDecRat (fromℤ z)))
                (TraceSignal.pos9 pos name cid sig (showInt-chars z) outer-suffix)
                outer-suffix)
    result-eq =
      cong₂ (λ rav fp → just (mkResult (mkRawAttrAssign name (ATgtSignal cid sig) rav)
                                       fp outer-suffix))
            value-eq pos-eq
      where
        value-eq : liftRavw (RavwBareInt z') ≡ RavDecRat (fromℤ z)
        value-eq = refl

        pos-eq : advancePositions pos
                   (emit attrAssignFmt (name , RatwSig (rawCanIdℕ cid) sig , RavwBareInt z' , tt))
               ≡ TraceSignal.pos9 pos name cid sig (showInt-chars z) outer-suffix
        pos-eq = cong (advancePositions pos)
          (trans (emit-attrAssignFmt-RatwSig name (rawCanIdℕ cid) sig (RavwBareInt z'))
                 (trans
                   (pos-eq-chars name cid sig (showInt-chars (intDecRatToℤ z')))
                   (cong (λ chars →
                           toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
                             toList " SG_ " ++ₗ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
                             ' ' ∷ Identifier.name sig ++ₗ
                             ' ' ∷ chars ++ₗ ';' ∷ '\n' ∷ [])
                         showInt-eq)))
