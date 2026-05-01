{-# OPTIONS --safe --without-K #-}

-- B.3.d Layer 3 3d.5.d 3c-B — `parseRawAttrAssign` × ATgtEnvVar per-line
-- construct roundtrips (3 emit shapes), η-style migration onto the
-- universal `parseAttrAssign-format-roundtrip` lemma.
--
-- ATgtEnvVar is the `RatwEv ev` constructor of `RawAttrTargetWire`, routed
-- through the `evArm` (`"EV_" ++ ws + ident + ws`) of `stdTargetWireFmt`'s
-- 5-way altSum.  Top-level disjointness against `altSum (altSum nodeArm
-- msgArm) sigArm` (closed via build-EmitsOK-stdTargetWireFmt-RatwEv).  No
-- buildCANId step (RatwEv has Identifier, not raw ℕ).
--
-- Carries an `IdentNameStop` precondition for `ev` (Layer 4 owes it from
-- `validIdentifierᵇ`), used by `build-EmitsOK-stdTargetWireFmt-RatwEv`'s
-- name-stop input.

module Aletheia.DBC.TextParser.Properties.Attributes.Assign.EnvVar where

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

open import Aletheia.DBC.TextParser.Attributes
  using (parseRawAttrAssign;
         RawAttrAssign; mkRawAttrAssign;
         RawAttrValue; RavString; RavDecRat;
         liftRavw; buildAttrAssignP)
open import Aletheia.DBC.TextParser.Lexer
  using (parseWS; parseWSOpt; parseStringLit; parseNewline;
         isHSpace)

open import Aletheia.DBC.TextFormatter.Emitter
  using (quoteStringLit-chars; showDecRat-dec-chars; showInt-chars; digitChar)

open import Aletheia.DBC.TextParser.DecRatParse.Properties using
  ( bind-just-step
  ; SuffixStops; ∷-stop; []-stop)
open import Aletheia.DBC.TextParser.Properties.Preamble.Newline using
  ( isNewlineStart
  ; manyHelper-parseNewline-exhaust)
open import Aletheia.DBC.TextParser.Properties.Attributes.Assign.Common using
  ( value-stops-isHSpace-RavString
  ; value-stops-isHSpace-RavDecRatFrac
  ; value-stops-isHSpace-RavDecRatBareInt)
open import Aletheia.DBC.TextParser.Properties.Attributes.Assign.Node using
  ( IdentNameStop)

open import Aletheia.DBC.TextParser.Format using
  (Format; emit; parse; EmitsOK)
open import Aletheia.DBC.TextParser.Format.AttrValue using
  (RawAttrValueWire; RavwString; RavwFrac; RavwBareInt;
   attrValueWireFmt;
   build-EmitsOK-RavwString;
   build-EmitsOK-RavwFrac;
   build-EmitsOK-RavwBareInt)
open import Aletheia.DBC.TextParser.Format.AttrLine using
  (attrAssignFmt; AttrAssignCarrier;
   stdTargetWireFmt; RatwEv;
   parseAttrAssign-format-roundtrip;
   emit-attrAssignFmt-RatwEv;
   emit-attrAssignFmt-RatwEv-with-outer;
   build-EmitsOK-stdTargetWireFmt-RatwEv)

-- ============================================================================
-- TRACE MODULE — kept for `Properties/Attributes/Line.agda` compatibility
-- ============================================================================

module TraceEnvVar (pos : Position) (name : List Char) (ev : Identifier)
                   (value-chars : List Char) (outer-suffix : List Char) where
  cs-name : List Char
  cs-name = quoteStringLit-chars name

  cs-ev : List Char
  cs-ev = Identifier.name ev

  pos9 : Position
  pos9 = advancePositions pos
           (toList "BA_ " ++ₗ cs-name ++ₗ
            toList " EV_ " ++ₗ cs-ev ++ₗ
            ' ' ∷ value-chars ++ₗ ';' ∷ '\n' ∷ [])

-- ============================================================================
-- BRIDGES — emit form ↔ inline-input shape
-- ============================================================================

private
  bridge-EnvVar-emit :
    ∀ (name : List Char) (ev : Identifier)
      (wireVal : RawAttrValueWire) (outer-suffix : List Char)
    → emit attrAssignFmt (name , RatwEv ev , wireVal , tt) ++ₗ outer-suffix
      ≡ toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
          toList " EV_ " ++ₗ Identifier.name ev ++ₗ
          ' ' ∷ emit attrValueWireFmt wireVal ++ₗ ';' ∷ '\n' ∷ outer-suffix
  bridge-EnvVar-emit = emit-attrAssignFmt-RatwEv-with-outer

-- ============================================================================
-- COMMON RAW-LEVEL ROUNDTRIP — EnvVar arm
-- ============================================================================

private
  parseRawAttrAssign-format-roundtrip-EnvVar-raw :
    ∀ (pos : Position) (name : List Char) (ev : Identifier)
      (wireVal : RawAttrValueWire) (outer-suffix : List Char)
    → IdentNameStop ev
    → SuffixStops isNewlineStart outer-suffix
    → SuffixStops isHSpace
        (emit attrValueWireFmt wireVal ++ₗ ';' ∷ '\n' ∷ outer-suffix)
    → EmitsOK attrValueWireFmt wireVal (';' ∷ '\n' ∷ outer-suffix)
    → parseRawAttrAssign pos
        (emit attrAssignFmt (name , RatwEv ev , wireVal , tt) ++ₗ outer-suffix)
      ≡ just (mkResult (mkRawAttrAssign name (ATgtEnvVar ev) (liftRavw wireVal))
                (advancePositions pos
                  (emit attrAssignFmt (name , RatwEv ev , wireVal , tt)))
                outer-suffix)
  parseRawAttrAssign-format-roundtrip-EnvVar-raw pos name ev wireVal outer-suffix
                                                 (c , cs , cs-eq , c-not-hsp)
                                                 ss-NL val-stop l6 =
    trans step-format
      (trans step-many-newline step-buildP)
    where
      pos-line : Position
      pos-line = advancePositions pos
                   (emit attrAssignFmt (name , RatwEv ev , wireVal , tt))

      cont-line : AttrAssignCarrier → Parser RawAttrAssign
      cont-line c = many parseNewline >>= λ _ →
                    buildAttrAssignP (proj₁ c)
                                     (proj₁ (proj₂ c))
                                     (proj₁ (proj₂ (proj₂ c)))

      cont-blanks : List Char → Parser RawAttrAssign
      cont-blanks _ = buildAttrAssignP name (RatwEv ev) wireVal

      l4 : SuffixStops isHSpace
            (emit stdTargetWireFmt (RatwEv ev) ++ₗ
             emit attrValueWireFmt wireVal ++ₗ ';' ∷ '\n' ∷ outer-suffix)
      l4 = ∷-stop refl

      name-stop : SuffixStops isHSpace
        ((Identifier.name ev ++ₗ ' ' ∷ []) ++ₗ
         (emit attrValueWireFmt wireVal ++ₗ ';' ∷ '\n' ∷ outer-suffix))
      name-stop = subst (λ chars → SuffixStops isHSpace
                            ((chars ++ₗ ' ' ∷ []) ++ₗ
                             (emit attrValueWireFmt wireVal ++ₗ ';' ∷ '\n' ∷ outer-suffix)))
                        (sym cs-eq) (∷-stop c-not-hsp)

      l5 : EmitsOK stdTargetWireFmt (RatwEv ev)
            (emit attrValueWireFmt wireVal ++ₗ ';' ∷ '\n' ∷ outer-suffix)
      l5 = build-EmitsOK-stdTargetWireFmt-RatwEv ev
            (emit attrValueWireFmt wireVal ++ₗ ';' ∷ '\n' ∷ outer-suffix)
            name-stop val-stop

      step-format :
        parseRawAttrAssign pos
          (emit attrAssignFmt (name , RatwEv ev , wireVal , tt) ++ₗ outer-suffix)
        ≡ cont-line (name , RatwEv ev , wireVal , tt) pos-line outer-suffix
      step-format =
        bind-just-step (parse attrAssignFmt) cont-line
          pos
          (emit attrAssignFmt (name , RatwEv ev , wireVal , tt) ++ₗ outer-suffix)
          (name , RatwEv ev , wireVal , tt) pos-line outer-suffix
          (parseAttrAssign-format-roundtrip pos name (RatwEv ev) wireVal
            outer-suffix l4 l5 l6)

      step-many-newline :
        cont-line (name , RatwEv ev , wireVal , tt) pos-line outer-suffix
        ≡ cont-blanks [] pos-line outer-suffix
      step-many-newline =
        bind-just-step (many parseNewline) cont-blanks
          pos-line outer-suffix
          [] pos-line outer-suffix
          (manyHelper-parseNewline-exhaust pos-line outer-suffix
            (length outer-suffix) ss-NL)

      step-buildP :
        cont-blanks [] pos-line outer-suffix
        ≡ just (mkResult (mkRawAttrAssign name (ATgtEnvVar ev) (liftRavw wireVal))
                  pos-line outer-suffix)
      step-buildP = refl

-- ============================================================================
-- pos-eq helper: emit-attrAssignFmt-RatwEv RHS ↔ TraceEnvVar.pos9 chars
-- ============================================================================
--
-- One ++ₗ-assoc step (over name ev ++ ' ∷ []) bridges the inner EV_ chunk
-- shape to the canonical " EV_ " ++ name ev ++ ' ∷ value-chars form.

private
  pos-eq-chars :
    ∀ (n : List Char) (ev : Identifier) (value-chars : List Char) →
    toList "BA_ " ++ₗ quoteStringLit-chars n ++ₗ
      ' ' ∷ (toList "EV_" ++ₗ ' ' ∷ Identifier.name ev ++ₗ ' ' ∷ []) ++ₗ
        (value-chars ++ₗ ';' ∷ '\n' ∷ [])
    ≡ toList "BA_ " ++ₗ quoteStringLit-chars n ++ₗ
        toList " EV_ " ++ₗ Identifier.name ev ++ₗ
        ' ' ∷ value-chars ++ₗ ';' ∷ '\n' ∷ []
  pos-eq-chars n ev value-chars =
    cong (λ z → toList "BA_ " ++ₗ quoteStringLit-chars n ++ₗ
                   ' ' ∷ 'E' ∷ 'V' ∷ '_' ∷ ' ' ∷ z)
         (++ₗ-assoc (Identifier.name ev) (' ' ∷ [])
                    (value-chars ++ₗ ';' ∷ '\n' ∷ []))

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
parseRawAttrAssign-roundtrip-ATgtEnvVar-RavString pos name ev s outer-suffix ident-stop ss-NL =
  trans
    (cong (parseRawAttrAssign pos)
          (sym (bridge-EnvVar-emit name ev (RavwString s) outer-suffix)))
    (trans
      (parseRawAttrAssign-format-roundtrip-EnvVar-raw pos name ev
        (RavwString s) outer-suffix ident-stop ss-NL
        (value-stops-isHSpace-RavString s outer-suffix)
        (build-EmitsOK-RavwString s (';' ∷ '\n' ∷ outer-suffix) (∷-stop refl)))
      result-eq)
  where
    result-eq :
      just (mkResult (mkRawAttrAssign name (ATgtEnvVar ev)
                       (liftRavw (RavwString s)))
              (advancePositions pos
                (emit attrAssignFmt (name , RatwEv ev , RavwString s , tt)))
              outer-suffix)
      ≡ just (mkResult
                (mkRawAttrAssign name (ATgtEnvVar ev) (RavString s))
                (TraceEnvVar.pos9 pos name ev (quoteStringLit-chars s) outer-suffix)
                outer-suffix)
    result-eq = cong (λ p → just (mkResult
                                    (mkRawAttrAssign name (ATgtEnvVar ev) (RavString s))
                                    p outer-suffix))
                     (cong (advancePositions pos)
                           (trans (emit-attrAssignFmt-RatwEv name ev (RavwString s))
                                  (pos-eq-chars name ev (quoteStringLit-chars s))))

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
parseRawAttrAssign-roundtrip-ATgtEnvVar-RavDecRatFrac pos name ev d outer-suffix ident-stop ss-NL =
  trans
    (cong (parseRawAttrAssign pos)
          (sym (bridge-EnvVar-emit name ev (RavwFrac d) outer-suffix)))
    (trans
      (parseRawAttrAssign-format-roundtrip-EnvVar-raw pos name ev
        (RavwFrac d) outer-suffix ident-stop ss-NL
        (value-stops-isHSpace-RavDecRatFrac d outer-suffix)
        (build-EmitsOK-RavwFrac d (';' ∷ '\n' ∷ outer-suffix) (∷-stop refl)))
      result-eq)
  where
    result-eq :
      just (mkResult (mkRawAttrAssign name (ATgtEnvVar ev)
                       (liftRavw (RavwFrac d)))
              (advancePositions pos
                (emit attrAssignFmt (name , RatwEv ev , RavwFrac d , tt)))
              outer-suffix)
      ≡ just (mkResult
                (mkRawAttrAssign name (ATgtEnvVar ev) (RavDecRat d))
                (TraceEnvVar.pos9 pos name ev (showDecRat-dec-chars d) outer-suffix)
                outer-suffix)
    result-eq = cong (λ p → just (mkResult
                                    (mkRawAttrAssign name (ATgtEnvVar ev) (RavDecRat d))
                                    p outer-suffix))
                     (cong (advancePositions pos)
                           (trans (emit-attrAssignFmt-RatwEv name ev (RavwFrac d))
                                  (pos-eq-chars name ev (showDecRat-dec-chars d))))

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
parseRawAttrAssign-roundtrip-ATgtEnvVar-RavDecRatBareInt pos name ev z outer-suffix ident-stop ss-NL =
  trans
    (cong (parseRawAttrAssign pos) reshape-input)
    (trans
      (parseRawAttrAssign-format-roundtrip-EnvVar-raw pos name ev
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
        toList " EV_ " ++ₗ Identifier.name ev ++ₗ
        ' ' ∷ showInt-chars z ++ₗ toList ";\n" ++ₗ outer-suffix
      ≡ emit attrAssignFmt (name , RatwEv ev , RavwBareInt z' , tt) ++ₗ outer-suffix
    reshape-input =
      trans (cong (λ chars →
              toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
                toList " EV_ " ++ₗ Identifier.name ev ++ₗ
                ' ' ∷ chars ++ₗ toList ";\n" ++ₗ outer-suffix)
              (sym showInt-eq))
        (sym (bridge-EnvVar-emit name ev (RavwBareInt z') outer-suffix))

    l4-rebuilt : SuffixStops isHSpace
      (emit attrValueWireFmt (RavwBareInt z') ++ₗ ';' ∷ '\n' ∷ outer-suffix)
    l4-rebuilt = subst (λ chars → SuffixStops isHSpace (chars ++ₗ ';' ∷ '\n' ∷ outer-suffix))
                       (sym showInt-eq)
                       (value-stops-isHSpace-RavDecRatBareInt z outer-suffix)

    result-eq :
      just (mkResult (mkRawAttrAssign name (ATgtEnvVar ev)
                       (liftRavw (RavwBareInt z')))
              (advancePositions pos
                (emit attrAssignFmt (name , RatwEv ev , RavwBareInt z' , tt)))
              outer-suffix)
      ≡ just (mkResult
                (mkRawAttrAssign name (ATgtEnvVar ev) (RavDecRat (fromℤ z)))
                (TraceEnvVar.pos9 pos name ev (showInt-chars z) outer-suffix)
                outer-suffix)
    result-eq =
      cong₂ (λ rav fp → just (mkResult (mkRawAttrAssign name (ATgtEnvVar ev) rav)
                                       fp outer-suffix))
            value-eq pos-eq
      where
        value-eq : liftRavw (RavwBareInt z') ≡ RavDecRat (fromℤ z)
        value-eq = refl

        pos-eq : advancePositions pos
                   (emit attrAssignFmt (name , RatwEv ev , RavwBareInt z' , tt))
               ≡ TraceEnvVar.pos9 pos name ev (showInt-chars z) outer-suffix
        pos-eq = cong (advancePositions pos)
          (trans (emit-attrAssignFmt-RatwEv name ev (RavwBareInt z'))
                 (trans
                   (pos-eq-chars name ev (showInt-chars (intDecRatToℤ z')))
                   (cong (λ chars →
                           toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
                             toList " EV_ " ++ₗ Identifier.name ev ++ₗ
                             ' ' ∷ chars ++ₗ ';' ∷ '\n' ∷ [])
                         showInt-eq)))
