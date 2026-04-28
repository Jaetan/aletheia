{-# OPTIONS --safe --without-K #-}

-- B.3.d Layer 3 3d.5.c-η — DSL-side `signalLineFmt`.
--
-- The full SG_ signal-line format as a single `Format RawSignal`.
-- Replaces the production `parseSignalLine` (in
-- `Topology.SignalLine`); the universal `roundtrip` theorem in
-- `Format.agda` discharges parse-after-emit for the whole line in one
-- structural pass.  The companion module
-- `Format.SignalLine.Roundtrip` builds the `EmitsOK` certificate from
-- domain preconditions on `RawSignal` and exposes the slim
-- `signalLine-roundtrip` derived from `roundtrip signalLineFmt`.
--
-- Whitespace fidelity (production-permissive, canonical-emit):
--   * `wsOpt`  — wherever production runs `parseWSOpt` (zero-or-more
--                spaces/tabs).  Canonical emit `[]`.
--   * `ws`     — wherever production runs `parseWS`    (one-or-more).
--                Canonical emit `' ' ∷ []`.
-- The two DSL constructors share the underlying `parseWSOpt`/`parseWS`
-- combinators, so the production parser keeps its tolerance for
-- non-canonical whitespace while the formal roundtrip pins canonical.
--
-- Mux-marker shape: per-branch `withWS` (NOT shared outside the altSum).
-- Production's `parseMuxMarker` is
--     (parseWS *> ((char 'M' …) <|> (char 'm' …))) <|> pure NotMux
-- where the leading `parseWS` lives *inside* the outer `<|>`.  A shared
-- `withWS` would force NotMux to consume a leading space; per-branch
-- mirrors the outer-`<|>` pure NotMux semantics.  `_<|>_`'s reset-on-
-- failure semantics keeps each per-branch `parseWS` attempt independent.
--
-- Newline: `parseNewline = (string "\r\n" *> pure '\n') <|> char '\n'`
-- maps to an `altSum` over the two literals collapsed to `⊤` via iso.
-- Canonical emit picks the inj₂ branch (lone `\n`).
--
-- Structure: 6 named per-segment chunks composed at the top via right-
-- associated `pair`, then a single top-level iso to `RawSignal`.  Each
-- chunk owns its leading whitespace and surrounding literals; carriers
-- are flattened via per-chunk iso so the top-level composition is a
-- shallow 6-deep `pair`.
module Aletheia.DBC.TextParser.Format.SignalLine where

open import Data.Bool using (Bool; true; false)
open import Data.Char using (Char)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_; proj₂)
open import Data.String using (toList)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl)

open import Aletheia.DBC.Identifier using (Identifier)
open import Aletheia.DBC.DecRat using (DecRat)
open import Aletheia.DBC.CanonicalReceivers using (CanonicalReceivers)
open import Aletheia.CAN.Endianness using
  (ByteOrder; LittleEndian; BigEndian)
open import Aletheia.DBC.TextParser.Topology.Foundations using
  (MuxMarker; NotMux; IsMux; SelBy; BothMux;
   RawSignal; mkRawSignal)
open import Aletheia.DBC.TextParser.Format using
  (Format; literal; ident; nat; stringLit; pair; iso; altSum;
   decRat; wsOpt; ws; wsCanonOne; withPrefix)
open import Aletheia.DBC.TextParser.Format.Receivers using
  (canonicalReceiversFmt)

-- ============================================================================
-- LOCAL SUGAR
-- ============================================================================

-- Whitespace prefixes prepended to a format `f`.  Carrier unchanged:
-- forward projects the right component, backward pairs `tt` with
-- `f`'s value.  Three flavours match the production parser/formatter
-- pairings:
--   * `withWSOpt`     — canonical empty, parser zero-or-more.  Used
--                       only for the pre-newline slot (formatter emits
--                       `""` before `\n`).
--   * `withWS`        — canonical single space, parser one-or-more.
--                       Used at mandatory-separator slots.
--   * `withWSCanonOne` — canonical single space, parser zero-or-more.
--                       Used at production `parseWSOpt` slots where
--                       the formatter emits a single space.
withWSOpt : ∀ {A} → Format A → Format A
withWSOpt f = iso proj₂ (λ a → tt , a) (λ _ → refl) (pair wsOpt f)

withWS : ∀ {A} → Format A → Format A
withWS f = iso proj₂ (λ a → tt , a) (λ _ → refl) (pair ws f)

withWSCanonOne : ∀ {A} → Format A → Format A
withWSCanonOne f = iso proj₂ (λ a → tt , a) (λ _ → refl) (pair wsCanonOne f)

-- Newline literal: accepts "\r\n" or "\n", canonical emit "\n".  The
-- iso collapses `⊤ ⊎ ⊤` to `⊤` by always choosing inj₂ for emit.
newlineFmt : Format ⊤
newlineFmt = iso (λ _ → tt) (λ _ → inj₂ tt) (λ _ → refl)
                  (altSum (literal ('\r' ∷ '\n' ∷ []))
                          (literal ('\n' ∷ [])))

-- ============================================================================
-- MUX MARKER FORMAT
-- ============================================================================

private
  isMuxFmt : Format ⊤
  isMuxFmt = withWS (literal ('M' ∷ []))

  bothMuxFmt : Format ℕ
  bothMuxFmt = withWS (iso (λ (n , _) → n)
                            (λ n → n , tt)
                            (λ _ → refl)
                            (pair (withPrefix ('m' ∷ []) nat)
                                  (literal ('M' ∷ []))))

  selByFmt : Format ℕ
  selByFmt = withWS (withPrefix ('m' ∷ []) nat)

  notMuxFmt : Format ⊤
  notMuxFmt = literal []

  -- Priority order: IsMux > BothMux > SelBy > NotMux (mirrors
  -- parseMuxMarker's nested `<|>` chain).
  MuxAltCarrier : Set
  MuxAltCarrier = ⊤ ⊎ (ℕ ⊎ (ℕ ⊎ ⊤))

  muxAltFmt : Format MuxAltCarrier
  muxAltFmt = altSum isMuxFmt
                (altSum bothMuxFmt
                  (altSum selByFmt
                    notMuxFmt))

  φMux : MuxAltCarrier → MuxMarker
  φMux (inj₁ tt)               = IsMux
  φMux (inj₂ (inj₁ n))         = BothMux n
  φMux (inj₂ (inj₂ (inj₁ n)))  = SelBy n
  φMux (inj₂ (inj₂ (inj₂ tt))) = NotMux

  ψMux : MuxMarker → MuxAltCarrier
  ψMux IsMux       = inj₁ tt
  ψMux (BothMux n) = inj₂ (inj₁ n)
  ψMux (SelBy n)   = inj₂ (inj₂ (inj₁ n))
  ψMux NotMux      = inj₂ (inj₂ (inj₂ tt))

  φψ-Mux : ∀ m → φMux (ψMux m) ≡ m
  φψ-Mux IsMux       = refl
  φψ-Mux (BothMux _) = refl
  φψ-Mux (SelBy _)   = refl
  φψ-Mux NotMux      = refl

muxMarkerFmt : Format MuxMarker
muxMarkerFmt = iso φMux ψMux φψ-Mux muxAltFmt

-- ============================================================================
-- BYTE ORDER + SIGN FLAG (one-byte selectors)
-- ============================================================================

-- DBC: '0' = BigEndian, '1' = LittleEndian.
private
  byteOrderAltFmt : Format (⊤ ⊎ ⊤)
  byteOrderAltFmt = altSum (literal ('0' ∷ [])) (literal ('1' ∷ []))

  φBO : ⊤ ⊎ ⊤ → ByteOrder
  φBO (inj₁ _) = BigEndian
  φBO (inj₂ _) = LittleEndian

  ψBO : ByteOrder → ⊤ ⊎ ⊤
  ψBO BigEndian    = inj₁ tt
  ψBO LittleEndian = inj₂ tt

  φψ-BO : ∀ b → φBO (ψBO b) ≡ b
  φψ-BO BigEndian    = refl
  φψ-BO LittleEndian = refl

byteOrderFmt : Format ByteOrder
byteOrderFmt = iso φBO ψBO φψ-BO byteOrderAltFmt

-- DBC: '+' = unsigned (`isSigned ≡ false`), '-' = signed (`true`).
private
  signFlagAltFmt : Format (⊤ ⊎ ⊤)
  signFlagAltFmt = altSum (literal ('+' ∷ [])) (literal ('-' ∷ []))

  φSgn : ⊤ ⊎ ⊤ → Bool
  φSgn (inj₁ _) = false
  φSgn (inj₂ _) = true

  ψSgn : Bool → ⊤ ⊎ ⊤
  ψSgn false = inj₁ tt
  ψSgn true  = inj₂ tt

  φψ-Sgn : ∀ b → φSgn (ψSgn b) ≡ b
  φψ-Sgn false = refl
  φψ-Sgn true  = refl

signFlagFmt : Format Bool
signFlagFmt = iso φSgn ψSgn φψ-Sgn signFlagAltFmt

-- ============================================================================
-- PER-SEGMENT CHUNKS
-- ============================================================================

-- Header: " SG_ <ident>"  →  Format Identifier.
-- Leading `withWSCanonOne` matches `emitSignalLine-chars`'s leading
-- `" SG_ "` while keeping production parseWSOpt tolerance.
headerFmt : Format Identifier
headerFmt =
  withWSCanonOne (
    withPrefix (toList "SG_") (
      withWS ident))

-- Size: " : <sb>|<bl>@<bo><sgn>"  →  Format (ℕ × ℕ × ByteOrder × Bool).
-- Two `withWSCanonOne` (pre-`:` and post-`:`) match the formatter's
-- `" : "`; both correspond to production `parseWSOpt` slots.
sizeFmt : Format (ℕ × (ℕ × (ByteOrder × Bool)))
sizeFmt =
  withWSCanonOne (
    withPrefix (':' ∷ []) (
      withWSCanonOne (
        pair nat (
          withPrefix ('|' ∷ []) (
            pair nat (
              withPrefix ('@' ∷ []) (
                pair byteOrderFmt signFlagFmt)))))))

-- Scaling: " (<factor>,<offset>)"  →  Format (DecRat × DecRat).
-- Leading `withWSCanonOne` for the formatter's pre-`(` space.  The
-- trailing `)` is absorbed via iso to keep the carrier flat.
scalingFmt : Format (DecRat × DecRat)
scalingFmt =
  iso (λ (f , o , _) → f , o)
      (λ (f , o) → f , o , tt)
      (λ _ → refl)
      (withWSCanonOne (
        withPrefix ('(' ∷ []) (
          pair decRat (
            withPrefix (',' ∷ []) (
              pair decRat (literal (')' ∷ [])))))))

-- Range: " [<min>|<max>]"  →  Format (DecRat × DecRat).
-- Leading `withWSCanonOne` for the formatter's `") "` post-scaling space.
rangeFmt : Format (DecRat × DecRat)
rangeFmt =
  iso (λ (mn , mx , _) → mn , mx)
      (λ (mn , mx) → mn , mx , tt)
      (λ _ → refl)
      (withWSCanonOne (
        withPrefix ('[' ∷ []) (
          pair decRat (
            withPrefix ('|' ∷ []) (
              pair decRat (literal (']' ∷ [])))))))

-- Tail: " <unit> <receivers>\n"  →  Format (List Char × CanonicalReceivers).
-- Two `withWSCanonOne` (pre-unit `"] "` trailing space and pre-recv
-- post-unit space) + one `withWSOpt` for the pre-newline slot
-- (formatter emits `""` there).  Underlying chain's trailing ⊤ from
-- `newlineFmt` is flattened by the top iso.
tailFmt : Format (List Char × CanonicalReceivers)
tailFmt =
  iso (λ (u , r , _) → u , r)
      (λ (u , r) → u , r , tt)
      (λ _ → refl)
      (withWSCanonOne (
        pair stringLit (
          withWSCanonOne (
            pair canonicalReceiversFmt (
              withWSOpt newlineFmt)))))

-- ============================================================================
-- TOP-LEVEL SIGNAL LINE
-- ============================================================================
--
-- Composition is right-associated `pair` over the 6 chunks.  Carrier:
--   Identifier × (MuxMarker × ((ℕ × ℕ × ByteOrder × Bool) ×
--     ((DecRat × DecRat) × ((DecRat × DecRat) ×
--       (List Char × CanonicalReceivers)))))
-- The top iso maps this to `RawSignal`.  Record-η on RawSignal makes
-- the iso law `refl`.

private
  RawSignalProductCarrier : Set
  RawSignalProductCarrier =
    Identifier × (MuxMarker × ((ℕ × (ℕ × (ByteOrder × Bool))) ×
    ((DecRat × DecRat) × ((DecRat × DecRat) ×
    (List Char × CanonicalReceivers)))))

  signalLineProductFmt : Format RawSignalProductCarrier
  signalLineProductFmt =
    pair headerFmt (
      pair muxMarkerFmt (
        pair sizeFmt (
          pair scalingFmt (
            pair rangeFmt
              tailFmt))))

  φSig : RawSignalProductCarrier → RawSignal
  φSig (name ,
        mux ,
        (sb , bl , bo , sgn) ,
        (fac , off) ,
        (mn , mx) ,
        (unit , recv)) =
    mkRawSignal name mux sb bl bo sgn fac off mn mx unit recv

  ψSig : RawSignal → RawSignalProductCarrier
  ψSig rs =
    RawSignal.name rs ,
    RawSignal.muxMarker rs ,
    (RawSignal.startBit rs ,
     RawSignal.bitLength rs ,
     RawSignal.byteOrder rs ,
     RawSignal.isSigned rs) ,
    (RawSignal.factor rs ,
     RawSignal.offset rs) ,
    (RawSignal.minimum rs ,
     RawSignal.maximum rs) ,
    (RawSignal.unit rs ,
     RawSignal.receivers rs)

  -- Record-η on `RawSignal` + Σ-η on the nested products.
  φψ-Sig : ∀ rs → φSig (ψSig rs) ≡ rs
  φψ-Sig _ = refl

signalLineFmt : Format RawSignal
signalLineFmt = iso φSig ψSig φψ-Sig signalLineProductFmt
