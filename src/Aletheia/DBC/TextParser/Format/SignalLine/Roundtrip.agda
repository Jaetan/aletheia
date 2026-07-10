-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- universal `signalLine-roundtrip`.
--
-- Closes the parse-after-emit law for `signalLineFmt` via one
-- `roundtrip signalLineFmt` call backed by an `EmitsOK` certificate
-- assembled from two domain preconditions:
--
--   1. `name-stop`     : `RawSignal.name rs`'s first char is non-hspace.
--   2. `recv-cont-stop` : `SuffixStops isReceiverCont suffix` so the
--                         receivers parser stops at the boundary.
--
-- Other obligations (boundary stops between literals, isDigit-stops
-- between numbers, isIdentCont-stops at name boundaries) reduce by
-- pattern-matching since the next char is a known fixed literal
-- (`:`, `|`, `@`, `(`, `)`, `[`, `]`, `,`, `"`, `\n`, `' '`, `M`, `m`).
--
-- Companion to `Format.SignalLine.signalLineFmt`; consumed by
-- `Properties.Topology.Signal` (the slim dispatcher wrappers).
module Aletheia.DBC.TextParser.Format.SignalLine.Roundtrip where

open import Data.Bool using (Bool; true; false)
open import Data.Char using (Char)
open import Data.List using (List; []; _∷_) renaming (_++_ to _++ₗ_)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_; Σ; proj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; sym)

open import Aletheia.Parser.Combinators
  using (Position; mkResult; advancePositions)
open import Aletheia.DBC.Identifier using (Identifier; isIdentCont)
open import Aletheia.DBC.TextParser.Lexer using (isHSpace)
open import Aletheia.DBC.CanonicalReceivers using (CanonicalReceivers)
open import Aletheia.DBC.TextParser.Topology.Foundations using
  (MuxMarker; NotMux; IsMux; SelBy; BothMux;
   RawSignal; mkRawSignal)
open import Aletheia.DBC.TextParser.DecRatParse.Properties
  using (SuffixStops; ∷-stop)
open import Aletheia.DBC.TextParser.Format
  using (Format; emit; parse; EmitsOK; roundtrip)
open import Aletheia.DBC.TextParser.Format.Receivers using (canonicalReceiversFmt)
open import Aletheia.DBC.TextParser.Format.Receivers.Roundtrip using (isReceiverCont)
import Aletheia.DBC.TextParser.Format.Receivers.Roundtrip as ReceiversRT
open import Aletheia.DBC.TextParser.Format.SignalLine using
  (signalLineFmt; muxMarkerFmt; byteOrderFmt; signFlagFmt;
   headerFmt; sizeFmt; scalingFmt; rangeFmt; tailFmt)
open import Aletheia.DBC.TextParser.Properties.Attributes.Assign.Common
  using (digitChar-not-isHSpace)
open import Aletheia.DBC.TextParser.DecRatParse.Properties
  using (showNat-chars-head; bind-just-step)
open import Aletheia.DBC.TextParser.Properties.Primitives
  using (bind-nothing; parseWS-one-space)
open import Aletheia.DBC.TextParser.Lexer using (parseWS)
open import Aletheia.Parser.Combinators
  using (_>>=_; pure)

-- ============================================================================
-- LOCAL HELPERS — double-concat shape after `pair` emit reduction
-- ============================================================================
--
-- `emit (pair f g) (a , b) = emit f a ++ₗ emit g b`.  Combined with the
-- outer `++ₗ rest` from EmitsOK pair's left obligation, the goal at a
-- left-side wsCanonOne becomes `SuffixStops isHSpace ((showNat-chars n
-- ++ₗ rest1) ++ₗ rest2)`.  ++-assoc isn't definitional, so we need a
-- shape-direct helper.

private
  open import Aletheia.DBC.TextFormatter.Emitter using (showNat-chars)
  open import Relation.Binary.PropositionalEquality using (subst)

  showNat-double-stop : ∀ (n : ℕ) (rest1 rest2 : List Char)
    → SuffixStops isHSpace ((showNat-chars n ++ₗ rest1) ++ₗ rest2)
  showNat-double-stop n rest1 rest2 with showNat-chars-head n
  ... | d , tail , _ , eq =
    subst (λ xs → SuffixStops isHSpace ((xs ++ₗ rest1) ++ₗ rest2))
          (sym eq)
          (∷-stop (digitChar-not-isHSpace d))

-- ============================================================================
-- DOMAIN PRECONDITION
-- ============================================================================

-- The signal name's first char must be non-hspace.  Identical to the
-- existing `SignalNameStop`-style precondition the earlier dispatchers
-- carried.
NameStop : RawSignal → Set
NameStop rs =
  Σ Char (λ c → Σ (List Char) (λ cs →
    (Identifier.name (RawSignal.name rs) ≡ c ∷ cs) ×
    (isHSpace c ≡ false)))

-- The first char of `emit canonicalReceiversFmt recv` is non-hspace.
-- Required to discharge the inner `withWSCanonOne` SuffixStops in
-- `tail-EmitsOK`: that slot demands `SuffixStops isHSpace ((emit
-- canonicalReceiversFmt recv ++ '\n' ∷ []) ++ suffix)`, and the head of
-- the outer concat reduces to the head of `emit canonicalReceiversFmt
-- recv` (when non-empty — which the canonical AST guarantees, since
-- the empty case re-encodes as `vectorXXX-id` whose name is `'V' ∷ …`).
-- Owed by a later step via the `isIdentStart→¬isHSpace` bridge for the
-- non-empty cases; the empty case discharges definitionally.
RecvHeadStop : CanonicalReceivers → Set
RecvHeadStop recv =
  Σ Char (λ c → Σ (List Char) (λ cs →
    (emit canonicalReceiversFmt recv ≡ c ∷ cs) × (isHSpace c ≡ false)))

-- ============================================================================
-- PER-CHUNK EmitsOK BUILDERS  (skeleton — fill bottom-up)
-- ============================================================================

open import Aletheia.CAN.Endianness using (ByteOrder; LittleEndian; BigEndian)
open import Aletheia.DBC.DecRat using (DecRat)

-- ============================================================================
-- ALT-FAIL HELPERS for muxMarkerFmt's altSum branches
-- ============================================================================
--
-- Each non-leftmost altSum branch demands `(∀ pos → parse f pos (emit g
-- b ++ suffix) ≡ nothing)` for the alt-fail of the LEFT alt(s).  All
-- six concrete fails below decompose into:
--   1. parseWS consumes the leading `' '` (via parseWS-one-space).
--   2. parseCharsSeq <X> on the next char fails (refl: closed-Char head
--      mismatch reduces parseCharsSeq's char satisfy to nothing).
-- The chain is `bind-just-step (parseWS) ... + bind-nothing (parse
-- (literal X)) ... refl`, wrapped by an outer bind-nothing for the iso
-- envelope around `pair ws (literal X)`.

private
  open import Aletheia.Parser.Combinators using
    (Position; advancePosition; mkResult)
  open import Aletheia.DBC.TextParser.Format using
    (literal; pair; ws; withPrefix; nat; iso)

  -- proj₂ (parse Format.ws pos (' ' ∷ X)) ≡ just (mkResult tt (advancePos pos ' ') X)
  -- when X has SuffixStops isHSpace.
  parse-ws-on-space-stop : ∀ (pos : Position) (X : List Char)
    → SuffixStops isHSpace X
    → proj₂ (parse ws pos (' ' ∷ X)) ≡ just (mkResult tt (advancePosition pos ' ') X)
  parse-ws-on-space-stop pos X ss =
    bind-just-step parseWS (λ _ → pure tt) pos (' ' ∷ X)
                   (' ' ∷ []) (advancePosition pos ' ') X
                   (parseWS-one-space pos X ss)

  -- parse (pair ws f) fails when parseWS consumes leading ' ' and parse
  -- f fails on the next position.  Generalised from the literal-only
  -- form so it accepts iso-wrapped inner formats (used for bothMux's
  -- and selBy's alt-fail proofs).
  pair-ws-f-fails : ∀ {A} (f : Format A) (pos : Position) (X : List Char)
    → SuffixStops isHSpace X
    → proj₂ (parse f (advancePosition pos ' ') X) ≡ nothing
    → proj₂ (parse (pair ws f) pos (' ' ∷ X)) ≡ nothing
  pair-ws-f-fails {A = A} f pos X ss f-fails =
    trans (bind-just-step (parse ws)
                          (λ _ → parse f >>= λ b → pure (tt , b))
                          pos (' ' ∷ X)
                          tt (advancePosition pos ' ') X
                          (parse-ws-on-space-stop pos X ss))
          (bind-nothing (parse f) (λ b → pure (tt , b))
                        (advancePosition pos ' ') X f-fails)

  -- iso-wrap propagates failure: parse (iso φ ψ pf f) = parse f >>= λ x
  -- → pure (φ x).  bind-nothing.
  iso-fails : ∀ {A B} {φ : A → B} {ψ : B → A} {pf : ∀ b → φ (ψ b) ≡ b}
                (f : Format A) (pos : Position) (input : List Char)
    → proj₂ (parse f pos input) ≡ nothing
    → proj₂ (parse (iso φ ψ pf f) pos input) ≡ nothing
  iso-fails {φ = φ} f pos input f-fails =
    bind-nothing (parse f) (λ x → pure (φ x)) pos input f-fails

  -- pair propagates left-failure.
  pair-left-fails : ∀ {A B} (f : Format A) (g : Format B) (pos : Position) (input : List Char)
    → proj₂ (parse f pos input) ≡ nothing
    → proj₂ (parse (pair f g) pos input) ≡ nothing
  pair-left-fails f g pos input f-fails =
    bind-nothing (parse f)
                 (λ a → parse g >>= λ b → pure (a , b))
                 pos input f-fails

  -- pair propagates RIGHT-failure when the LEFT succeeds: bind through
  -- the left's just-step, then bind-nothing through the right's failure
  -- on the post-left residual.  Used in the SelBy bothMux-fail proof
  -- (the natural number's emit consumes 'm<digits>' successfully, then
  -- "M" fails on the trailing ' ').
  pair-left-succeeds-right-fails :
    ∀ {A B} (f : Format A) (g : Format B)
      (pos : Position) (input : List Char)
      (a : A) (pos-a : Position) (residual : List Char)
    → proj₂ (parse f pos input) ≡ just (mkResult a pos-a residual)
    → proj₂ (parse g pos-a residual) ≡ nothing
    → proj₂ (parse (pair f g) pos input) ≡ nothing
  pair-left-succeeds-right-fails f g pos input a pos-a residual eq-f eq-g =
    trans (bind-just-step (parse f)
                          (λ a' → parse g >>= λ b' → pure (a' , b'))
                          pos input a pos-a residual eq-f)
          (bind-nothing (parse g) (λ b' → pure (a , b')) pos-a residual eq-g)

-- (End of private block for the helpers.)

-- HEADER chunk: " SG_ <name>".
-- EmitsOK reduces to a 4-tuple:
--   (s1) SuffixStops isHSpace ("SG_ <name>" ++ rest)  — head 'S', refl
--   (s2) ⊤                                            — literal "SG_"
--   (s3) SuffixStops isHSpace (Identifier.name name ++ rest)
--                                                     — from NameStop
--   (s4) SuffixStops isIdentCont rest                 — caller-provided
header-EmitsOK : ∀ (rs : RawSignal) (rest : List Char)
  → NameStop rs
  → SuffixStops isIdentCont rest
  → EmitsOK headerFmt (RawSignal.name rs) rest
header-EmitsOK rs rest (c , cs , name-eq , c-non-hs) ident-stop
  rewrite name-eq = ∷-stop refl , tt , ∷-stop c-non-hs , ident-stop

-- MUX chunk: " M" / " m<n>M" / " m<n>" / "" depending on muxMarker.
-- Precondition is the SPECIFIC chain shape: rest = ' ' ∷ ':' ∷ rest'
-- (sizeFmt's leading two chars).  This lets every alt-fail close on
-- concrete chars (parseCharsSeq "M" fails on 'm' or ' ' or ':', etc.).
-- Coupling to sizeFmt is acceptable: the universal `roundtrip
-- signalLineFmt` is the only consumer.
mux-EmitsOK : ∀ (mux : MuxMarker) (rest' : List Char)
  → EmitsOK muxMarkerFmt mux (' ' ∷ ':' ∷ rest')
mux-EmitsOK IsMux rest' =
  -- ψMux IsMux = inj₁ tt (first alt; no alt-fail).
  ∷-stop refl , tt
mux-EmitsOK (BothMux n) rest' =
  -- ψMux (BothMux n) = inj₂ (inj₁ n).  isMux fails after parseWS:
  -- parseCharsSeq "M" on 'm' (head of " m<n>M") fails.
  ((∷-stop refl , (tt , ∷-stop refl) , tt) ,
   λ pos →
     bind-nothing (parse (pair ws (literal ('M' ∷ []))))
                  (λ x → pure (proj₂ x))
                  pos (' ' ∷ 'm' ∷ emit nat n ++ₗ 'M' ∷ ' ' ∷ ':' ∷ rest')
                  (pair-ws-f-fails (literal ('M' ∷ [])) pos
                                   ('m' ∷ emit nat n ++ₗ 'M' ∷ ' ' ∷ ':' ∷ rest')
                                   (∷-stop refl) refl))
mux-EmitsOK (SelBy n) rest' =
  -- ψMux (SelBy n) = inj₂ (inj₂ (inj₁ n)).  Two alt-fails:
  -- bothMux-fail (parseNatural roundtrip succeeds, then "M" on ' ' head fails),
  -- isMux-fail (parseWS + "M" on 'm' head).
  (((∷-stop refl , (tt , ∷-stop refl)) ,
    -- bothMux fails: pair ws (iso _ _ _ (pair (withPrefix "m" nat)
    -- (literal "M"))).  After parseWS consumes leading ' ', the
    -- input is 'm' ∷ emit nat n ++ ' ' ∷ ':' ∷ rest'.  The inner
    -- (withPrefix "m" nat) SUCCEEDS (universal roundtrip, since its
    -- emit shape is 'm' ∷ emit nat n), leaving the residual
    -- ' ' ∷ ':' ∷ rest'.  The right (literal "M") then fails on
    -- head ' ' (refl).  Composition uses pair-left-succeeds-right-fails.
    λ pos →
      bind-nothing
        (parse (pair ws (iso (λ (n , _) → n) (λ n → n , tt) (λ _ → refl)
                             (pair (withPrefix ('m' ∷ []) nat) (literal ('M' ∷ []))))))
        (λ x → pure (proj₂ x))
        pos (' ' ∷ 'm' ∷ emit nat n ++ₗ ' ' ∷ ':' ∷ rest')
        (pair-ws-f-fails
          (iso (λ (n , _) → n) (λ n → n , tt) (λ _ → refl)
               (pair (withPrefix ('m' ∷ []) nat) (literal ('M' ∷ []))))
          pos
          ('m' ∷ emit nat n ++ₗ ' ' ∷ ':' ∷ rest')
          (∷-stop refl)
          (bind-nothing
            (parse (pair (withPrefix ('m' ∷ []) nat) (literal ('M' ∷ []))))
            (λ x → pure ((λ (n , _) → n) x))
            (advancePosition pos ' ')
            ('m' ∷ emit nat n ++ₗ ' ' ∷ ':' ∷ rest')
            (pair-left-succeeds-right-fails
              (withPrefix ('m' ∷ []) nat) (literal ('M' ∷ []))
              (advancePosition pos ' ')
              ('m' ∷ emit nat n ++ₗ ' ' ∷ ':' ∷ rest')
              n
              (advancePositions (advancePosition pos ' ') ('m' ∷ emit nat n))
              (' ' ∷ ':' ∷ rest')
              (roundtrip (withPrefix ('m' ∷ []) nat) (advancePosition pos ' ')
                         n (' ' ∷ ':' ∷ rest') (tt , ∷-stop refl))
              refl))))
   ,
   λ pos →
     bind-nothing (parse (pair ws (literal ('M' ∷ []))))
                  (λ x → pure (proj₂ x))
                  pos (' ' ∷ 'm' ∷ emit nat n ++ₗ ' ' ∷ ':' ∷ rest')
                  (pair-ws-f-fails (literal ('M' ∷ [])) pos
                                   ('m' ∷ emit nat n ++ₗ ' ' ∷ ':' ∷ rest')
                                   (∷-stop refl) refl))
mux-EmitsOK NotMux rest' =
  -- ψMux NotMux = inj₂ (inj₂ (inj₂ tt)).  Three alt-fails on input
  -- ' ' ∷ ':' ∷ rest'; all three (selBy/bothMux/isMux) parseWS the ' '
  -- then fail on ':' via the literal head mismatch.
  ((tt ,
    -- selBy fails: pair ws (withPrefix "m" nat).  After parseWS, the
    -- inner withPrefix "m" → parse (literal "m") on ':' fails.
    λ pos →
      bind-nothing (parse (pair ws (withPrefix ('m' ∷ []) nat)))
                   (λ x → pure (proj₂ x))
                   pos (' ' ∷ ':' ∷ rest')
                   (pair-ws-f-fails (withPrefix ('m' ∷ []) nat) pos
                                    (':' ∷ rest') (∷-stop refl)
                                    (bind-nothing (parse (pair (literal ('m' ∷ [])) nat))
                                                  (λ x → pure (proj₂ x))
                                                  (advancePosition pos ' ')
                                                  (':' ∷ rest')
                                                  (pair-left-fails (literal ('m' ∷ [])) nat
                                                                   (advancePosition pos ' ')
                                                                   (':' ∷ rest') refl)))) ,
   -- bothMux fails: pair ws (iso _ _ _ (pair (withPrefix "m" nat)
   -- (literal "M"))).  Inner pair-left fails: parse (withPrefix "m"
   -- nat) on ':' fails (same chain as selBy).
   λ pos →
     bind-nothing
       (parse (pair ws (iso (λ (n , _) → n) (λ n → n , tt) (λ _ → refl)
                            (pair (withPrefix ('m' ∷ []) nat) (literal ('M' ∷ []))))))
       (λ x → pure (proj₂ x))
       pos (' ' ∷ ':' ∷ rest')
       (pair-ws-f-fails (iso (λ (n , _) → n) (λ n → n , tt) (λ _ → refl)
                             (pair (withPrefix ('m' ∷ []) nat) (literal ('M' ∷ []))))
                        pos (':' ∷ rest') (∷-stop refl)
                        (bind-nothing
                          (parse (pair (withPrefix ('m' ∷ []) nat) (literal ('M' ∷ []))))
                          (λ x → pure ((λ (n , _) → n) x))
                          (advancePosition pos ' ') (':' ∷ rest')
                          (pair-left-fails (withPrefix ('m' ∷ []) nat) (literal ('M' ∷ []))
                                           (advancePosition pos ' ') (':' ∷ rest')
                                           (bind-nothing
                                             (parse (pair (literal ('m' ∷ [])) nat))
                                             (λ x → pure (proj₂ x))
                                             (advancePosition pos ' ') (':' ∷ rest')
                                             (pair-left-fails (literal ('m' ∷ [])) nat
                                                              (advancePosition pos ' ')
                                                              (':' ∷ rest') refl)))))) ,
  λ pos →
    bind-nothing (parse (pair ws (literal ('M' ∷ []))))
                 (λ x → pure (proj₂ x))
                 pos (' ' ∷ ':' ∷ rest')
                 (pair-ws-f-fails (literal ('M' ∷ [])) pos
                                  (':' ∷ rest') (∷-stop refl) refl)

-- SIZE chunk: " : <sb>|<bl>@<bo><sgn>".
-- EmitsOK reduces to a 9-tuple:
--   wsCanonOne head ':' (refl), literal ':',
--   wsCanonOne head showNat sb (showNat-chars-head-stop-isHSpace),
--   nat sb next '|' (refl), literal '|',
--   nat bl next '@' (refl), literal '@',
--   byteOrderFmt bo + signFlagFmt sgn — both altSum, alt-fail proofs
--   for inj₂ branches reduce to `refl` (head-mismatch on closed literal).
-- No `rest`-side precondition: sizeFmt's emit ends with signFlagFmt
-- which imposes no constraint on `rest`.
size-EmitsOK : ∀ (sb bl : ℕ) (bo : ByteOrder) (sgn : Bool) (rest : List Char)
  → EmitsOK sizeFmt (sb , bl , bo , sgn) rest
size-EmitsOK sb bl BigEndian false rest =
  ∷-stop refl , tt ,
  showNat-double-stop sb _ rest ,
  ∷-stop refl , tt , ∷-stop refl , tt , tt , tt
size-EmitsOK sb bl BigEndian true rest =
  ∷-stop refl , tt ,
  showNat-double-stop sb _ rest ,
  ∷-stop refl , tt , ∷-stop refl , tt , tt ,
  (tt , λ pos → refl)
size-EmitsOK sb bl LittleEndian false rest =
  ∷-stop refl , tt ,
  showNat-double-stop sb _ rest ,
  ∷-stop refl , tt , ∷-stop refl , tt ,
  (tt , λ pos → refl) ,
  tt
size-EmitsOK sb bl LittleEndian true rest =
  ∷-stop refl , tt ,
  showNat-double-stop sb _ rest ,
  ∷-stop refl , tt , ∷-stop refl , tt ,
  (tt , λ pos → refl) ,
  (tt , λ pos → refl)

-- SCALING chunk: " (<f>,<o>)".
-- EmitsOK reduces to a 6-tuple of all `∷-stop refl` and `tt`:
--   wsCanonOne head '(' (non-hspace), literal '(', decRat f next ',' (non-digit),
--   literal ',', decRat o next ')' (non-digit), literal ')'.
-- No `rest`-side precondition: scalingFmt's emit ends with literal ')'.
scaling-EmitsOK : ∀ (f o : DecRat) (rest : List Char)
  → EmitsOK scalingFmt (f , o) rest
scaling-EmitsOK _ _ _ =
  ∷-stop refl , tt , ∷-stop refl , tt , ∷-stop refl , tt

-- RANGE chunk: " [<min>|<max>]".  Same structural shape as scaling.
range-EmitsOK : ∀ (mn mx : DecRat) (rest : List Char)
  → EmitsOK rangeFmt (mn , mx) rest
range-EmitsOK _ _ _ =
  ∷-stop refl , tt , ∷-stop refl , tt , ∷-stop refl , tt

-- TAIL chunk: ` "<unit>" <recv>\n`.
-- 7-tuple decomposition (the inner `iso` passes through ψ, then the
-- nested `withWSCanonOne`/`pair`/`stringLit`/`canonicalReceiversFmt`/
-- `withWSOpt`/`newlineFmt` reduces structurally):
--
--   s1 : SuffixStops isHSpace head₁         -- outer wsCanonOne head '"'
--   s2 : SuffixStops (≈ᵇ '"') head₂         -- stringLit's stop on inner ' '
--   s3 : SuffixStops isHSpace head₃         -- inner wsCanonOne at recv head
--   s4 : EmitsOK canonicalReceiversFmt …    -- via ReceiversRT.build-emits-ok
--   s5 : SuffixStops isHSpace ('\n' ∷ …)    -- pre-newline wsOpt
--   s6 : ⊤                                   -- literal "\n"
--   s7 : alt-fail of `\r\n` on `'\n' ∷ …`   -- bind-nothing chain via char '\r'
--
-- s1, s2, s5: head reduces to a known literal char, ∷-stop refl.
-- s3: head reduces to head of `emit canonicalReceiversFmt recv`; we
--     `rewrite` with the user-supplied `recv-eq` and close with
--     `c-non-hs`.
-- s4: receivers' EmitsOK from `ReceiversRT.build-emits-ok`, with
--     `'\n' ∷ suffix` head closing via `∷-stop refl` (`isReceiverCont
--     '\n' ≡ false`).
-- s7: `parse (literal "\r\n") pos ('\n' ∷ …)` reduces to `nothing`
--     via `char '\r' pos ('\n' ∷ …) ≡ nothing` (head mismatch).
tail-EmitsOK : ∀ (unit : List Char) (recv : CanonicalReceivers)
                 (suffix : List Char)
  → RecvHeadStop recv
  → SuffixStops isReceiverCont suffix
  → EmitsOK tailFmt (unit , recv) suffix
tail-EmitsOK unit recv suffix (c , cs , recv-eq , c-non-hs) recv-stop =
  ∷-stop refl ,
  ∷-stop refl ,
  s3 ,
  ReceiversRT.build-emits-ok recv ('\n' ∷ suffix) (∷-stop refl) ,
  ∷-stop refl ,
  tt ,
  λ pos → refl
  where
    s3 : SuffixStops isHSpace
           ((emit canonicalReceiversFmt recv ++ₗ '\n' ∷ []) ++ₗ suffix)
    s3 rewrite recv-eq = ∷-stop c-non-hs

-- ============================================================================
-- TOP-LEVEL EmitsOK COMPOSER
-- ============================================================================

-- `signalLineFmt = iso φSig ψSig pf signalLineProductFmt`, where
-- signalLineProductFmt is `pair headerFmt (pair muxMarkerFmt (pair sizeFmt
-- (pair scalingFmt (pair rangeFmt tailFmt))))`.  EmitsOK on iso passes
-- through ψSig; EmitsOK on each `pair` decomposes into the chunk's
-- EmitsOK over its tail-suffix and the right-side chunk's EmitsOK over
-- the smaller suffix.  The 6 chunk-EmitsOKs assemble into a right-
-- associated 6-tuple.
--
-- Pattern-matches on `rs` to expose its fields (so the `EmitsOK` chain
-- reduces to concrete subterms via `ψSig`'s record destructuring), then
-- case-splits on `mux` so that `emit muxMarkerFmt mux` reduces to a
-- concrete shape — exposing the leading ' ' that the `header-EmitsOK`'s
-- `ident-stop` precondition (`SuffixStops isIdentCont …`) discharges via
-- `∷-stop refl`.  In all four mux cases the head is ' ' (non-NotMux:
-- mux's emit starts with ' '; NotMux: mux's emit is `[]` and the next
-- chunk `sizeFmt`'s leading wsCanonOne supplies ' ').
build-emits-ok : ∀ (rs : RawSignal) (suffix : List Char)
  → NameStop rs
  → RecvHeadStop (RawSignal.receivers rs)
  → SuffixStops isReceiverCont suffix
  → EmitsOK signalLineFmt rs suffix
build-emits-ok rs@(mkRawSignal name IsMux sb bl bo sgn fac off mn mx unit recv)
               suffix name-stop recv-head-stop recv-stop =
  header-EmitsOK rs _ name-stop (∷-stop refl) ,
  mux-EmitsOK IsMux _ ,
  size-EmitsOK sb bl bo sgn _ ,
  scaling-EmitsOK fac off _ ,
  range-EmitsOK mn mx _ ,
  tail-EmitsOK unit recv suffix recv-head-stop recv-stop
build-emits-ok rs@(mkRawSignal name (BothMux n) sb bl bo sgn fac off mn mx unit recv)
               suffix name-stop recv-head-stop recv-stop =
  header-EmitsOK rs _ name-stop (∷-stop refl) ,
  mux-EmitsOK (BothMux n) _ ,
  size-EmitsOK sb bl bo sgn _ ,
  scaling-EmitsOK fac off _ ,
  range-EmitsOK mn mx _ ,
  tail-EmitsOK unit recv suffix recv-head-stop recv-stop
build-emits-ok rs@(mkRawSignal name (SelBy n) sb bl bo sgn fac off mn mx unit recv)
               suffix name-stop recv-head-stop recv-stop =
  header-EmitsOK rs _ name-stop (∷-stop refl) ,
  mux-EmitsOK (SelBy n) _ ,
  size-EmitsOK sb bl bo sgn _ ,
  scaling-EmitsOK fac off _ ,
  range-EmitsOK mn mx _ ,
  tail-EmitsOK unit recv suffix recv-head-stop recv-stop
build-emits-ok rs@(mkRawSignal name NotMux sb bl bo sgn fac off mn mx unit recv)
               suffix name-stop recv-head-stop recv-stop =
  -- NotMux's mux-EmitsOK body references `(' ' ∷ ':' ∷ rest')` in three
  -- alt-fail proofs, and Agda can't infer rest' from the goal's
  -- `emit (pair sizeFmt …) … ++ suffix` (the `' ' ∷ ':'` prefix sits
  -- under nested withWSCanonOne/withPrefix isos that don't reduce
  -- transparently for the meta).  Provide rest' explicitly: it's the
  -- third-char-onward of `emit sizeFmt size`, then concatenated with
  -- the remaining chunks and the outer suffix.
  let rest' = ' ' ∷ emit nat sb ++ₗ '|' ∷ emit nat bl
                ++ₗ '@' ∷ emit byteOrderFmt bo ++ₗ emit signFlagFmt sgn
                ++ₗ emit (pair scalingFmt (pair rangeFmt tailFmt))
                         ((fac , off) , (mn , mx) , (unit , recv))
                ++ₗ suffix
  in header-EmitsOK rs _ name-stop (∷-stop refl) ,
     mux-EmitsOK NotMux rest' ,
     size-EmitsOK sb bl bo sgn _ ,
     scaling-EmitsOK fac off _ ,
     range-EmitsOK mn mx _ ,
     tail-EmitsOK unit recv suffix recv-head-stop recv-stop

-- ============================================================================
-- THE GATE
-- ============================================================================

signalLine-roundtrip : ∀ (pos : Position) (rs : RawSignal) (suffix : List Char)
  → NameStop rs
  → RecvHeadStop (RawSignal.receivers rs)
  → SuffixStops isReceiverCont suffix
  → proj₂ (parse signalLineFmt pos (emit signalLineFmt rs ++ₗ suffix))
    ≡ just (mkResult rs (advancePositions pos (emit signalLineFmt rs)) suffix)
signalLine-roundtrip pos rs suffix name-stop recv-head-stop recv-stop =
  roundtrip signalLineFmt pos rs suffix
    (build-emits-ok rs suffix name-stop recv-head-stop recv-stop)
