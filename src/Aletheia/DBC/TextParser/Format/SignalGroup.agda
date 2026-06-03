-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- B.3.d Layer 4a — DSL-side `signalGroupFmt` for the DBC `SIG_GROUP_`
-- line.  Layer 3 carry-over: SignalGroup was the last per-line
-- construct without a Format DSL form (BO_/BA_*/CM_/EV_/VAL_TABLE_/BU_
-- all migrated in 3d.5/3d.8/3c-A/3c-B).
--
-- Wire grammar (BNF section F from `Aletheia.DBC.TextParser`):
--   sig-group ::= "SIG_GROUP_" ws nat ws identifier ws nat ws? ":"
--                 (ws identifier)* ws? ";" newline
--
-- Two wire-only fields the Agda `SignalGroup` record drops:
--   * Owning message's CAN ID — emit canonical `0`.
--   * Repetitions count        — emit canonical `1`.
-- Both captured via `discardFmt` (sugar over `iso` — see `Format/EnvVar`).
--
-- Whitespace fidelity:
--   * `withWS`         — three mandatory single-space slots (after
--                        keyword, after CAN ID, after name).
--   * `withWSCanonOne` — between "1" and ":" (parseWSOpt; emit one).
--   * `withWSOpt`      — between signal list and ";" (parseWSOpt; emit
--                        empty).
--   * `withWS` per signal entry — production parser uses mandatory
--                                  `parseWS` before each ident.
--   * `newlineFmt`     — line terminator; canonical `\n`, parser
--                        accepts `\n` / `\r\n`.
module Aletheia.DBC.TextParser.Format.SignalGroup where

open import Data.Bool using (false)
open import Data.Char using (Char)
open import Data.List using (List; []; _∷_) renaming (_++_ to _++ₗ_)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (s≤s; z≤n)
open import Data.Product using (_×_; _,_; proj₂; Σ-syntax)
open import Data.String using (toList)
open import Data.Sum using (inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; subst)

open import Aletheia.Parser.Combinators
  using (mkResult; advancePositions)
open import Aletheia.DBC.Identifier using (Identifier)
open import Aletheia.DBC.Types using (SignalGroup)
open import Aletheia.DBC.TextParser.Lexer using (isHSpace)
open import Aletheia.DBC.TextParser.DecRatParse.Properties
  using (SuffixStops; ∷-stop)
open import Aletheia.DBC.TextParser.Format
  using (Format; literal; ident; nat; pair; iso; many;
         altSum; ws; wsOpt; wsCanonOne; withPrefix;
         emit; parse; EmitsOK; EmitsOKMany;
         []-fails; ∷-cons;
         roundtrip)

-- ============================================================================
-- LOCAL SUGAR — ws-aware combinators (mirrors Format.ValueTable)
-- ============================================================================

private
  -- Mandatory single space, parser one-or-more.  Canonical emit `' ' ∷ []`.
  withWS : ∀ {A} → Format A → Format A
  withWS f = iso proj₂ (λ a → tt , a) (λ _ → refl) (pair ws f)

  -- Optional whitespace, parser zero-or-more.  Canonical emit `[]`.
  withWSOpt : ∀ {A} → Format A → Format A
  withWSOpt f = iso proj₂ (λ a → tt , a) (λ _ → refl) (pair wsOpt f)

  -- Canonical single space, parser zero-or-more.  Canonical emit `' ' ∷ []`.
  withWSCanonOne : ∀ {A} → Format A → Format A
  withWSCanonOne f =
    iso proj₂ (λ a → tt , a) (λ _ → refl) (pair wsCanonOne f)

  -- Line terminator: accepts `"\r\n"` or `"\n"`, canonical emit `"\n"`.
  newlineFmt : Format ⊤
  newlineFmt = iso (λ _ → tt) (λ _ → inj₂ tt) (λ _ → refl)
                    (altSum (literal ('\r' ∷ '\n' ∷ []))
                            (literal ('\n' ∷ [])))

  -- Discard combinator: parse anything matching `f` (production-permissive),
  -- discard the result; emit `f`'s canonical default.  Mirrors `Format/EnvVar`.
  discardFmt : ∀ {A} → A → Format A → Format ⊤
  discardFmt default f =
    iso (λ _ → tt) (λ _ → default) (λ _ → refl) f

-- ============================================================================
-- PER-SIGNAL FORMAT — `withWS ident` (mandatory leading space + identifier)
-- ============================================================================

-- One ` <name>` entry.  Reused inside `many` for the signal list.
sigEntry-format : Format Identifier
sigEntry-format = withWS ident

-- ============================================================================
-- SIGNALGROUP FORMAT
-- ============================================================================

-- Inner-format carrier: tuple of all parsed pieces in wire order.
-- Wire-only fields (CAN ID, repetitions) collapse to `⊤` via `discardFmt`;
-- the trailing newline format also produces `⊤`.  Right-associative
-- `_×_` flattens the nested-pair structure.
private
  SGInner : Set
  SGInner = ⊤ × Identifier × ⊤ × List Identifier × ⊤

-- Full `SIG_GROUP_ 0 <name> 1 :<sigs>;\n` line.  `bwd` projects with
-- canonical `tt`s in the wire-only slots; `fwd` reconstructs the record.
signalGroupFmt : Format SignalGroup
signalGroupFmt =
  iso fwd bwd (λ _ → refl) inner
  where
    fwd : SGInner → SignalGroup
    fwd (_ , name , _ , sigs , _) = record { name = name ; signals = sigs }

    bwd : SignalGroup → SGInner
    bwd sg =
        tt
      , SignalGroup.name sg
      , tt
      , SignalGroup.signals sg
      , tt

    inner : Format SGInner
    inner =
      withPrefix (toList "SIG_GROUP_") (
        withWS (
          pair (discardFmt 0 nat) (
            withWS (
              pair ident (
                withWS (
                  pair (discardFmt 1 nat) (
                    withWSCanonOne (
                      withPrefix (':' ∷ []) (
                        pair (many sigEntry-format) (
                          withWSOpt (
                            withPrefix (';' ∷ []) newlineFmt)))))))))))

-- ============================================================================
-- PER-LINE / PER-SIGNAL PRECONDITIONS
-- ============================================================================

-- Each SignalGroup's `name` decomposes as `c ∷ cs` with `isHSpace c
-- ≡ false`.  Layer 4 will discharge this universally from
-- `validIdentifierᵇ` via the `isIdentStart→¬isHSpace` bridge (in
-- `Properties/CharClassDisjoint.agda`).
SignalGroupNameStop : SignalGroup → Set
SignalGroupNameStop sg =
  Σ[ c ∈ Char ] Σ[ cs ∈ List Char ]
    (Identifier.name (SignalGroup.name sg) ≡ c ∷ cs) × (isHSpace c ≡ false)

-- Each signal-name's first char is non-hspace.  Like `NodeNameStop` over
-- the BU_ list; Layer 4 discharges via the same identifier bridge.
SigNameStop : Identifier → Set
SigNameStop i =
  Σ[ c ∈ Char ] Σ[ cs ∈ List Char ]
    (Identifier.name i ≡ c ∷ cs) × (isHSpace c ≡ false)

-- ============================================================================
-- TERMINATION CERTIFICATE — `parse sigEntry-format` rejects `;` / `\n`
-- ============================================================================

-- After all entries are parsed, the trailing input is `';' ∷ '\n' ∷ rest`
-- (or `';' ∷ ' ' ∷ ...` if the wsOpt slot has spaces, but the canonical
-- empty case is what `EmitsOK` reduces to).  `parse sigEntry-format`
-- fires `parseWS` on the leading char, which rejects `;` (not hspace).
-- `refl` since every step reduces definitionally on the closed leading char.
parse-sigEntry-fails-on-semi : ∀ pos rest
  → parse sigEntry-format pos (';' ∷ rest) ≡ nothing
parse-sigEntry-fails-on-semi pos rest = refl

-- ============================================================================
-- WELL-FORMEDNESS — per-signal EmitsOK
-- ============================================================================

-- `EmitsOK sigEntry-format i outer-rest` reduces (through `iso → pair → ws`)
-- to `SuffixStops isHSpace (Identifier.name i ++ outer-rest) × SuffixStops
-- isIdentCont outer-rest`.  Caller supplies the per-signal NameStop and
-- the head-of-outer-rest isIdentCont witness.
build-EmitsOK-sigEntry : ∀ (i : Identifier) (outer-rest : List Char)
  → SigNameStop i
  → SuffixStops (Aletheia.DBC.Identifier.isIdentCont) outer-rest
  → EmitsOK sigEntry-format i outer-rest
build-EmitsOK-sigEntry i outer-rest (c , cs , name-eq , c-non-hs) outer-stop =
  (subst (λ xs → SuffixStops isHSpace (xs ++ₗ outer-rest))
         (sym name-eq)
         (∷-stop c-non-hs))
  , outer-stop

-- ============================================================================
-- WELL-FORMEDNESS — signal list (EmitsOKMany)
-- ============================================================================

-- `EmitsOKMany sigEntry-format sigs (';' ∷ '\n' ∷ outer-suffix)`.  Empty:
-- `[]-fails` via `parse-sigEntry-fails-on-semi`.  Cons (last): per-signal
-- EmitsOK against `';' ∷ '\n' ∷ …`; recursive `[]` step.  Cons (non-last):
-- per-signal EmitsOK against next entry's leading `' '`; recursive cons step.
build-EmitsOKMany-sigs : ∀ (sigs : List Identifier) (outer-suffix : List Char)
  → All SigNameStop sigs
  → EmitsOKMany sigEntry-format sigs (';' ∷ '\n' ∷ outer-suffix)
build-EmitsOKMany-sigs [] outer-suffix _ =
  []-fails (λ pos →
    parse-sigEntry-fails-on-semi pos ('\n' ∷ outer-suffix))
build-EmitsOKMany-sigs (i ∷ []) outer-suffix (i-stop ∷ _) =
  ∷-cons
    (build-EmitsOK-sigEntry i (';' ∷ '\n' ∷ outer-suffix) i-stop (∷-stop refl))
    (s≤s z≤n)
    (build-EmitsOKMany-sigs [] outer-suffix [])
build-EmitsOKMany-sigs (i ∷ (i' ∷ rest')) outer-suffix (i-stop ∷ rest-stops) =
  ∷-cons
    (build-EmitsOK-sigEntry i
       (emit (many sigEntry-format) (i' ∷ rest')
        ++ₗ ';' ∷ '\n' ∷ outer-suffix)
       i-stop
       (∷-stop refl))
    (s≤s z≤n)
    (build-EmitsOKMany-sigs (i' ∷ rest') outer-suffix rest-stops)

-- ============================================================================
-- WELL-FORMEDNESS — top-level builder
-- ============================================================================

-- Build `EmitsOK signalGroupFmt sg outer-suffix` from the pair of domain
-- preconditions: `SignalGroupNameStop sg` (the group's name first char is
-- non-hspace) and `All SigNameStop (signals sg)` (each signal's name
-- first char is non-hspace).  Reduces structurally through the layered
-- iso → withPrefix → withWS → discardFmt → ... → newlineFmt chain.
--
-- Tuple structure mirrors the L1–L17 chain in `inner`:
--   L1 (withPrefix "SIG_GROUP_"): vacuous
--   L2 (withWS):                  SuffixStops isHSpace ('0' ∷ ...) — `'0'` non-hspace
--   L3 (pair (discardFmt 0 nat) ...): SuffixStops isDigit (' ' ∷ ...) — ' ' non-digit
--   L4 (withWS):                  SuffixStops isHSpace (name ++ ...) — via NameStop
--   L5 (pair ident ...):          SuffixStops isIdentCont (' ' ∷ ...) — ' ' non-idCont
--   L6 (withWS):                  SuffixStops isHSpace ('1' ∷ ...) — `'1'` non-hspace
--   L7 (pair (discardFmt 1 nat) ...): SuffixStops isDigit (' ' ∷ ...)
--   L8 (withWSCanonOne):          SuffixStops isHSpace (':' ∷ ...) — ':' non-hspace
--   L9 (withPrefix ":"):          vacuous
--   L10 (pair (many sigEntry) ...): EmitsOKMany over sigs at (';' ∷ '\n' ∷ outer)
--   L11 (withWSOpt):              SuffixStops isHSpace (';' ∷ ...) — ';' non-hspace
--   L12 (withPrefix ";"):         vacuous
--   L13 (newlineFmt):             altSum-tree disjointness on inj₂.
private
  -- L4 ws-witness — `SuffixStops isHSpace ((Identifier.name name ++
  -- after-name-rest) ++ outer-suffix)` from the NameStop precondition.
  -- `after-name-rest` is the emit of everything past the name (filled in
  -- by Agda from context at the call site).  Mirrors EV_'s
  -- `ws-slot1-witness` shape.
  ws-slot-name-witness : ∀ (sg : SignalGroup)
                          (after-name-rest outer-suffix : List Char)
    → SignalGroupNameStop sg
    → SuffixStops isHSpace
        ((Identifier.name (SignalGroup.name sg) ++ₗ after-name-rest)
         ++ₗ outer-suffix)
  ws-slot-name-witness sg after-name-rest outer-suffix
                       (c , cs , name-eq , c-non-hs) =
    subst (λ xs → SuffixStops isHSpace
                    ((xs ++ₗ after-name-rest) ++ₗ outer-suffix))
          (sym name-eq)
          (∷-stop c-non-hs)

build-emits-ok : ∀ (sg : SignalGroup) (outer-suffix : List Char)
  → SignalGroupNameStop sg
  → All SigNameStop (SignalGroup.signals sg)
  → EmitsOK signalGroupFmt sg outer-suffix
build-emits-ok sg outer-suffix nameStop sigs-stops =
    -- L1 (withPrefix "SIG_GROUP_"): vacuous.
    tt
    -- L2 (withWS) before discarded "0": head is '0', non-hspace.
  , ∷-stop refl
    -- L3 (pair (discardFmt 0 nat) ...): SuffixStops isDigit on ' ' ∷ name ∷ …, head ' '.
  , ∷-stop refl
    -- L4 (withWS) before name: head is name's first char, non-hspace via NameStop.
  , ws-slot-name-witness sg _ outer-suffix nameStop
    -- L5 (pair ident ...): SuffixStops isIdentCont on ' ' ∷ '1' ∷ …, head ' '.
  , ∷-stop refl
    -- L6 (withWS) before discarded "1": head is '1', non-hspace.
  , ∷-stop refl
    -- L7 (pair (discardFmt 1 nat) ...): SuffixStops isDigit on ' ' ∷ ':' ∷ …, head ' '.
  , ∷-stop refl
    -- L8 (withWSCanonOne) before ':': head is ':', non-hspace.
  , ∷-stop refl
    -- L9 (withPrefix ":"): vacuous.
  , tt
    -- L10 (pair (many sigEntry) ...): EmitsOKMany over sigs.
  , build-EmitsOKMany-sigs (SignalGroup.signals sg) outer-suffix sigs-stops
    -- L11 (withWSOpt) before ';': head is ';', non-hspace.
  , ∷-stop refl
    -- L12 (withPrefix ";"): vacuous.
  , tt
    -- L13 (newlineFmt at inj₂ tt): inner literal "\n" vacuous + altSum
    -- disjointness witness ('\n' doesn't start with '\r').
  , tt
  , (λ pos → refl)

-- ============================================================================
-- TOP-LEVEL ROUNDTRIP — the universal-form theorem
-- ============================================================================

-- THE GATE: parseSignalGroup expressed via Format DSL.  Body is one
-- `roundtrip` call + the EmitsOK construction.  Universal in `sg` and
-- `outer-suffix`; the two domain preconditions are
-- `SignalGroupNameStop sg` and `All SigNameStop (signals sg)`, which
-- Layer 4 discharges universally from identifier validity.
parseSignalGroup-format-roundtrip : ∀ pos sg outer-suffix
  → SignalGroupNameStop sg
  → All SigNameStop (SignalGroup.signals sg)
  → parse signalGroupFmt pos
      (emit signalGroupFmt sg ++ₗ outer-suffix)
    ≡ just (mkResult sg
             (advancePositions pos (emit signalGroupFmt sg))
             outer-suffix)
parseSignalGroup-format-roundtrip pos sg outer-suffix nameStop sigs-stops =
  roundtrip signalGroupFmt pos sg outer-suffix
    (build-emits-ok sg outer-suffix nameStop sigs-stops)
