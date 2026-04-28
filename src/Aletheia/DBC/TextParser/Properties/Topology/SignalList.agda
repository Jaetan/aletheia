{-# OPTIONS --safe --without-K #-}

-- B.3.d Layer 3 3d.6 — `parseSignalLines-roundtrip` over the SG_ block.
--
-- Lifts the per-MuxMarker dispatchers from `Properties.Topology.Signal`
-- (3d.5.c-η) to a list of DBCSignal under `WellFormedTextSignal` +
-- `MasterCoherent` (only the `WellFormedTextPresence` slice of the
-- former is needed here — the receiver-side `NoVectorXXXReceiver` and
-- master-coherence are 3d.7's concerns).
--
-- Composition strategy: apply the framework's universal
-- `roundtrip (many signalLineFmt)` from `Format.agda`.  Two glue lemmas:
--
--   1. `emit-many-signalLineFmt-eq-foldr` — bridge from the DSL's
--      `concatMap (emit signalLineFmt) ∘ map expectedRawOfDBC` shape
--      to the existing formatter's
--      `foldr (λ s acc → emitSignalLine-chars … ++ acc) []` shape.
--      Reduces the list-level emit to per-signal emit-eq via
--      `emit-signalLineFmt-eq-emitSignalLine-chars`.
--   2. `build-emits-ok-many` — assembles `EmitsOKMany signalLineFmt
--      expectedRaws suffix` by structural induction on the signal list.
--      Each `∷-cons` step calls `Format.SignalLine.Roundtrip.build-emits-ok`
--      with the per-signal preconditions; the inter-signal
--      `SuffixStops isReceiverCont` gap is automatic
--      (head of next signal's emit is `' '`); the terminator
--      `ParseFailsAt signalLineFmt outer-suffix` and the last-signal
--      `SuffixStops isReceiverCont outer-suffix` are caller obligations.
--
-- 3d.7 will compose this with `findMuxName ≡ findMuxMaster` and
-- `buildSignal ∘ rawOf ≡ just` to recover the original `List DBCSignal`
-- from the parsed `List RawSignal`.  3d.8 ties everything together via
-- `messageHeaderFmt` + this lemma + the trailing `many parseNewline`.
module Aletheia.DBC.TextParser.Properties.Topology.SignalList where

open import Data.Bool using (Bool; true; false)
open import Data.Char using (Char) renaming (_≟_ to _≟ᶜ_)
import Data.List.Properties as ListProps
open import Data.List using (List; []; _∷_; foldr; map; concatMap; length)
  renaming (_++_ to _++ₗ_)
open import Data.List.Properties using (length-++)
  renaming (++-assoc to ++ₗ-assoc)
open import Data.List.NonEmpty as List⁺ using (List⁺; _∷_)
open import Data.List.Relation.Unary.All as All using (All)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _<_; s≤s; z≤n)
open import Data.Product using (_×_; _,_; Σ; Σ-syntax)
open import Data.String using (toList)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import Aletheia.Parser.Combinators using
  (Position; mkResult; advancePositions)
open import Aletheia.DBC.Identifier using (Identifier)
open import Aletheia.DBC.CanonicalReceivers using (CanonicalReceivers)
open import Aletheia.DBC.Types using
  (DBCSignal; SignalPresence; Always; When)

open import Aletheia.DBC.TextFormatter.Emitter using
  (showℕ-dec-chars; showNat-chars)
open import Aletheia.DBC.TextFormatter.Topology using
  (emitMuxMarker-chars; emitSignalLine-chars)

open import Aletheia.DBC.Formatter.WellFormedText using
  (WellFormedTextPresence; wftp-always; wftp-when-single;
   WellFormedTextSignal)

open import Aletheia.DBC.TextParser.Topology.Foundations using
  (RawSignal; mkRawSignal;
   MuxMarker; NotMux; IsMux; SelBy)
open import Aletheia.DBC.TextParser.Topology using (parseSignalLine)

open import Aletheia.DBC.TextParser.Format using
  (Format; emit; parse; EmitsOK; EmitsOKMany; []-fails; ∷-cons;
   ParseFailsAt; roundtrip)
  renaming (many to manyF)
open import Aletheia.DBC.TextParser.Format.SignalLine using
  (signalLineFmt; muxMarkerFmt)
open import Aletheia.DBC.TextParser.Format.SignalLine.Roundtrip using
  (NameStop; RecvHeadStop;
   build-emits-ok)

open import Aletheia.DBC.TextParser.DecRatParse.Properties using
  (SuffixStops; ∷-stop)
open import Aletheia.DBC.TextParser.Format.Receivers.Roundtrip using
  (isReceiverCont)

open import Aletheia.DBC.TextParser.Properties.Topology.Signal using
  (SignalNameStop; expectedRaw;
   emit-signalLineFmt-eq-emitSignalLine-chars)


-- ============================================================================
-- expectedMux + expectedRawOfDBC — DBC-level analogues of expectedRaw
-- ============================================================================

-- The MuxMarker chosen by the formatter for a signal under `master`:
--   * `Always` + master == name      ⇒ IsMux
--   * `Always` + master /= name      ⇒ NotMux
--   * `Always` + no master           ⇒ NotMux
--   * `When _ (v ∷ _)` (any master)  ⇒ SelBy v   (head of values list)
--
-- Mirrors `emitMuxMarker-chars`'s logic exactly so the per-signal mux
-- bridge below is provable case-by-case.  `BothMux` is unreachable
-- under `WellFormedTextPresence` (singleton-When only) — the formatter
-- never emits an `m<N>M` marker.
--
-- Takes (presence, name) as explicit arguments rather than projecting
-- from a `DBCSignal`; this lets the bridge proof pattern-match directly
-- on `presence` (driving both LHS and RHS reduction in tandem).
nameEq? : List Char → List Char → Bool
nameEq? a b = ⌊ ListProps.≡-dec _≟ᶜ_ a b ⌋

expectedMuxFor : Maybe (List Char) → List Char → SignalPresence → MuxMarker
expectedMuxFor _ _ (When _ (v ∷ _)) = SelBy v
expectedMuxFor nothing  _    Always = NotMux
expectedMuxFor (just m) name Always with nameEq? name m
... | true  = IsMux
... | false = NotMux

expectedMux : Maybe (List Char) → DBCSignal → MuxMarker
expectedMux master sig =
  expectedMuxFor master (Identifier.name (DBCSignal.name sig))
                        (DBCSignal.presence sig)

expectedRawOfDBC : Maybe (List Char) → ℕ → DBCSignal → RawSignal
expectedRawOfDBC master fb sig = expectedRaw (expectedMux master sig) sig fb


-- ============================================================================
-- PER-SIGNAL BRIDGES
-- ============================================================================

-- Bridge: DSL muxMarkerFmt emit on `expectedMuxFor master name presence`
-- matches `emitMuxMarker-chars master name presence`.  Pattern-matches
-- on `wfp` (which determines `presence`'s shape) so both sides reduce
-- in lockstep.
emit-muxMarkerFmt-eq-for :
    ∀ (master : Maybe (List Char)) (name : List Char) (p : SignalPresence)
  → WellFormedTextPresence p
  → emit muxMarkerFmt (expectedMuxFor master name p)
    ≡ emitMuxMarker-chars master name p
emit-muxMarkerFmt-eq-for nothing  _    Always wftp-always = refl
emit-muxMarkerFmt-eq-for (just m) name Always wftp-always with nameEq? name m
... | true  = refl
... | false = refl
-- For the When case: pattern-match on master so the third clause of
-- `emitMuxMarker-chars` (which uses `_` for the first arg but doesn't
-- fire under abstract master because Agda's clause-matching is stuck on
-- the first/second clauses' `nothing`/`just _` requirements until master
-- is concrete) reduces in both branches.
emit-muxMarkerFmt-eq-for nothing  _ (When _ (_ ∷ [])) wftp-when-single = refl
emit-muxMarkerFmt-eq-for (just _) _ (When _ (_ ∷ [])) wftp-when-single = refl

-- Surface form on a `DBCSignal`: project the name/presence and apply.
emit-muxMarkerFmt-eq : ∀ (master : Maybe (List Char)) (sig : DBCSignal)
  → WellFormedTextPresence (DBCSignal.presence sig)
  → emit muxMarkerFmt (expectedMux master sig)
    ≡ emitMuxMarker-chars master (Identifier.name (DBCSignal.name sig))
                                 (DBCSignal.presence sig)
emit-muxMarkerFmt-eq master sig wfp =
  emit-muxMarkerFmt-eq-for master (Identifier.name (DBCSignal.name sig))
                                  (DBCSignal.presence sig) wfp

-- Bridge: DSL signalLineFmt emit on `expectedRawOfDBC master fb sig`
-- matches the existing `emitSignalLine-chars master fb sig`.  Composes
-- the mux bridge with `emit-signalLineFmt-eq-emitSignalLine-chars` from
-- `Properties.Topology.Signal`.
emit-signalLineFmt-eq-DBCSignal :
    ∀ (master : Maybe (List Char)) (fb : ℕ) (sig : DBCSignal)
  → WellFormedTextPresence (DBCSignal.presence sig)
  → emit signalLineFmt (expectedRawOfDBC master fb sig)
    ≡ emitSignalLine-chars master fb sig
emit-signalLineFmt-eq-DBCSignal master fb sig wfp =
  emit-signalLineFmt-eq-emitSignalLine-chars
    (expectedMux master sig) master fb sig
    (emit-muxMarkerFmt-eq master sig wfp)


-- ============================================================================
-- LIST-LEVEL EMIT BRIDGE — concatMap ≡ foldr
-- ============================================================================

-- The DSL's `emit (many signalLineFmt) (map (expectedRawOfDBC master fb) sigs)`
-- expands to `concatMap (emit signalLineFmt) (map _ sigs)`; the formatter's
-- SG_ block is `foldr (λ s acc → emitSignalLine-chars master fb s ++ acc)
-- [] sigs`.  Structural induction over `sigs`, each step applying the
-- per-signal bridge above.
emit-many-signalLineFmt-eq-foldr :
    ∀ (master : Maybe (List Char)) (fb : ℕ)
      (sigs : List DBCSignal)
  → All (λ s → WellFormedTextPresence (DBCSignal.presence s)) sigs
  → emit (manyF signalLineFmt) (map (expectedRawOfDBC master fb) sigs)
    ≡ foldr (λ s acc → emitSignalLine-chars master fb s ++ₗ acc) [] sigs
emit-many-signalLineFmt-eq-foldr _ _ [] _ = refl
emit-many-signalLineFmt-eq-foldr master fb (s ∷ rest) (wfp All.∷ rest-wfps) =
  cong₂ _++ₗ_
        (emit-signalLineFmt-eq-DBCSignal master fb s wfp)
        (emit-many-signalLineFmt-eq-foldr master fb rest rest-wfps)


-- ============================================================================
-- LIST-LEVEL WF — per-signal preconditions for the SG_ block roundtrip
-- ============================================================================

-- Per-signal preconditions consumed by `signalLine-roundtrip` plus the
-- mux-bridge condition that lifts `WellFormedTextPresence` to the DSL
-- shape.  Bundled into a single record per signal so the All-list is
-- ergonomic at call sites.
record SignalLineWF (sig : DBCSignal) : Set where
  field
    name-stop      : SignalNameStop sig
    recv-head-stop : RecvHeadStop (DBCSignal.receivers sig)
    presence-wf    : WellFormedTextPresence (DBCSignal.presence sig)

-- Project the WellFormedTextPresence All-list out of an All SignalLineWF
-- list (used by `emit-many-signalLineFmt-eq-foldr`).
SignalLineWF→PresenceWF :
    ∀ (sigs : List DBCSignal)
  → All SignalLineWF sigs
  → All (λ s → WellFormedTextPresence (DBCSignal.presence s)) sigs
SignalLineWF→PresenceWF []       All.[]            = All.[]
SignalLineWF→PresenceWF (_ ∷ ss) (item All.∷ rest) =
  SignalLineWF.presence-wf item All.∷ SignalLineWF→PresenceWF ss rest


-- ============================================================================
-- TRANSLATION: SignalLineWF sig → NameStop / RecvHeadStop on expectedRaw
-- ============================================================================

-- `RawSignal.name (expectedRawOfDBC master fb sig) ≡ DBCSignal.name sig`
-- by direct projection through `expectedRaw`'s mkRawSignal.  Hence the
-- per-RawSignal `NameStop` collapses to the per-DBCSignal `SignalNameStop`.
sig-name-stop→name-stop :
    ∀ (master : Maybe (List Char)) (fb : ℕ) (sig : DBCSignal)
  → SignalNameStop sig
  → NameStop (expectedRawOfDBC master fb sig)
sig-name-stop→name-stop _ _ _ ns = ns

-- `RawSignal.receivers (expectedRawOfDBC master fb sig) ≡ DBCSignal.receivers sig`
-- by direct projection.  Hence the per-RawSignal `RecvHeadStop` collapses
-- to the per-DBCSignal version.
sig-recv-head-stop→recv-head-stop :
    ∀ (master : Maybe (List Char)) (fb : ℕ) (sig : DBCSignal)
  → RecvHeadStop (DBCSignal.receivers sig)
  → RecvHeadStop (RawSignal.receivers (expectedRawOfDBC master fb sig))
sig-recv-head-stop→recv-head-stop _ _ _ rhs = rhs


-- ============================================================================
-- INTER-SIGNAL recv-cont-stop — head of next signal's emit is ' '
-- ============================================================================

-- `' '` is non-isReceiverCont (not isIdentCont, not `,`), so when the
-- per-signal suffix is `emit (many signalLineFmt) (next ∷ ...) ++ outer`,
-- the head reduces to ' ' (signalLineFmt's leading withWSCanonOne emits
-- a single ' ' canonically) and `SuffixStops isReceiverCont` discharges
-- by `∷-stop refl`.
--
-- Used inside `build-emits-ok-many`'s ∷-cons step when there is at least
-- one more signal after the current one.
inter-signal-recv-stop :
    ∀ (master : Maybe (List Char)) (fb : ℕ) (next : DBCSignal)
      (rest : List DBCSignal) (outer-suffix : List Char)
  → SuffixStops isReceiverCont
      (emit (manyF signalLineFmt)
            (expectedRawOfDBC master fb next ∷
             map (expectedRawOfDBC master fb) rest)
       ++ₗ outer-suffix)
inter-signal-recv-stop master fb next rest outer-suffix =
  -- emit (many f) (x ∷ xs) = emit f x ++ emit (many f) xs.
  -- emit signalLineFmt rs starts with ' '.  Hence the head of the
  -- whole concat is ' ', and `isReceiverCont ' ' ≡ false`.
  ∷-stop refl


-- ============================================================================
-- 0 < length (emit signalLineFmt rs)
-- ============================================================================

-- signalLineFmt emits at least `' SG_ '` (5 chars) — closed-form length
-- bound discharged by `s≤s z≤n` after Agda reduces the iso/pair chain to
-- expose the leading ' '.  Pattern-match on `rs` to force the
-- `mkRawSignal` projection inside `ψSig` to compute.
emit-signalLineFmt-nonzero : ∀ (rs : RawSignal)
  → 0 < length (emit signalLineFmt rs)
emit-signalLineFmt-nonzero
    (mkRawSignal _ _ _ _ _ _ _ _ _ _ _ _) = s≤s z≤n


-- ============================================================================
-- BUILD `EmitsOKMany signalLineFmt expectedRaws suffix`
-- ============================================================================

-- Recursion on the signal list.  Empty: discharge via the outer
-- `ParseFailsAt` precondition.  Non-empty: build the per-signal
-- `EmitsOK signalLineFmt rs ...` via `build-emits-ok` from
-- `Format.SignalLine.Roundtrip`, the inter-signal recv-stop via
-- `inter-signal-recv-stop` (or fall through to the outer recv-stop
-- when this is the last signal), the nonzero-length witness, and
-- recurse on the tail.
build-emits-ok-many :
    ∀ (master : Maybe (List Char)) (fb : ℕ)
      (sigs : List DBCSignal) (outer-suffix : List Char)
  → All SignalLineWF sigs
  → ParseFailsAt signalLineFmt outer-suffix
  → SuffixStops isReceiverCont outer-suffix
  → EmitsOKMany signalLineFmt
                (map (expectedRawOfDBC master fb) sigs)
                outer-suffix
build-emits-ok-many _ _ [] outer-suffix _ tf _ =
  []-fails tf
build-emits-ok-many master fb (s ∷ rest) outer-suffix
                    (item All.∷ rest-items) tf outer-recv-stop =
  ∷-cons
    (build-emits-ok
       (expectedRawOfDBC master fb s)
       (emit (manyF signalLineFmt) (map (expectedRawOfDBC master fb) rest)
        ++ₗ outer-suffix)
       (sig-name-stop→name-stop master fb s (SignalLineWF.name-stop item))
       (sig-recv-head-stop→recv-head-stop master fb s
          (SignalLineWF.recv-head-stop item))
       (recv-stop-for-this-signal rest))
    (emit-signalLineFmt-nonzero (expectedRawOfDBC master fb s))
    (build-emits-ok-many master fb rest outer-suffix rest-items tf
                         outer-recv-stop)
  where
    -- For non-empty rest, the suffix to this signal is `' ' ∷ ...`
    -- (head of next signal's emit), so recv-stop is `∷-stop refl`.
    -- For empty rest, fall through to the outer recv-stop.
    recv-stop-for-this-signal : (xs : List DBCSignal)
      → SuffixStops isReceiverCont
          (emit (manyF signalLineFmt)
                (map (expectedRawOfDBC master fb) xs)
           ++ₗ outer-suffix)
    recv-stop-for-this-signal []          = outer-recv-stop
    recv-stop-for-this-signal (next ∷ rs) =
      inter-signal-recv-stop master fb next rs outer-suffix


-- ============================================================================
-- MAIN THEOREM — `parse (many signalLineFmt)` over a foldr-shape SG_ block
-- ============================================================================

-- Input shape: `foldr (λ s acc → emitSignalLine-chars master fb s ++ acc)
-- [] sigs ++ outer-suffix` (the SG_ block as emitted by emitMessage-chars).
-- Output: parses the list of expected RawSignals + advances position.
--
-- Composition: bridge the input shape to `emit (many signalLineFmt)
-- (map expectedRawOfDBC sigs) ++ outer-suffix` via
-- `emit-many-signalLineFmt-eq-foldr`, then apply the framework's universal
-- `roundtrip (many signalLineFmt)` backed by `build-emits-ok-many`.
-- The output position is bridged back through the same equation.
parseSignalLines-roundtrip :
    ∀ (pos : Position) (master : Maybe (List Char)) (fb : ℕ)
      (sigs : List DBCSignal) (outer-suffix : List Char)
  → All SignalLineWF sigs
  → ParseFailsAt signalLineFmt outer-suffix
  → SuffixStops isReceiverCont outer-suffix
  → parse (manyF signalLineFmt) pos
       (foldr (λ s acc → emitSignalLine-chars master fb s ++ₗ acc) []
              sigs
        ++ₗ outer-suffix)
    ≡ just (mkResult (map (expectedRawOfDBC master fb) sigs)
             (advancePositions pos
               (foldr (λ s acc → emitSignalLine-chars master fb s ++ₗ acc)
                      [] sigs))
             outer-suffix)
parseSignalLines-roundtrip pos master fb sigs outer-suffix
                           items tf outer-recv-stop =
  trans
    (cong (λ inp → parse (manyF signalLineFmt) pos (inp ++ₗ outer-suffix))
          (sym bridge))
    (trans
      (roundtrip (manyF signalLineFmt) pos
                 (map (expectedRawOfDBC master fb) sigs)
                 outer-suffix
                 (build-emits-ok-many master fb sigs outer-suffix
                                      items tf outer-recv-stop))
      (cong (λ s → just (mkResult (map (expectedRawOfDBC master fb) sigs)
                                   (advancePositions pos s)
                                   outer-suffix))
            bridge))
  where
    bridge : emit (manyF signalLineFmt)
                  (map (expectedRawOfDBC master fb) sigs)
             ≡ foldr (λ s acc → emitSignalLine-chars master fb s ++ₗ acc)
                     [] sigs
    bridge = emit-many-signalLineFmt-eq-foldr master fb sigs
               (SignalLineWF→PresenceWF sigs items)
