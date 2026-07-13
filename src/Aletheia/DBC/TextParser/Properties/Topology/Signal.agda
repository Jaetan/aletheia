-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- `parseSignalLine-roundtrip-{NotMux,IsMux,SelBy}` — per-MuxMarker-shape
-- roundtrip lemmas for the SG_ DBC signal line.
--
-- Previously, each dispatcher was a 700+ LOC step-by-step bind-chain
-- proof through `parseSignalTail-roundtrip` (1140 LOC) over 28 parser
-- primitives; total ~1873 LOC across the three dispatchers + shared tail.
--
-- Now `parseSignalLine = parse signalLineFmt` (single DSL form), and
-- the dispatchers reduce to:
--
--   1. A bridge `emit-signalLineFmt-eq-emitSignalLine-chars` proving
--      the DSL emit on `expectedRaw mux sig fb` equals the existing
--      `emitSignalLine-chars master fb sig` (given the dispatcher's
--      `emitMuxMarker-chars … ≡ <mux-shape>` precondition).
--   2. A slim wrapper per `MuxMarker` that lifts the bridge equation
--      through `parse signalLineFmt` and applies the universal
--      `signalLine-roundtrip` (from `Format.SignalLine.Roundtrip`).
--
-- Receiver-side equivalence: `Properties.Topology.Receivers
-- .emit-canonicalReceiversFmt-eq-emitReceivers`.
-- Universal receivers roundtrip: `Format.Receivers.Roundtrip
-- .canonicalReceivers-roundtrip`.
--
-- Dispatcher signature change: the former `novecxxx : All ¬...vectorXXX
-- (.list)` precondition is dropped — `DBCSignal.receivers : CanonicalReceivers`
-- (after the retype) already carries `T (isCanonicalReceiversᵇ list)`,
-- which subsumes the singleton-Vector__XXX prohibition.  No external
-- callers (the composers are still pending).
module Aletheia.DBC.TextParser.Properties.Topology.Signal where

open import Data.Bool using (Bool; true; false; T; _∧_)
open import Data.Char using (Char)
open import Data.List using (List; []; _∷_) renaming (_++_ to _++ₗ_)
open import Data.List.Properties renaming (++-assoc to ++ₗ-assoc)
open import Data.Maybe using (Maybe; just)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₂)
open import Data.String using (toList)
open import Data.Empty using (⊥-elim)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong)

open import Aletheia.Parser.Combinators using
  (Position; mkResult; advancePositions)
open import Aletheia.DBC.Identifier using (Identifier; mkIdent)
open import Aletheia.DBC.CanonicalReceivers using
  (CanonicalReceivers; mkCanonical)
open import Aletheia.CAN.Endianness using
  (ByteOrder; LittleEndian; BigEndian; unconvertStartBit)
open import Aletheia.CAN.Signal using (SignalDef)

open import Aletheia.DBC.TextParser.Lexer using (isHSpace)
open import Aletheia.DBC.TextParser.Topology using (parseSignalLine)
open import Aletheia.DBC.TextParser.Topology.Foundations using
  (RawSignal; mkRawSignal;
   MuxMarker; NotMux; IsMux; SelBy)
open import Aletheia.DBC.TextFormatter.Emitter using
  (showNat-chars; showDecRat-dec-chars)
open import Aletheia.DBC.TextFormatter.Topology using
  (emitSignalLine-chars; emitMuxMarker-chars; emitReceivers-chars;
   emitByteOrderDigit-chars; emitSignFlag-chars)
open import Aletheia.DBC.Types using (DBCSignal)

open import Aletheia.DBC.TextParser.DecRatParse.Properties using
  (SuffixStops; ∷-stop)
open import Aletheia.DBC.TextParser.Format using
  (emit)
open import Aletheia.DBC.TextParser.Format.SignalLine using
  (signalLineFmt; muxMarkerFmt; byteOrderFmt; signFlagFmt)
open import Aletheia.DBC.TextParser.Format.SignalLine.Roundtrip using
  (NameStop; RecvHeadStop; signalLine-roundtrip)
open import Aletheia.DBC.TextParser.Properties.Topology.Receivers using
  (isReceiverCont; emit-canonicalReceiversFmt-eq-emitReceivers)
open import Aletheia.DBC.TextParser.Properties.CharClassDisjoint using
  (isIdentStart→¬isHSpace)


-- ============================================================================
-- SIGNAL NAME STOP — per-signal precondition
-- ============================================================================

-- The signal's identifier name decomposes as `c ∷ cs` with
-- `isHSpace c ≡ false`; required by the DSL header chunk's `withWS`
-- after `withPrefix "SG_"`.  Discharged universally from `Identifier`
-- validity by `Properties.WellFormedFromValidity.signalNameStop` (via the
-- already-proven `isIdentStart→¬isHSpace` bridge in
-- `Properties.CharClassDisjoint`); still taken as a precondition here because
-- the threading through `MessageWF` is not yet removed (see DEFERRED_ITEMS.md
-- E.1/E.2).  Identical in shape to
-- `Format.SignalLine.Roundtrip.NameStop` modulo
-- `RawSignal.name (expectedRaw _ sig _) ≡ DBCSignal.name sig` (record-η).
SignalNameStop : DBCSignal → Set
SignalNameStop sig =
  Σ[ c ∈ Char ] Σ[ cs ∈ List Char ]
    (Identifier.name (DBCSignal.name sig) ≡ c ∷ cs) × (isHSpace c ≡ false)


-- ============================================================================
-- EXPECTED RawSignal — per-MuxMarker shape
-- ============================================================================

-- The `RawSignal` returned by `parseSignalLine` on the formatter's emit,
-- parameterized on the resolved `MuxMarker` (per dispatcher).  Computed
-- from `sig` + `frameBytes` via direct field projection except:
--
--   * `RawSignal.muxMarker` is supplied by the dispatcher.
--   * `RawSignal.startBit` is the formatter-emitted RAW value
--     `unconvertStartBit fb bo (SignalDef.startBit def) (SignalDef.bitLength def)`,
--     not the post-`% max-physical-bits` clamped value.  The `% / convert`
--     roundtrip is handled by a later composition step.
--   * `RawSignal.receivers ≡ DBCSignal.receivers sig` directly
--     (both fields are `CanonicalReceivers` — no projection needed).
expectedRaw : MuxMarker → DBCSignal → ℕ → RawSignal
expectedRaw mux sig frameBytes = mkRawSignal
    (DBCSignal.name sig)
    mux
    (unconvertStartBit frameBytes
        (DBCSignal.byteOrder sig)
        (SignalDef.startBit (DBCSignal.signalDef sig))
        (SignalDef.bitLength (DBCSignal.signalDef sig)))
    (SignalDef.bitLength (DBCSignal.signalDef sig))
    (DBCSignal.byteOrder sig)
    (SignalDef.isSigned (DBCSignal.signalDef sig))
    (SignalDef.factor (DBCSignal.signalDef sig))
    (SignalDef.offset (DBCSignal.signalDef sig))
    (SignalDef.minimum (DBCSignal.signalDef sig))
    (SignalDef.maximum (DBCSignal.signalDef sig))
    (DBCSignal.unit sig)
    (DBCSignal.receivers sig)


-- ============================================================================
-- DSL ↔ EXISTING FORMATTER BRIDGES (byte-order + sign-flag sub-pieces)
-- ============================================================================

private
  -- The DSL emit on `byteOrderFmt`/`signFlagFmt` reduces to `emit alt
  -- (ψ b)` until `b` is concrete; case-split closes both with `refl`.
  emit-byteOrderFmt-eq : ∀ (b : ByteOrder)
    → emit byteOrderFmt b ≡ emitByteOrderDigit-chars b
  emit-byteOrderFmt-eq BigEndian    = refl
  emit-byteOrderFmt-eq LittleEndian = refl

  emit-signFlagFmt-eq : ∀ (b : Bool)
    → emit signFlagFmt b ≡ emitSignFlag-chars b
  emit-signFlagFmt-eq false = refl
  emit-signFlagFmt-eq true  = refl

  -- Flatten a 4-piece chunk `(A ++ s1 ∷ B ++ s2 ∷ C ++ D) ++ rest` into
  -- the formatter's `A ++ s1 ∷ B ++ s2 ∷ C ++ D ++ rest`.  Used at the
  -- size-chunk seam (3 ++-assoc applications).
  flatten-4 : ∀ (A B C D rest : List Char) (s1 s2 : Char)
    → (A ++ₗ s1 ∷ B ++ₗ s2 ∷ C ++ₗ D) ++ₗ rest
      ≡ A ++ₗ s1 ∷ B ++ₗ s2 ∷ C ++ₗ D ++ₗ rest
  flatten-4 A B C D rest s1 s2 =
    trans (++ₗ-assoc A (s1 ∷ B ++ₗ s2 ∷ C ++ₗ D) rest)
      (cong (A ++ₗ_)
        (cong (s1 ∷_)
          (trans (++ₗ-assoc B (s2 ∷ C ++ₗ D) rest)
            (cong (B ++ₗ_)
              (cong (s2 ∷_)
                (++ₗ-assoc C D rest))))))

  -- Flatten a 2-piece chunk `(A ++ s ∷ B ++ tail) ++ rest`.  Used at the
  -- scaling/range chunk seams where the inner ends with `_ ∷ []`.
  flatten-2 : ∀ (A B rest : List Char) (s : Char) (tail : List Char)
    → (A ++ₗ s ∷ B ++ₗ tail) ++ₗ rest
      ≡ A ++ₗ s ∷ B ++ₗ tail ++ₗ rest
  flatten-2 A B rest s tail =
    trans (++ₗ-assoc A (s ∷ B ++ₗ tail) rest)
      (cong (A ++ₗ_)
        (cong (s ∷_)
          (++ₗ-assoc B tail rest)))

  -- Flatten the 3 chunk seams (size + scaling + range) in one go.
  -- LHS = chunk-grouped DSL form; RHS = flat formatter form.  No
  -- `pre`-parameter: caller wraps via `cong (λ x → PREFIX ++ x)`.
  inner-bridge :
    ∀ (sb bl bo sgn fac off mn mx unit recv : List Char)
    → (sb ++ₗ '|' ∷ bl ++ₗ '@' ∷ bo ++ₗ sgn) ++ₗ
        ' ' ∷ '(' ∷ (fac ++ₗ ',' ∷ off ++ₗ ')' ∷ []) ++ₗ
        ' ' ∷ '[' ∷ (mn ++ₗ '|' ∷ mx ++ₗ ']' ∷ []) ++ₗ
        ' ' ∷ '"' ∷ unit ++ₗ ' ' ∷ recv ++ₗ '\n' ∷ []
      ≡ sb ++ₗ '|' ∷ bl ++ₗ '@' ∷ bo ++ₗ sgn ++ₗ
        ' ' ∷ '(' ∷ fac ++ₗ ',' ∷ off ++ₗ ')' ∷
        ' ' ∷ '[' ∷ mn ++ₗ '|' ∷ mx ++ₗ ']' ∷
        ' ' ∷ '"' ∷ unit ++ₗ ' ' ∷ recv ++ₗ '\n' ∷ []
  inner-bridge sb bl bo sgn fac off mn mx unit recv =
    trans (flatten-4 sb bl bo sgn _ '|' '@')
      (cong (λ y → sb ++ₗ '|' ∷ bl ++ₗ '@' ∷ bo ++ₗ sgn ++ₗ ' ' ∷ '(' ∷ y)
        (trans (flatten-2 fac off _ ',' (')' ∷ []))
          (cong (λ z → fac ++ₗ ',' ∷ off ++ₗ ')' ∷ ' ' ∷ '[' ∷ z)
            (flatten-2 mn mx _ '|' (']' ∷ [])))))


-- ============================================================================
-- THE MAIN BRIDGE: DSL emit ≡ existing emitSignalLine-chars
-- ============================================================================

-- Given the dispatcher's mux-eq precondition + the receiver-side bridge
-- + the byte-order/sign-flag sub-bridges, the DSL emit on
-- `expectedRaw mux sig fb` collapses to `emitSignalLine-chars master fb
-- sig`.  All other chunks (literal text, decimal/decRat shows, etc.)
-- align by definitional reduction once `iso`/`pair`/`withPrefix`/
-- `withWSCanonOne` unfold against the concrete format constructors.
emit-signalLineFmt-eq-emitSignalLine-chars :
    ∀ (mux : MuxMarker) (master : Maybe (List Char))
      (fb : ℕ) (sig : DBCSignal)
  → emit muxMarkerFmt mux
    ≡ emitMuxMarker-chars master (Identifier.name (DBCSignal.name sig))
                                  (DBCSignal.presence sig)
  → emit signalLineFmt (expectedRaw mux sig fb)
    ≡ emitSignalLine-chars master fb sig
emit-signalLineFmt-eq-emitSignalLine-chars mux master fb sig mux-eq
  rewrite mux-eq
        | emit-canonicalReceiversFmt-eq-emitReceivers (DBCSignal.receivers sig)
        | emit-byteOrderFmt-eq (DBCSignal.byteOrder sig)
        | emit-signFlagFmt-eq (SignalDef.isSigned (DBCSignal.signalDef sig))
        = let def  = DBCSignal.signalDef sig
              bo   = DBCSignal.byteOrder sig
              sb-ℕ = unconvertStartBit fb bo (SignalDef.startBit def)
                                          (SignalDef.bitLength def)
              sb-c   = showNat-chars sb-ℕ
              bl-c   = showNat-chars (SignalDef.bitLength def)
              bo-c   = emitByteOrderDigit-chars bo
              sgn-c  = emitSignFlag-chars (SignalDef.isSigned def)
              fac-c  = showDecRat-dec-chars (SignalDef.factor def)
              off-c  = showDecRat-dec-chars (SignalDef.offset def)
              mn-c   = showDecRat-dec-chars (SignalDef.minimum def)
              mx-c   = showDecRat-dec-chars (SignalDef.maximum def)
          in cong (λ x → ' ' ∷ 'S' ∷ 'G' ∷ '_' ∷ ' ' ∷
                          Identifier.name (DBCSignal.name sig) ++ₗ
                          emitMuxMarker-chars master
                            (Identifier.name (DBCSignal.name sig))
                            (DBCSignal.presence sig) ++ₗ
                          ' ' ∷ ':' ∷ ' ' ∷ x)
                  (inner-bridge sb-c bl-c bo-c sgn-c fac-c off-c
                                mn-c mx-c _ _)


-- ============================================================================
-- PRECONDITION TRANSLATION HELPERS
-- ============================================================================

private
  -- `SignalNameStop sig → NameStop (expectedRaw mux sig fb)`.  Identity
  -- modulo `RawSignal.name (expectedRaw _ sig _) ≡ DBCSignal.name sig`
  -- (record projection on `mkRawSignal _` reduces to the first arg).
  sig-name-stop→name-stop : ∀ (mux : MuxMarker) (fb : ℕ) (sig : DBCSignal)
    → SignalNameStop sig
    → NameStop (expectedRaw mux sig fb)
  sig-name-stop→name-stop _ _ _ ns = ns

  -- Build `RecvHeadStop cr` from the dispatcher's existing
  -- `SuffixStops isHSpace (emitReceivers-chars (.list cr) ++ '\n' ∷ suffix)`.
  -- Three cases mirror the canonical AST shapes (the `bwd` of
  -- `canonicalReceiversFmt`):
  --
  --   * `mkCanonical [] _`        — emit ≡ "Vector__XXX"; head 'V' is
  --                                  closed-form non-hspace.
  --   * `mkCanonical (mkIdent [] vp ∷ _) _`   — `vp : T (validIdentifierᵇ
  --                                  []) = T false = ⊥`; ⊥-elim closes.
  --   * `mkCanonical (mkIdent (c ∷ cs) _ ∷ rest) _` — emit starts with
  --                                  `c`; SuffixStops gives `isHSpace c
  --                                  ≡ false` (after the bridge).
  build-RecvHeadStop : ∀ (cr : CanonicalReceivers) (suffix : List Char)
    → SuffixStops isHSpace
        (emitReceivers-chars (CanonicalReceivers.list cr) ++ₗ '\n' ∷ suffix)
    → RecvHeadStop cr
  build-RecvHeadStop (mkCanonical [] _) _ _ = 'V' , _ , refl , refl
  build-RecvHeadStop (mkCanonical (mkIdent [] vp ∷ _) _) _ _ = ⊥-elim vp
  build-RecvHeadStop
      (mkCanonical (mkIdent (c ∷ cs) _ ∷ []) _) _ (∷-stop hsp) =
    c , (cs ++ₗ []) , refl , hsp
  build-RecvHeadStop
      (mkCanonical (mkIdent (c ∷ cs) _ ∷ s ∷ rest) _) _ (∷-stop hsp) =
    c , _ , refl , hsp


-- ============================================================================
-- UNIVERSAL RECEIVER-HEAD STOP  (no SuffixStops premise — importable)
-- ============================================================================
--
-- `RecvHeadStop cr` for EVERY canonical receiver list.  Unlike the private
-- `build-RecvHeadStop`, this takes NO parser `SuffixStops` premise: the
-- head-non-hspace fact comes from the receiver identifier's OWN validity witness
-- (`isIdentStart→¬isHSpace c (T-∧₁ v)`, the identNameStop move —
-- WellFormedFromValidity.agda:72-83, CharClassDisjoint.agda:76).  This makes the
-- `SignalLineWF.recv-head-stop` field free for the E.2 route (b) checker (§3), so
-- the soundness tree can discharge it with no per-DBC decision.  Four clauses
-- mirror `build-RecvHeadStop` exactly; the emit-equation `refl`s and the `cs`
-- component are premise-independent (they reduce from the AST alone).

private
  -- First-conjunct projection of a `T`-valued conjunction (local mirror of the
  -- private helper in WellFormedFromValidity.agda; kept local to avoid a cycle).
  T-∧₁ : ∀ {a b : Bool} → T (a ∧ b) → T a
  T-∧₁ {true} {true} _ = tt

recvHeadStop : ∀ (cr : CanonicalReceivers) → RecvHeadStop cr
recvHeadStop (mkCanonical [] _)                             = 'V' , _ , refl , refl
recvHeadStop (mkCanonical (mkIdent [] vp ∷ _) _)            = ⊥-elim vp
recvHeadStop (mkCanonical (mkIdent (c ∷ cs) v ∷ []) _)      =
  c , (cs ++ₗ []) , refl , isIdentStart→¬isHSpace c (T-∧₁ v)
recvHeadStop (mkCanonical (mkIdent (c ∷ cs) v ∷ s ∷ rest) _) =
  c , _ , refl , isIdentStart→¬isHSpace c (T-∧₁ v)


-- ============================================================================
-- THE THREE DISPATCHERS — per-MuxMarker slim wrappers
-- ============================================================================
--
-- Body shape (all three dispatchers):
--   1. Lift the bridge: `emit signalLineFmt (expectedRaw mux sig fb) ≡
--      emitSignalLine-chars master fb sig`.
--   2. `cong (parseSignalLine pos)` over the bridge applied to `_++ suffix`.
--   3. Apply universal `signalLine-roundtrip` with translated preconditions.
-- The trans chain reads: parser ∘ formatter ≡ parser ∘ DSL-emit ≡ just …

parseSignalLine-roundtrip-NotMux :
    ∀ (pos : Position) (master : Maybe (List Char)) (fb : ℕ)
      (sig : DBCSignal) (suffix : List Char)
  → emitMuxMarker-chars master (Identifier.name (DBCSignal.name sig))
                                (DBCSignal.presence sig)
    ≡ []
  → SignalNameStop sig
  → SuffixStops isHSpace
      (emitReceivers-chars (CanonicalReceivers.list (DBCSignal.receivers sig))
        ++ₗ '\n' ∷ suffix)
  → SuffixStops isReceiverCont suffix
  → proj₂ (parseSignalLine pos
      (emitSignalLine-chars master fb sig ++ₗ suffix))
    ≡ just (mkResult (expectedRaw NotMux sig fb)
             (advancePositions pos (emitSignalLine-chars master fb sig))
             suffix)
parseSignalLine-roundtrip-NotMux pos master fb sig suffix
                                    mux-eq name-stop hs-stop recv-cont-stop =
  trans
    (cong (λ s → proj₂ (parseSignalLine pos (s ++ₗ suffix))) (sym bridge))
    (trans
      (signalLine-roundtrip pos rs suffix
         (sig-name-stop→name-stop NotMux fb sig name-stop)
         (build-RecvHeadStop (DBCSignal.receivers sig) suffix hs-stop)
         recv-cont-stop)
      (cong (λ s → just (mkResult rs (advancePositions pos s) suffix)) bridge))
  where
    rs : RawSignal
    rs = expectedRaw NotMux sig fb
    bridge : emit signalLineFmt rs ≡ emitSignalLine-chars master fb sig
    bridge = emit-signalLineFmt-eq-emitSignalLine-chars
              NotMux master fb sig (sym mux-eq)

parseSignalLine-roundtrip-IsMux :
    ∀ (pos : Position) (master : Maybe (List Char)) (fb : ℕ)
      (sig : DBCSignal) (suffix : List Char)
  → emitMuxMarker-chars master (Identifier.name (DBCSignal.name sig))
                                (DBCSignal.presence sig)
    ≡ toList " M"
  → SignalNameStop sig
  → SuffixStops isHSpace
      (emitReceivers-chars (CanonicalReceivers.list (DBCSignal.receivers sig))
        ++ₗ '\n' ∷ suffix)
  → SuffixStops isReceiverCont suffix
  → proj₂ (parseSignalLine pos
      (emitSignalLine-chars master fb sig ++ₗ suffix))
    ≡ just (mkResult (expectedRaw IsMux sig fb)
             (advancePositions pos (emitSignalLine-chars master fb sig))
             suffix)
parseSignalLine-roundtrip-IsMux pos master fb sig suffix
                                   mux-eq name-stop hs-stop recv-cont-stop =
  trans
    (cong (λ s → proj₂ (parseSignalLine pos (s ++ₗ suffix))) (sym bridge))
    (trans
      (signalLine-roundtrip pos rs suffix
         (sig-name-stop→name-stop IsMux fb sig name-stop)
         (build-RecvHeadStop (DBCSignal.receivers sig) suffix hs-stop)
         recv-cont-stop)
      (cong (λ s → just (mkResult rs (advancePositions pos s) suffix)) bridge))
  where
    rs : RawSignal
    rs = expectedRaw IsMux sig fb
    bridge : emit signalLineFmt rs ≡ emitSignalLine-chars master fb sig
    bridge = emit-signalLineFmt-eq-emitSignalLine-chars
              IsMux master fb sig (sym mux-eq)

parseSignalLine-roundtrip-SelBy :
    ∀ (pos : Position) (master : Maybe (List Char)) (fb : ℕ)
      (sig : DBCSignal) (v : ℕ) (suffix : List Char)
  → emitMuxMarker-chars master (Identifier.name (DBCSignal.name sig))
                                (DBCSignal.presence sig)
    ≡ toList " m" ++ₗ showNat-chars v
    -- (= `toList " m" ++ showℕ-dec-chars v` since
    -- `showℕ-dec-chars = showNat-chars`; the formatter writes the
    -- former, this lemma exposes the latter to match the bridge's
    -- `emit nat v = showNat-chars v` reduction without an extra step.)
  → SignalNameStop sig
  → SuffixStops isHSpace
      (emitReceivers-chars (CanonicalReceivers.list (DBCSignal.receivers sig))
        ++ₗ '\n' ∷ suffix)
  → SuffixStops isReceiverCont suffix
  → proj₂ (parseSignalLine pos
      (emitSignalLine-chars master fb sig ++ₗ suffix))
    ≡ just (mkResult (expectedRaw (SelBy v) sig fb)
             (advancePositions pos (emitSignalLine-chars master fb sig))
             suffix)
parseSignalLine-roundtrip-SelBy pos master fb sig v suffix
                                   mux-eq name-stop hs-stop recv-cont-stop =
  trans
    (cong (λ s → proj₂ (parseSignalLine pos (s ++ₗ suffix))) (sym bridge))
    (trans
      (signalLine-roundtrip pos rs suffix
         (sig-name-stop→name-stop (SelBy v) fb sig name-stop)
         (build-RecvHeadStop (DBCSignal.receivers sig) suffix hs-stop)
         recv-cont-stop)
      (cong (λ s → just (mkResult rs (advancePositions pos s) suffix)) bridge))
  where
    rs : RawSignal
    rs = expectedRaw (SelBy v) sig fb
    bridge : emit signalLineFmt rs ≡ emitSignalLine-chars master fb sig
    bridge = emit-signalLineFmt-eq-emitSignalLine-chars
              (SelBy v) master fb sig (sym mux-eq)
