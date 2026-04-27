{-# OPTIONS --safe --without-K #-}

-- `parseSignalLine-roundtrip-{NotMux,IsMux,SelBy}` — per-MuxMarker-shape
-- roundtrip lemmas for the SG_ DBC signal line (B.3.d Layer 3 Commit 3d.3).
--
-- Bind chain (33 steps; matches `Aletheia.DBC.TextParser.Topology.parseSignalLine`):
--
--   parseWSOpt *> string "SG_" *> parseWS *>
--   parseIdentifier >>= λ name →
--   parseMuxMarker  >>= λ mux  →
--   parseWSOpt *> char ':' *> parseWSOpt *>
--   parseNatural >>= λ sb →
--   char '|' *>
--   parseNatural >>= λ bl →
--   char '@' *>
--   parseByteOrderDigit >>= λ bo →
--   parseSignFlag       >>= λ isSigned →
--   parseWSOpt *> char '(' *>
--   parseDecRat >>= λ factor →
--   char ',' *>
--   parseDecRat >>= λ offset →
--   char ')' *> parseWSOpt *> char '[' *>
--   parseDecRat >>= λ minimum →
--   char '|' *>
--   parseDecRat >>= λ maximum →
--   char ']' *> parseWSOpt *>
--   parseStringLit >>= λ unit →
--   parseWSOpt *>
--   parseReceiverList >>= λ receivers →
--   parseWSOpt *> parseNewline *>
--   pure (mkRawSignal name mux sb bl bo isSigned
--                     factor offset minimum maximum unit
--                     (stripVectorPlaceholder receivers))
--
-- The mux dispatcher is the only branch with three dispatcher cases
-- (NotMux / IsMux / SelBy v); BothMux is dead-under-formatter (see G-A6 in
-- `WellFormedText.agda`'s module header).  All three dispatchers converge
-- on `" : ..."` post-mux input — the tail proof (steps 6-33) is shared.
--
-- The receiver-list segment composes 3d.2's
-- `parseReceiverList∘strip-roundtrip`, returning an existential parsedRs
-- together with `stripVectorPlaceholder parsedRs ≡ DBCSignal.receivers sig`.
module Aletheia.DBC.TextParser.Properties.Topology.Signal where

open import Data.Bool using (Bool; true; false; T; not; _∨_; _∧_)
open import Data.Bool.Properties using (T?)
open import Data.Char using (Char)
open import Data.Char.Base using (_≈ᵇ_; isDigit)
open import Data.List using (List; []; _∷_; map; length; foldr) renaming (_++_ to _++ₗ_)
open import Data.List.NonEmpty as List⁺ using (List⁺; _∷_)
open import Data.List.Properties using (length-++) renaming (++-assoc to ++ₗ-assoc)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; s≤s; z≤n)
open import Data.Product using (Σ; Σ-syntax; ∃; ∃-syntax; _×_; _,_; proj₁; proj₂)
open import Data.String as String using (String; toList) renaming (_≟_ to _≟ₛ_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary using (¬_; yes; no; ⌊_⌋)

open import Aletheia.Parser.Combinators using
  (Parser; Position; ParseResult; mkResult; advancePosition; advancePositions;
   pure; _>>=_; _*>_; _<|>_; string; char; satisfy; many; manyHelper)
open import Aletheia.DBC.Identifier using
  (Identifier; mkIdent; isIdentStart; isIdentCont; validIdentifierᵇ)
open import Aletheia.DBC.CanonicalReceivers using (CanonicalReceivers)
open import Aletheia.DBC.DecRat using (DecRat)
open import Aletheia.CAN.Endianness using
  (ByteOrder; LittleEndian; BigEndian; unconvertStartBit)
open import Aletheia.CAN.Signal using (SignalDef)

open import Aletheia.DBC.TextParser.Lexer using
  (parseIdentifier; parseStringLit; parseNatural;
   parseWS; parseWSOpt; parseNewline; isHSpace)
open import Aletheia.DBC.TextParser.DecRatParse using (parseDecRat)
open import Aletheia.DBC.TextParser.Topology using
  (parseSignalLine; parseMuxMarker;
   parseByteOrderDigit; parseSignFlag;
   RawSignal; mkRawSignal; stripVectorPlaceholder;
   MuxMarker; NotMux; IsMux; SelBy; BothMux)
open import Aletheia.DBC.TextFormatter.Topology using
  (emitSignalLine-chars; emitMuxMarker-chars; emitReceivers-chars;
   emitByteOrderDigit-chars; emitSignFlag-chars)
open import Aletheia.DBC.TextFormatter.Emitter using
  (showℕ-dec-chars; showDecRat-dec-chars; quoteStringLit-chars)
open import Aletheia.DBC.Types using
  (DBCSignal; SignalPresence; Always; When)

open import Aletheia.DBC.TextParser.DecRatParse.Properties using
  (SuffixStops; []-stop; ∷-stop; bind-just-step;
   manyHelper-satisfy-exhaust-many; advancePositions-++;
   parseNatural-showNat-chars; parseDecRat-roundtrip-suffix)
open import Aletheia.DBC.TextParser.Properties.Primitives using
  (string-success; char-matches; parseWS-one-space;
   parseIdentifier-roundtrip;
   parseByteOrderDigit-roundtrip; parseSignFlag-roundtrip;
   parseStringLit-roundtrip;
   parseMuxMarker-IsMux-roundtrip; parseMuxMarker-NotMux-roundtrip;
   parseMuxMarker-SelBy-roundtrip; parseMuxMarker-left-branch)
open import Aletheia.DBC.TextParser.Properties.Preamble.Newline using
  (isNewlineStart; parseNewline-match-LF)
open import Aletheia.DBC.TextParser.Properties.Topology.Receivers using
  (isReceiverCont; parseReceiverList∘strip-roundtrip)
open import Aletheia.DBC.Formatter.WellFormedText using
  (WellFormedTextSignal; WellFormedTextPresence;
   wftp-always; wftp-when-single; NoVectorXXXReceiver)


-- ============================================================================
-- IDENTIFIER NAME STOP — per-signal precondition
-- ============================================================================

-- The signal's identifier name decomposes as `c ∷ cs` with
-- `isHSpace c ≡ false`; required by `parseWS *> parseIdentifier` (the
-- single-space separator plus `validIdentifierᵇ`-driven identifier
-- consumption).  Owed by Layer 4 via the `isIdentStart→¬isHSpace` bridge
-- lemma (deferred per `project_b3d_layer4_owed_lemmas.md`).
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
--     roundtrip is a 3d.5 / Layer 4 concern.
--   * `RawSignal.receivers` ≡ `DBCSignal.receivers sig` via 3d.2's
--     `parseReceiverList∘strip-roundtrip` discharging the parsed-back list
--     through `stripVectorPlaceholder`.
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
    (CanonicalReceivers.list (DBCSignal.receivers sig))


-- ============================================================================
-- INPUT SHAPE — emitSignalLine-chars decomposition
-- ============================================================================

-- The signal line emit is a flat concat of fixed separators, value
-- emitters, and the mux marker insert.  We decompose it into named pieces
-- so each step's input/output rest is visible at the proof site.

private
  -- Convenience: project all the per-signal show-chars in one place.
  module _ (sig : DBCSignal) (frameBytes : ℕ) where
    nameChars : List Char
    nameChars = Identifier.name (DBCSignal.name sig)

    sbChars : List Char
    sbChars = showℕ-dec-chars
                (unconvertStartBit frameBytes
                  (DBCSignal.byteOrder sig)
                  (SignalDef.startBit (DBCSignal.signalDef sig))
                  (SignalDef.bitLength (DBCSignal.signalDef sig)))

    blChars : List Char
    blChars = showℕ-dec-chars (SignalDef.bitLength (DBCSignal.signalDef sig))

    boChars : List Char
    boChars = emitByteOrderDigit-chars (DBCSignal.byteOrder sig)

    signChars : List Char
    signChars = emitSignFlag-chars (SignalDef.isSigned (DBCSignal.signalDef sig))

    factorChars : List Char
    factorChars = showDecRat-dec-chars (SignalDef.factor (DBCSignal.signalDef sig))

    offsetChars : List Char
    offsetChars = showDecRat-dec-chars (SignalDef.offset (DBCSignal.signalDef sig))

    minChars : List Char
    minChars = showDecRat-dec-chars (SignalDef.minimum (DBCSignal.signalDef sig))

    maxChars : List Char
    maxChars = showDecRat-dec-chars (SignalDef.maximum (DBCSignal.signalDef sig))

    unitChars : List Char
    unitChars = quoteStringLit-chars (DBCSignal.unit sig)

    recvChars : List Char
    recvChars = emitReceivers-chars (CanonicalReceivers.list (DBCSignal.receivers sig))

-- The full body string from `" : "` through `'\n'`, parameterized by
-- `frameBytes`, `sig`, and the post-receiver suffix.  Pulling the head
-- (` SG_ <name><mux>`) and the tail (everything after) apart is the
-- main reassociation we use.
private
  tailBody-chars : (frameBytes : ℕ) (sig : DBCSignal) → List Char
  tailBody-chars frameBytes sig =
    toList " : "       ++ₗ sbChars sig frameBytes
      ++ₗ '|'  ∷ blChars sig frameBytes
      ++ₗ '@'  ∷ boChars sig frameBytes
      ++ₗ           signChars sig frameBytes
      ++ₗ toList " (" ++ₗ factorChars sig frameBytes
      ++ₗ ','  ∷ offsetChars sig frameBytes
      ++ₗ toList ") "
      ++ₗ '['  ∷ minChars sig frameBytes
      ++ₗ '|'  ∷ maxChars sig frameBytes
      ++ₗ toList "] "
      ++ₗ unitChars sig frameBytes
      ++ₗ ' '  ∷ recvChars sig frameBytes
      ++ₗ '\n' ∷ []

-- ============================================================================
-- SHAPE LEMMA: emitSignalLine-chars decomposition
-- ============================================================================

-- `emitSignalLine-chars` is a right-associated `++ₗ` chain whose head is
-- `toList " SG_ "` and tail terminates at `'\n' ∷ []`.  The chain factors
-- through 3 `++ₗ-assoc` boundaries: `[" SG_ "]` / `[<name>]` /
-- `[<mux marker>]` / `[<tailBody>]`.  Pushing the outer `++ₗ suffix`
-- through these three boundaries lands a structured shape we can step
-- through by parser primitives.
private
  emitSignalLine-chars-shape :
      ∀ (master : Maybe (List Char)) (frameBytes : ℕ) (sig : DBCSignal)
        (suffix : List Char)
    → emitSignalLine-chars master frameBytes sig ++ₗ suffix
      ≡ toList " SG_ " ++ₗ nameChars sig frameBytes
          ++ₗ emitMuxMarker-chars master (Identifier.name (DBCSignal.name sig))
                (DBCSignal.presence sig)
          ++ₗ tailBody-chars frameBytes sig ++ₗ suffix
  emitSignalLine-chars-shape master frameBytes sig suffix =
    trans (++ₗ-assoc (toList " SG_ ")
                     (Identifier.name (DBCSignal.name sig) ++ₗ
                      emitMuxMarker-chars master (Identifier.name (DBCSignal.name sig))
                        (DBCSignal.presence sig) ++ₗ
                      tailBody-chars frameBytes sig)
                     suffix)
      (cong (toList " SG_ " ++ₗ_)
        (trans (++ₗ-assoc (Identifier.name (DBCSignal.name sig))
                          (emitMuxMarker-chars master (Identifier.name (DBCSignal.name sig))
                             (DBCSignal.presence sig) ++ₗ
                           tailBody-chars frameBytes sig)
                          suffix)
          (cong (Identifier.name (DBCSignal.name sig) ++ₗ_)
            (++ₗ-assoc (emitMuxMarker-chars master (Identifier.name (DBCSignal.name sig))
                          (DBCSignal.presence sig))
                       (tailBody-chars frameBytes sig)
                       suffix))))


-- ============================================================================
-- TAIL EXTRACTION
-- ============================================================================

-- The 28-step tail of `parseSignalLine` (after `parseIdentifier` + `parseMuxMarker`)
-- as a standalone parser parameterized on the name + mux.  The body is
-- definitionally the same as the original `parseSignalLine` body from
-- `parseWSOpt` (step 6) onwards, with `name` and `mux` already bound.
parseSignalTail : Identifier → MuxMarker → Parser RawSignal
parseSignalTail name mux = do
  _ ← parseWSOpt
  _ ← char ':'
  _ ← parseWSOpt
  startBit ← parseNatural
  _ ← char '|'
  bitLength ← parseNatural
  _ ← char '@'
  bo ← parseByteOrderDigit
  isSigned ← parseSignFlag
  _ ← parseWSOpt
  _ ← char '('
  factor ← parseDecRat
  _ ← char ','
  offset ← parseDecRat
  _ ← char ')'
  _ ← parseWSOpt
  _ ← char '['
  minimum ← parseDecRat
  _ ← char '|'
  maximum ← parseDecRat
  _ ← char ']'
  _ ← parseWSOpt
  unit ← parseStringLit
  _ ← parseWSOpt
  receivers ← parseReceiverList
  _ ← parseWSOpt
  _ ← parseNewline
  pure (mkRawSignal name mux startBit bitLength bo isSigned
                    factor offset minimum maximum unit
                    (stripVectorPlaceholder receivers))
  where open import Aletheia.DBC.TextParser.Topology using (parseReceiverList)

-- Verify decomposition holds definitionally.
parseSignalLine-decompose : ∀ (pos : Position) (input : List Char)
  → parseSignalLine pos input
    ≡ (parseWSOpt >>= λ _ →
       string "SG_" >>= λ _ →
       parseWS >>= λ _ →
       parseIdentifier >>= λ name →
       parseMuxMarker >>= λ mux →
       parseSignalTail name mux) pos input
parseSignalLine-decompose _ _ = refl


-- ============================================================================
-- HELPERS
-- ============================================================================

-- `parseWSOpt` consuming zero hspace.  Used between the mux marker and
-- `':'`, between `']'` and `'"'`, between the receiver list and `'\n'`,
-- etc. — wherever the formatter does NOT emit a space at that position
-- but the parser optionally tolerates one.
private
  parseWSOpt-zero : ∀ (pos : Position) (suffix : List Char)
    → SuffixStops isHSpace suffix
    → parseWSOpt pos suffix
      ≡ just (mkResult [] pos suffix)
  parseWSOpt-zero pos suffix ss =
    manyHelper-satisfy-exhaust-many isHSpace pos [] suffix [] ss

-- `parseWSOpt` consuming exactly one leading space.  Mirrors
-- `parseWS-one-space` but lifted to `parseWSOpt = many` (which differs
-- only at the empty-input boundary, irrelevant here since input has at
-- least one char).
  parseWSOpt-one-space : ∀ (pos : Position) (suffix : List Char)
    → SuffixStops isHSpace suffix
    → parseWSOpt pos (' ' ∷ suffix)
      ≡ just (mkResult (' ' ∷ [])
                       (advancePosition pos ' ') suffix)
  parseWSOpt-one-space pos suffix ss =
    manyHelper-satisfy-exhaust-many isHSpace pos (' ' ∷ []) suffix
      (refl All.∷ All.[]) ss

-- We refer to `parseReceiverList` from Topology directly to compose 3d.2.
open import Aletheia.DBC.TextParser.Topology using (parseReceiverList)


-- ============================================================================
-- TAIL ROUNDTRIP — 28-step bind chain for the post-mux body
-- ============================================================================

-- The 28-step bind chain after `parseMuxMarker`.  Output uses
-- `DBCSignal.receivers sig` directly (post-`stripVectorPlaceholder`
-- discharge via 3d.2's existential lemma); other fields recovered by
-- composing Layer 2 roundtrip lemmas.
--
-- Tail input starts with `' ' ∷ ':' ∷ ' ' ∷ <sb> ++ '|' ∷ <bl> ++ ...`.
-- All fixed separators (`':' '|' '@' '(' ',' ')' '[' '|' ']' '\n'`) are
-- closed chars; their stop witnesses are `∷-stop refl` against each
-- subsequent parser's `Suffix Stops` predicate.

-- Tail input chunks, bookkeeping position after each step.  Useful for
-- both the proof body (advances cursor literally) AND a separate
-- alignment lemma that bridges `pos-end-of-tail` to `advancePositions pos
-- (tailBody-chars fb sig)`.
private
  module TailPositions
      (pos : Position) (sig : DBCSignal) (frameBytes : ℕ) where
    sbCs blCs boCs sgnCs facCs offCs minCs maxCs untCs rcvCs : List Char
    sbCs   = showℕ-dec-chars (unconvertStartBit frameBytes
                                (DBCSignal.byteOrder sig)
                                (SignalDef.startBit (DBCSignal.signalDef sig))
                                (SignalDef.bitLength (DBCSignal.signalDef sig)))
    blCs   = showℕ-dec-chars (SignalDef.bitLength (DBCSignal.signalDef sig))
    boCs   = emitByteOrderDigit-chars (DBCSignal.byteOrder sig)
    sgnCs  = emitSignFlag-chars (SignalDef.isSigned (DBCSignal.signalDef sig))
    facCs  = showDecRat-dec-chars (SignalDef.factor (DBCSignal.signalDef sig))
    offCs  = showDecRat-dec-chars (SignalDef.offset (DBCSignal.signalDef sig))
    minCs  = showDecRat-dec-chars (SignalDef.minimum (DBCSignal.signalDef sig))
    maxCs  = showDecRat-dec-chars (SignalDef.maximum (DBCSignal.signalDef sig))
    untCs  = quoteStringLit-chars (DBCSignal.unit sig)
    rcvCs  = emitReceivers-chars (CanonicalReceivers.list (DBCSignal.receivers sig))

    pos₁  = advancePosition  pos    ' '
    pos₂  = advancePosition  pos₁   ':'
    pos₃  = advancePosition  pos₂   ' '
    pos₄  = advancePositions pos₃   sbCs
    pos₅  = advancePosition  pos₄   '|'
    pos₆  = advancePositions pos₅   blCs
    pos₇  = advancePosition  pos₆   '@'
    pos₈  = advancePositions pos₇   boCs
    pos₉  = advancePositions pos₈   sgnCs
    pos₁₀ = advancePosition  pos₉   ' '
    pos₁₁ = advancePosition  pos₁₀  '('
    pos₁₂ = advancePositions pos₁₁  facCs
    pos₁₃ = advancePosition  pos₁₂  ','
    pos₁₄ = advancePositions pos₁₃  offCs
    pos₁₅ = advancePosition  pos₁₄  ')'
    pos₁₆ = advancePosition  pos₁₅  ' '
    pos₁₇ = advancePosition  pos₁₆  '['
    pos₁₈ = advancePositions pos₁₇  minCs
    pos₁₉ = advancePosition  pos₁₈  '|'
    pos₂₀ = advancePositions pos₁₉  maxCs
    pos₂₁ = advancePosition  pos₂₀  ']'
    pos₂₂ = advancePosition  pos₂₁  ' '
    pos₂₃ = advancePositions pos₂₂  untCs
    pos₂₄ = advancePosition  pos₂₃  ' '
    pos₂₅ = advancePositions pos₂₄  rcvCs
    pos₂₆ = pos₂₅
    pos₂₇ = advancePosition  pos₂₆  '\n'

-- ============================================================================
-- showNat-chars head non-hspace witnesses
-- ============================================================================

-- Helpers extracting the leading `c ∷ cs` shape of `showℕ-dec-chars n`
-- and witnessing `isHSpace c ≡ false` (digits are not hspace).  Drives
-- the `SuffixStops isHSpace` witnesses for the `parseWSOpt` calls
-- adjacent to the startBit / bitLength digit segments.

private
  open import Aletheia.DBC.TextParser.DecRatParse.Properties using
    (showNat-chars-head)
  open import Aletheia.DBC.TextFormatter.Emitter using (digitChar)

  -- Generic: `digitChar d` is not hspace (`isHSpace = ⌊_≟_' '⌋ ∨ ⌊_≟_'\t'⌋`).
  -- digitChar d ∈ {'0','1',...,'9'}, none of which is space or tab.
  digitChar-isHSpace-false : ∀ d → d Data.Nat.< 10 → isHSpace (digitChar d) ≡ false
  digitChar-isHSpace-false zero                                 _                              = refl
  digitChar-isHSpace-false (suc zero)                           _                              = refl
  digitChar-isHSpace-false (suc (suc zero))                     _                              = refl
  digitChar-isHSpace-false (suc (suc (suc zero)))               _                              = refl
  digitChar-isHSpace-false (suc (suc (suc (suc zero))))         _                              = refl
  digitChar-isHSpace-false (suc (suc (suc (suc (suc zero)))))   _                              = refl
  digitChar-isHSpace-false (suc (suc (suc (suc (suc (suc zero)))))) _                          = refl
  digitChar-isHSpace-false (suc (suc (suc (suc (suc (suc (suc zero))))))) _                    = refl
  digitChar-isHSpace-false (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) _              = refl
  digitChar-isHSpace-false (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))  _       = refl
  digitChar-isHSpace-false (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc _)))))))))) (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ()))))))))))

  -- Suffix stop witness for `showℕ-dec-chars n ++ rest` — the head is a
  -- digitChar (non-hspace) so the leading char fails `isHSpace`.
  showℕ-head-isHSpace-stop : ∀ n (rest : List Char)
    → SuffixStops isHSpace (showℕ-dec-chars n ++ₗ rest)
  showℕ-head-isHSpace-stop n rest with showNat-chars-head n
  ... | d , tail , d<10 , eq
      rewrite eq = ∷-stop (digitChar-isHSpace-false d d<10)


-- ============================================================================
-- TAIL-WITH-SUFFIX SHAPE
-- ============================================================================

-- The right-associated form of `tailBody-chars fb sig ++ suffix` with
-- the outer `++ suffix` pushed all the way through to the trailing `'\n'`.
-- This form lets each parser step in `parseSignalTail-roundtrip` consume
-- its chunk and emit a clean `<chunk> ++ <next-rest>` shape without
-- per-step `++-assoc` rewrites.
private
  tailBody-with-suffix : (frameBytes : ℕ) (sig : DBCSignal)
                          (suffix : List Char) → List Char
  tailBody-with-suffix fb sig suffix =
    toList " : "
      ++ₗ sbChars sig fb
      ++ₗ '|' ∷ blChars sig fb
      ++ₗ '@' ∷ boChars sig fb
      ++ₗ           signChars sig fb
      ++ₗ toList " (" ++ₗ factorChars sig fb
      ++ₗ ',' ∷ offsetChars sig fb
      ++ₗ toList ") "
      ++ₗ '[' ∷ minChars sig fb
      ++ₗ '|' ∷ maxChars sig fb
      ++ₗ toList "] "
      ++ₗ unitChars sig fb
      ++ₗ ' ' ∷ recvChars sig fb
      ++ₗ '\n' ∷ suffix

  -- The 14 segments of `tailBody-chars` as a list of pieces.  Each
  -- piece is either a closed string (`toList "..."`), a closed cons
  -- (`'c' ∷ ...`), or a variable-length chunk (`<show>` chars).  The
  -- whole body is the segments folded right via `++ₗ`, with a trailing
  -- argument that becomes either `'\n' ∷ []` (for `tailBody-chars`) or
  -- `'\n' ∷ suffix` (for `tailBody-with-suffix`).
  tailBody-segments : (frameBytes : ℕ) (sig : DBCSignal) → List (List Char)
  tailBody-segments fb sig =
      toList " : "
    ∷ sbChars sig fb
    ∷ ('|' ∷ blChars sig fb)
    ∷ ('@' ∷ boChars sig fb)
    ∷ signChars sig fb
    ∷ toList " ("
    ∷ factorChars sig fb
    ∷ (',' ∷ offsetChars sig fb)
    ∷ toList ") "
    ∷ ('[' ∷ minChars sig fb)
    ∷ ('|' ∷ maxChars sig fb)
    ∷ toList "] "
    ∷ unitChars sig fb
    ∷ (' ' ∷ recvChars sig fb)
    ∷ []

  -- Right-fold over a list of segments with a trailing literal.  Equiv-
  -- alent in shape to `Data.List.concat` but with a custom trailing
  -- arg, which is what makes the shift lemma below collapse to one
  -- structural induction.
  buildTail : List (List Char) → List Char → List Char
  buildTail []         trail = trail
  buildTail (s ∷ segs) trail = s ++ₗ buildTail segs trail

  -- `tailBody-chars` and `tailBody-with-suffix` agree on segments and
  -- differ only in the trail.  Both unfold by `refl` against the
  -- explicit definitions above.
  tailBody-via-buildTail : ∀ (fb : ℕ) (sig : DBCSignal)
    → tailBody-chars fb sig ≡ buildTail (tailBody-segments fb sig) ('\n' ∷ [])
  tailBody-via-buildTail _ _ = refl

  tailBody-with-suffix-via-buildTail : ∀ (fb : ℕ) (sig : DBCSignal) (suffix : List Char)
    → tailBody-with-suffix fb sig suffix
      ≡ buildTail (tailBody-segments fb sig) ('\n' ∷ suffix)
  tailBody-with-suffix-via-buildTail _ _ _ = refl

  -- THE structural shift lemma.  One induction on segs covers the 14
  -- segments (and would scale to any number) — the user-flagged
  -- `cong (trans ...)` cascade is gone.
  buildTail-++-shift : ∀ (segs : List (List Char)) (trail suffix : List Char)
    → buildTail segs trail ++ₗ suffix ≡ buildTail segs (trail ++ₗ suffix)
  buildTail-++-shift []         trail suffix = refl
  buildTail-++-shift (s ∷ segs) trail suffix =
    trans (++ₗ-assoc s (buildTail segs trail) suffix)
          (cong (s ++ₗ_) (buildTail-++-shift segs trail suffix))

  tailBody-shape : ∀ (frameBytes : ℕ) (sig : DBCSignal) (suffix : List Char)
    → tailBody-chars frameBytes sig ++ₗ suffix
      ≡ tailBody-with-suffix frameBytes sig suffix
  tailBody-shape fb sig suffix =
    trans (cong (_++ₗ suffix) (tailBody-via-buildTail fb sig))
      (trans (buildTail-++-shift (tailBody-segments fb sig) ('\n' ∷ []) suffix)
        (sym (tailBody-with-suffix-via-buildTail fb sig suffix)))


-- ============================================================================
-- parseSignalTail-roundtrip — 28-step bind chain proof body
-- ============================================================================

parseSignalTail-roundtrip :
    ∀ (pos : Position) (name : Identifier) (mux : MuxMarker)
      (sig : DBCSignal) (frameBytes : ℕ) (suffix : List Char)
  → All (λ r → ¬ Identifier.name r ≡ toList "Vector__XXX") (CanonicalReceivers.list (DBCSignal.receivers sig))
  → SuffixStops isHSpace (emitReceivers-chars (CanonicalReceivers.list (DBCSignal.receivers sig))
                          ++ₗ '\n' ∷ suffix)
  → SuffixStops isReceiverCont suffix
  → parseSignalTail name mux pos
      (tailBody-with-suffix frameBytes sig suffix)
    ≡ just (mkResult
              (mkRawSignal name mux
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
                 (CanonicalReceivers.list (DBCSignal.receivers sig)))
              (TailPositions.pos₂₇ pos sig frameBytes)
              suffix)
parseSignalTail-roundtrip pos name mux sig fb suffix novecxxx recv-stop ss = proof
  where
    open TailPositions pos sig fb

    -- Field projections for the result RawSignal.
    sb : ℕ
    sb = unconvertStartBit fb (DBCSignal.byteOrder sig)
            (SignalDef.startBit (DBCSignal.signalDef sig))
            (SignalDef.bitLength (DBCSignal.signalDef sig))
    bl : ℕ
    bl = SignalDef.bitLength (DBCSignal.signalDef sig)
    bo : ByteOrder
    bo = DBCSignal.byteOrder sig
    isSign : Bool
    isSign = SignalDef.isSigned (DBCSignal.signalDef sig)
    facd offd mind maxd : DecRat
    facd = SignalDef.factor (DBCSignal.signalDef sig)
    offd = SignalDef.offset (DBCSignal.signalDef sig)
    mind = SignalDef.minimum (DBCSignal.signalDef sig)
    maxd = SignalDef.maximum (DBCSignal.signalDef sig)
    -- Post-3d.4 + JSON-mirror: `DBCSignal.unit : List Char`.
    unitS : List Char
    unitS = DBCSignal.unit sig

    -- Compose 3d.2's existential to discharge `stripVectorPlaceholder`.
    receivers-strip-eq :
        ∃[ parsedRs ]
            (parseReceiverList pos₂₄
              (rcvCs ++ₗ '\n' ∷ suffix)
              ≡ just (mkResult parsedRs pos₂₅ ('\n' ∷ suffix)))
          × (stripVectorPlaceholder parsedRs ≡ CanonicalReceivers.list (DBCSignal.receivers sig))
    receivers-strip-eq =
      parseReceiverList∘strip-roundtrip pos₂₄
        (CanonicalReceivers.list (DBCSignal.receivers sig)) ('\n' ∷ suffix)
        novecxxx (∷-stop refl)

    parsedRs : List Identifier
    parsedRs = proj₁ receivers-strip-eq

    parseRcv-eq : parseReceiverList pos₂₄
                    (rcvCs ++ₗ '\n' ∷ suffix)
                  ≡ just (mkResult parsedRs pos₂₅ ('\n' ∷ suffix))
    parseRcv-eq = proj₁ (proj₂ receivers-strip-eq)

    strip-eq : stripVectorPlaceholder parsedRs ≡ CanonicalReceivers.list (DBCSignal.receivers sig)
    strip-eq = proj₂ (proj₂ receivers-strip-eq)

    -- Concrete result of the bind chain — name, mux, plus all parsed
    -- field values (using DBCSignal.receivers sig via strip-eq rewrite).
    expectedRawHere : RawSignal
    expectedRawHere = mkRawSignal name mux
      (unconvertStartBit fb (DBCSignal.byteOrder sig)
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
      (CanonicalReceivers.list (DBCSignal.receivers sig))

    -- Step proofs follow.  Each `step-N` advances one bind in the
    -- 28-step chain, threaded via `bind-just-step`.  The continuation
    -- arg is left implicit (Agda infers from the surrounding `>>=`
    -- structure).
    --
    -- Below `pos`, each `posₙ` and char-segment name comes from
    -- `TailPositions` (opened at the top of the where).

    -- Each `stepN-input` is the input the parser sees ENTERING step N.
    -- Each `stepN-rest` is what's left AFTER step N consumes its chunk.
    -- The clean right-associated form lets each step witness be a
    -- direct Layer-2 lemma application.
    step1-input step1-rest step2-rest step3-rest step4-rest step5-rest
      step6-rest step7-rest step8-rest step9-rest step10-rest step11-rest
      step12-rest step13-rest step14-rest step15-rest step16-rest
      step17-rest step18-rest step19-rest step20-rest step21-rest
      step22-rest step23-rest step24-rest step25-rest step26-rest
      step27-rest : List Char
    step1-input  = tailBody-with-suffix fb sig suffix
    step1-rest   = ':' ∷ ' ' ∷ sbCs ++ₗ '|' ∷ blCs ++ₗ '@' ∷ boCs ++ₗ sgnCs ++ₗ
                   toList " (" ++ₗ facCs ++ₗ ',' ∷ offCs ++ₗ toList ") " ++ₗ
                   '[' ∷ minCs ++ₗ '|' ∷ maxCs ++ₗ toList "] " ++ₗ untCs ++ₗ
                   ' ' ∷ rcvCs ++ₗ '\n' ∷ suffix
    step2-rest   = ' ' ∷ sbCs ++ₗ '|' ∷ blCs ++ₗ '@' ∷ boCs ++ₗ sgnCs ++ₗ
                   toList " (" ++ₗ facCs ++ₗ ',' ∷ offCs ++ₗ toList ") " ++ₗ
                   '[' ∷ minCs ++ₗ '|' ∷ maxCs ++ₗ toList "] " ++ₗ untCs ++ₗ
                   ' ' ∷ rcvCs ++ₗ '\n' ∷ suffix
    step3-rest   = sbCs ++ₗ '|' ∷ blCs ++ₗ '@' ∷ boCs ++ₗ sgnCs ++ₗ
                   toList " (" ++ₗ facCs ++ₗ ',' ∷ offCs ++ₗ toList ") " ++ₗ
                   '[' ∷ minCs ++ₗ '|' ∷ maxCs ++ₗ toList "] " ++ₗ untCs ++ₗ
                   ' ' ∷ rcvCs ++ₗ '\n' ∷ suffix
    step4-rest   = '|' ∷ blCs ++ₗ '@' ∷ boCs ++ₗ sgnCs ++ₗ
                   toList " (" ++ₗ facCs ++ₗ ',' ∷ offCs ++ₗ toList ") " ++ₗ
                   '[' ∷ minCs ++ₗ '|' ∷ maxCs ++ₗ toList "] " ++ₗ untCs ++ₗ
                   ' ' ∷ rcvCs ++ₗ '\n' ∷ suffix
    step5-rest   = blCs ++ₗ '@' ∷ boCs ++ₗ sgnCs ++ₗ
                   toList " (" ++ₗ facCs ++ₗ ',' ∷ offCs ++ₗ toList ") " ++ₗ
                   '[' ∷ minCs ++ₗ '|' ∷ maxCs ++ₗ toList "] " ++ₗ untCs ++ₗ
                   ' ' ∷ rcvCs ++ₗ '\n' ∷ suffix
    step6-rest   = '@' ∷ boCs ++ₗ sgnCs ++ₗ
                   toList " (" ++ₗ facCs ++ₗ ',' ∷ offCs ++ₗ toList ") " ++ₗ
                   '[' ∷ minCs ++ₗ '|' ∷ maxCs ++ₗ toList "] " ++ₗ untCs ++ₗ
                   ' ' ∷ rcvCs ++ₗ '\n' ∷ suffix
    step7-rest   = boCs ++ₗ sgnCs ++ₗ
                   toList " (" ++ₗ facCs ++ₗ ',' ∷ offCs ++ₗ toList ") " ++ₗ
                   '[' ∷ minCs ++ₗ '|' ∷ maxCs ++ₗ toList "] " ++ₗ untCs ++ₗ
                   ' ' ∷ rcvCs ++ₗ '\n' ∷ suffix
    step8-rest   = sgnCs ++ₗ
                   toList " (" ++ₗ facCs ++ₗ ',' ∷ offCs ++ₗ toList ") " ++ₗ
                   '[' ∷ minCs ++ₗ '|' ∷ maxCs ++ₗ toList "] " ++ₗ untCs ++ₗ
                   ' ' ∷ rcvCs ++ₗ '\n' ∷ suffix
    step9-rest   = toList " (" ++ₗ facCs ++ₗ ',' ∷ offCs ++ₗ toList ") " ++ₗ
                   '[' ∷ minCs ++ₗ '|' ∷ maxCs ++ₗ toList "] " ++ₗ untCs ++ₗ
                   ' ' ∷ rcvCs ++ₗ '\n' ∷ suffix
    step10-rest  = '(' ∷ facCs ++ₗ ',' ∷ offCs ++ₗ toList ") " ++ₗ
                   '[' ∷ minCs ++ₗ '|' ∷ maxCs ++ₗ toList "] " ++ₗ untCs ++ₗ
                   ' ' ∷ rcvCs ++ₗ '\n' ∷ suffix
    step11-rest  = facCs ++ₗ ',' ∷ offCs ++ₗ toList ") " ++ₗ
                   '[' ∷ minCs ++ₗ '|' ∷ maxCs ++ₗ toList "] " ++ₗ untCs ++ₗ
                   ' ' ∷ rcvCs ++ₗ '\n' ∷ suffix
    step12-rest  = ',' ∷ offCs ++ₗ toList ") " ++ₗ
                   '[' ∷ minCs ++ₗ '|' ∷ maxCs ++ₗ toList "] " ++ₗ untCs ++ₗ
                   ' ' ∷ rcvCs ++ₗ '\n' ∷ suffix
    step13-rest  = offCs ++ₗ toList ") " ++ₗ
                   '[' ∷ minCs ++ₗ '|' ∷ maxCs ++ₗ toList "] " ++ₗ untCs ++ₗ
                   ' ' ∷ rcvCs ++ₗ '\n' ∷ suffix
    step14-rest  = toList ") " ++ₗ
                   '[' ∷ minCs ++ₗ '|' ∷ maxCs ++ₗ toList "] " ++ₗ untCs ++ₗ
                   ' ' ∷ rcvCs ++ₗ '\n' ∷ suffix
    step15-rest  = ' ' ∷ '[' ∷ minCs ++ₗ '|' ∷ maxCs ++ₗ toList "] " ++ₗ untCs ++ₗ
                   ' ' ∷ rcvCs ++ₗ '\n' ∷ suffix
    step16-rest  = '[' ∷ minCs ++ₗ '|' ∷ maxCs ++ₗ toList "] " ++ₗ untCs ++ₗ
                   ' ' ∷ rcvCs ++ₗ '\n' ∷ suffix
    step17-rest  = minCs ++ₗ '|' ∷ maxCs ++ₗ toList "] " ++ₗ untCs ++ₗ
                   ' ' ∷ rcvCs ++ₗ '\n' ∷ suffix
    step18-rest  = '|' ∷ maxCs ++ₗ toList "] " ++ₗ untCs ++ₗ
                   ' ' ∷ rcvCs ++ₗ '\n' ∷ suffix
    step19-rest  = maxCs ++ₗ toList "] " ++ₗ untCs ++ₗ
                   ' ' ∷ rcvCs ++ₗ '\n' ∷ suffix
    step20-rest  = toList "] " ++ₗ untCs ++ₗ ' ' ∷ rcvCs ++ₗ '\n' ∷ suffix
    step21-rest  = ' ' ∷ untCs ++ₗ ' ' ∷ rcvCs ++ₗ '\n' ∷ suffix
    step22-rest  = untCs ++ₗ ' ' ∷ rcvCs ++ₗ '\n' ∷ suffix
    step23-rest  = ' ' ∷ rcvCs ++ₗ '\n' ∷ suffix
    step24-rest  = rcvCs ++ₗ '\n' ∷ suffix
    step25-rest  = '\n' ∷ suffix
    step26-rest  = '\n' ∷ suffix
    step27-rest  = suffix

    -- We will use `bind-just-step` at each step.  The continuation is
    -- inferred by Agda from the nested do-block of `parseSignalTail`.

    -- Continuation after step N: the residual `parseSignalTail name mux`
    -- body from step N+1 onwards, with values from steps 1..N already
    -- bound.  Defined as Parser RawSignal so each step is a bind chain.
    cont1 : List Char → Parser RawSignal
    cont1 _ = do
      _ ← char ':'
      _ ← parseWSOpt
      startBit ← parseNatural
      _ ← char '|'
      bitLength ← parseNatural
      _ ← char '@'
      bo ← parseByteOrderDigit
      isSigned ← parseSignFlag
      _ ← parseWSOpt
      _ ← char '('
      factor ← parseDecRat
      _ ← char ','
      offset ← parseDecRat
      _ ← char ')'
      _ ← parseWSOpt
      _ ← char '['
      minimum ← parseDecRat
      _ ← char '|'
      maximum ← parseDecRat
      _ ← char ']'
      _ ← parseWSOpt
      unit ← parseStringLit
      _ ← parseWSOpt
      receivers ← parseReceiverList
      _ ← parseWSOpt
      _ ← parseNewline
      pure (mkRawSignal name mux startBit bitLength bo isSigned
                        factor offset minimum maximum unit
                        (stripVectorPlaceholder receivers))

    -- Step 1: parseWSOpt consumes ' ' (head of " : " in the tail).
    step1 : parseSignalTail name mux pos step1-input
          ≡ cont1 (' ' ∷ []) pos₁ step1-rest
    step1 = bind-just-step parseWSOpt cont1 pos step1-input
              (' ' ∷ []) pos₁ step1-rest
              (parseWSOpt-one-space pos step1-rest (∷-stop refl))

    -- Step 2: char ':' matches the literal colon.
    cont2 : Char → Parser RawSignal
    cont2 _ = do
      _ ← parseWSOpt
      startBit ← parseNatural
      _ ← char '|'
      bitLength ← parseNatural
      _ ← char '@'
      bo ← parseByteOrderDigit
      isSigned ← parseSignFlag
      _ ← parseWSOpt
      _ ← char '('
      factor ← parseDecRat
      _ ← char ','
      offset ← parseDecRat
      _ ← char ')'
      _ ← parseWSOpt
      _ ← char '['
      minimum ← parseDecRat
      _ ← char '|'
      maximum ← parseDecRat
      _ ← char ']'
      _ ← parseWSOpt
      unit ← parseStringLit
      _ ← parseWSOpt
      receivers ← parseReceiverList
      _ ← parseWSOpt
      _ ← parseNewline
      pure (mkRawSignal name mux startBit bitLength bo isSigned
                        factor offset minimum maximum unit
                        (stripVectorPlaceholder receivers))

    step2 : cont1 (' ' ∷ []) pos₁ step1-rest ≡ cont2 ':' pos₂ step2-rest
    step2 = bind-just-step (char ':') cont2 pos₁ step1-rest
              ':' pos₂ step2-rest
              (char-matches ':' pos₁ step2-rest)

    -- Step 3: parseWSOpt consumes ' ' (between ':' and startBit digits).
    cont3 : List Char → Parser RawSignal
    cont3 _ = do
      startBit ← parseNatural
      _ ← char '|'
      bitLength ← parseNatural
      _ ← char '@'
      bo ← parseByteOrderDigit
      isSigned ← parseSignFlag
      _ ← parseWSOpt
      _ ← char '('
      factor ← parseDecRat
      _ ← char ','
      offset ← parseDecRat
      _ ← char ')'
      _ ← parseWSOpt
      _ ← char '['
      minimum ← parseDecRat
      _ ← char '|'
      maximum ← parseDecRat
      _ ← char ']'
      _ ← parseWSOpt
      unit ← parseStringLit
      _ ← parseWSOpt
      receivers ← parseReceiverList
      _ ← parseWSOpt
      _ ← parseNewline
      pure (mkRawSignal name mux startBit bitLength bo isSigned
                        factor offset minimum maximum unit
                        (stripVectorPlaceholder receivers))

    step3 : cont2 ':' pos₂ step2-rest ≡ cont3 (' ' ∷ []) pos₃ step3-rest
    step3 = bind-just-step parseWSOpt cont3 pos₂ step2-rest
              (' ' ∷ []) pos₃ step3-rest
              (parseWSOpt-one-space pos₂ step3-rest
                 (showℕ-head-isHSpace-stop sb step4-rest))

    -- Step 4: parseNatural sb (startBit).
    cont4 : ℕ → Parser RawSignal
    cont4 startBit = do
      _ ← char '|'
      bitLength ← parseNatural
      _ ← char '@'
      bo ← parseByteOrderDigit
      isSigned ← parseSignFlag
      _ ← parseWSOpt
      _ ← char '('
      factor ← parseDecRat
      _ ← char ','
      offset ← parseDecRat
      _ ← char ')'
      _ ← parseWSOpt
      _ ← char '['
      minimum ← parseDecRat
      _ ← char '|'
      maximum ← parseDecRat
      _ ← char ']'
      _ ← parseWSOpt
      unit ← parseStringLit
      _ ← parseWSOpt
      receivers ← parseReceiverList
      _ ← parseWSOpt
      _ ← parseNewline
      pure (mkRawSignal name mux startBit bitLength bo isSigned
                        factor offset minimum maximum unit
                        (stripVectorPlaceholder receivers))

    step4 : cont3 (' ' ∷ []) pos₃ step3-rest ≡ cont4 sb pos₄ step4-rest
    step4 = bind-just-step parseNatural cont4 pos₃ step3-rest
              sb pos₄ step4-rest
              (parseNatural-showNat-chars pos₃ sb step4-rest (∷-stop refl))

    -- Step 5: char '|'.
    cont5 : ℕ → Char → Parser RawSignal
    cont5 startBit _ = do
      bitLength ← parseNatural
      _ ← char '@'
      bo ← parseByteOrderDigit
      isSigned ← parseSignFlag
      _ ← parseWSOpt
      _ ← char '('
      factor ← parseDecRat
      _ ← char ','
      offset ← parseDecRat
      _ ← char ')'
      _ ← parseWSOpt
      _ ← char '['
      minimum ← parseDecRat
      _ ← char '|'
      maximum ← parseDecRat
      _ ← char ']'
      _ ← parseWSOpt
      unit ← parseStringLit
      _ ← parseWSOpt
      receivers ← parseReceiverList
      _ ← parseWSOpt
      _ ← parseNewline
      pure (mkRawSignal name mux startBit bitLength bo isSigned
                        factor offset minimum maximum unit
                        (stripVectorPlaceholder receivers))

    step5 : cont4 sb pos₄ step4-rest ≡ cont5 sb '|' pos₅ step5-rest
    step5 = bind-just-step (char '|') (cont5 sb) pos₄ step4-rest
              '|' pos₅ step5-rest
              (char-matches '|' pos₄ step5-rest)

    -- Step 6: parseNatural bl (bitLength).
    cont6 : ℕ → ℕ → Parser RawSignal
    cont6 startBit bitLength = do
      _ ← char '@'
      bo ← parseByteOrderDigit
      isSigned ← parseSignFlag
      _ ← parseWSOpt
      _ ← char '('
      factor ← parseDecRat
      _ ← char ','
      offset ← parseDecRat
      _ ← char ')'
      _ ← parseWSOpt
      _ ← char '['
      minimum ← parseDecRat
      _ ← char '|'
      maximum ← parseDecRat
      _ ← char ']'
      _ ← parseWSOpt
      unit ← parseStringLit
      _ ← parseWSOpt
      receivers ← parseReceiverList
      _ ← parseWSOpt
      _ ← parseNewline
      pure (mkRawSignal name mux startBit bitLength bo isSigned
                        factor offset minimum maximum unit
                        (stripVectorPlaceholder receivers))

    step6 : cont5 sb '|' pos₅ step5-rest ≡ cont6 sb bl pos₆ step6-rest
    step6 = bind-just-step parseNatural (cont6 sb) pos₅ step5-rest
              bl pos₆ step6-rest
              (parseNatural-showNat-chars pos₅ bl step6-rest (∷-stop refl))

    -- Step 7: char '@'.
    cont7 : ℕ → ℕ → Char → Parser RawSignal
    cont7 startBit bitLength _ = do
      bo ← parseByteOrderDigit
      isSigned ← parseSignFlag
      _ ← parseWSOpt
      _ ← char '('
      factor ← parseDecRat
      _ ← char ','
      offset ← parseDecRat
      _ ← char ')'
      _ ← parseWSOpt
      _ ← char '['
      minimum ← parseDecRat
      _ ← char '|'
      maximum ← parseDecRat
      _ ← char ']'
      _ ← parseWSOpt
      unit ← parseStringLit
      _ ← parseWSOpt
      receivers ← parseReceiverList
      _ ← parseWSOpt
      _ ← parseNewline
      pure (mkRawSignal name mux startBit bitLength bo isSigned
                        factor offset minimum maximum unit
                        (stripVectorPlaceholder receivers))

    step7 : cont6 sb bl pos₆ step6-rest ≡ cont7 sb bl '@' pos₇ step7-rest
    step7 = bind-just-step (char '@') (cont7 sb bl) pos₆ step6-rest
              '@' pos₇ step7-rest
              (char-matches '@' pos₆ step7-rest)

    -- Step 8: parseByteOrderDigit.
    cont8 : ℕ → ℕ → ByteOrder → Parser RawSignal
    cont8 startBit bitLength bo = do
      isSigned ← parseSignFlag
      _ ← parseWSOpt
      _ ← char '('
      factor ← parseDecRat
      _ ← char ','
      offset ← parseDecRat
      _ ← char ')'
      _ ← parseWSOpt
      _ ← char '['
      minimum ← parseDecRat
      _ ← char '|'
      maximum ← parseDecRat
      _ ← char ']'
      _ ← parseWSOpt
      unit ← parseStringLit
      _ ← parseWSOpt
      receivers ← parseReceiverList
      _ ← parseWSOpt
      _ ← parseNewline
      pure (mkRawSignal name mux startBit bitLength bo isSigned
                        factor offset minimum maximum unit
                        (stripVectorPlaceholder receivers))

    step8 : cont7 sb bl '@' pos₇ step7-rest ≡ cont8 sb bl bo pos₈ step8-rest
    step8 = bind-just-step parseByteOrderDigit (cont8 sb bl) pos₇ step7-rest
              bo pos₈ step8-rest
              (parseByteOrderDigit-roundtrip pos₇ bo step8-rest)

    -- Step 9: parseSignFlag.
    cont9 : ℕ → ℕ → ByteOrder → Bool → Parser RawSignal
    cont9 startBit bitLength bo isSigned = do
      _ ← parseWSOpt
      _ ← char '('
      factor ← parseDecRat
      _ ← char ','
      offset ← parseDecRat
      _ ← char ')'
      _ ← parseWSOpt
      _ ← char '['
      minimum ← parseDecRat
      _ ← char '|'
      maximum ← parseDecRat
      _ ← char ']'
      _ ← parseWSOpt
      unit ← parseStringLit
      _ ← parseWSOpt
      receivers ← parseReceiverList
      _ ← parseWSOpt
      _ ← parseNewline
      pure (mkRawSignal name mux startBit bitLength bo isSigned
                        factor offset minimum maximum unit
                        (stripVectorPlaceholder receivers))

    step9 : cont8 sb bl bo pos₈ step8-rest
          ≡ cont9 sb bl bo isSign pos₉ step9-rest
    step9 = bind-just-step parseSignFlag (cont9 sb bl bo) pos₈ step8-rest
              isSign pos₉ step9-rest
              (parseSignFlag-roundtrip pos₈ isSign step9-rest)

    -- Step 10: parseWSOpt consumes ' ' (before '(').
    cont10 : ℕ → ℕ → ByteOrder → Bool → List Char → Parser RawSignal
    cont10 startBit bitLength bo isSigned _ = do
      _ ← char '('
      factor ← parseDecRat
      _ ← char ','
      offset ← parseDecRat
      _ ← char ')'
      _ ← parseWSOpt
      _ ← char '['
      minimum ← parseDecRat
      _ ← char '|'
      maximum ← parseDecRat
      _ ← char ']'
      _ ← parseWSOpt
      unit ← parseStringLit
      _ ← parseWSOpt
      receivers ← parseReceiverList
      _ ← parseWSOpt
      _ ← parseNewline
      pure (mkRawSignal name mux startBit bitLength bo isSigned
                        factor offset minimum maximum unit
                        (stripVectorPlaceholder receivers))

    step10 : cont9 sb bl bo isSign pos₉ step9-rest
           ≡ cont10 sb bl bo isSign (' ' ∷ []) pos₁₀ step10-rest
    step10 = bind-just-step parseWSOpt (cont10 sb bl bo isSign)
              pos₉ step9-rest (' ' ∷ []) pos₁₀ step10-rest
              (parseWSOpt-one-space pos₉ step10-rest (∷-stop refl))

    -- Step 11: char '('.
    cont11 : ℕ → ℕ → ByteOrder → Bool → Char → Parser RawSignal
    cont11 startBit bitLength bo isSigned _ = do
      factor ← parseDecRat
      _ ← char ','
      offset ← parseDecRat
      _ ← char ')'
      _ ← parseWSOpt
      _ ← char '['
      minimum ← parseDecRat
      _ ← char '|'
      maximum ← parseDecRat
      _ ← char ']'
      _ ← parseWSOpt
      unit ← parseStringLit
      _ ← parseWSOpt
      receivers ← parseReceiverList
      _ ← parseWSOpt
      _ ← parseNewline
      pure (mkRawSignal name mux startBit bitLength bo isSigned
                        factor offset minimum maximum unit
                        (stripVectorPlaceholder receivers))

    step11 : cont10 sb bl bo isSign (' ' ∷ []) pos₁₀ step10-rest
           ≡ cont11 sb bl bo isSign '(' pos₁₁ step11-rest
    step11 = bind-just-step (char '(') (cont11 sb bl bo isSign)
              pos₁₀ step10-rest '(' pos₁₁ step11-rest
              (char-matches '(' pos₁₀ step11-rest)

    -- Step 12: parseDecRat factor.
    cont12 : ℕ → ℕ → ByteOrder → Bool → DecRat → Parser RawSignal
    cont12 startBit bitLength bo isSigned factor = do
      _ ← char ','
      offset ← parseDecRat
      _ ← char ')'
      _ ← parseWSOpt
      _ ← char '['
      minimum ← parseDecRat
      _ ← char '|'
      maximum ← parseDecRat
      _ ← char ']'
      _ ← parseWSOpt
      unit ← parseStringLit
      _ ← parseWSOpt
      receivers ← parseReceiverList
      _ ← parseWSOpt
      _ ← parseNewline
      pure (mkRawSignal name mux startBit bitLength bo isSigned
                        factor offset minimum maximum unit
                        (stripVectorPlaceholder receivers))

    step12 : cont11 sb bl bo isSign '(' pos₁₁ step11-rest
           ≡ cont12 sb bl bo isSign facd pos₁₂ step12-rest
    step12 = bind-just-step parseDecRat (cont12 sb bl bo isSign)
              pos₁₁ step11-rest facd pos₁₂ step12-rest
              (parseDecRat-roundtrip-suffix facd pos₁₁ step12-rest (∷-stop refl))

    -- Step 13: char ','.
    cont13 : ℕ → ℕ → ByteOrder → Bool → DecRat → Char → Parser RawSignal
    cont13 startBit bitLength bo isSigned factor _ = do
      offset ← parseDecRat
      _ ← char ')'
      _ ← parseWSOpt
      _ ← char '['
      minimum ← parseDecRat
      _ ← char '|'
      maximum ← parseDecRat
      _ ← char ']'
      _ ← parseWSOpt
      unit ← parseStringLit
      _ ← parseWSOpt
      receivers ← parseReceiverList
      _ ← parseWSOpt
      _ ← parseNewline
      pure (mkRawSignal name mux startBit bitLength bo isSigned
                        factor offset minimum maximum unit
                        (stripVectorPlaceholder receivers))

    step13 : cont12 sb bl bo isSign facd pos₁₂ step12-rest
           ≡ cont13 sb bl bo isSign facd ',' pos₁₃ step13-rest
    step13 = bind-just-step (char ',') (cont13 sb bl bo isSign facd)
              pos₁₂ step12-rest ',' pos₁₃ step13-rest
              (char-matches ',' pos₁₂ step13-rest)

    -- Step 14: parseDecRat offset.
    cont14 : ℕ → ℕ → ByteOrder → Bool → DecRat → DecRat → Parser RawSignal
    cont14 startBit bitLength bo isSigned factor offset = do
      _ ← char ')'
      _ ← parseWSOpt
      _ ← char '['
      minimum ← parseDecRat
      _ ← char '|'
      maximum ← parseDecRat
      _ ← char ']'
      _ ← parseWSOpt
      unit ← parseStringLit
      _ ← parseWSOpt
      receivers ← parseReceiverList
      _ ← parseWSOpt
      _ ← parseNewline
      pure (mkRawSignal name mux startBit bitLength bo isSigned
                        factor offset minimum maximum unit
                        (stripVectorPlaceholder receivers))

    step14 : cont13 sb bl bo isSign facd ',' pos₁₃ step13-rest
           ≡ cont14 sb bl bo isSign facd offd pos₁₄ step14-rest
    step14 = bind-just-step parseDecRat (cont14 sb bl bo isSign facd)
              pos₁₃ step13-rest offd pos₁₄ step14-rest
              (parseDecRat-roundtrip-suffix offd pos₁₃ step14-rest (∷-stop refl))

    -- Step 15: char ')'.
    cont15 : ℕ → ℕ → ByteOrder → Bool → DecRat → DecRat → Char → Parser RawSignal
    cont15 startBit bitLength bo isSigned factor offset _ = do
      _ ← parseWSOpt
      _ ← char '['
      minimum ← parseDecRat
      _ ← char '|'
      maximum ← parseDecRat
      _ ← char ']'
      _ ← parseWSOpt
      unit ← parseStringLit
      _ ← parseWSOpt
      receivers ← parseReceiverList
      _ ← parseWSOpt
      _ ← parseNewline
      pure (mkRawSignal name mux startBit bitLength bo isSigned
                        factor offset minimum maximum unit
                        (stripVectorPlaceholder receivers))

    step15 : cont14 sb bl bo isSign facd offd pos₁₄ step14-rest
           ≡ cont15 sb bl bo isSign facd offd ')' pos₁₅ step15-rest
    step15 = bind-just-step (char ')') (cont15 sb bl bo isSign facd offd)
              pos₁₄ step14-rest ')' pos₁₅ step15-rest
              (char-matches ')' pos₁₄ step15-rest)

    -- Step 16: parseWSOpt consumes ' ' (between ')' and '[').
    cont16 : ℕ → ℕ → ByteOrder → Bool → DecRat → DecRat → List Char → Parser RawSignal
    cont16 startBit bitLength bo isSigned factor offset _ = do
      _ ← char '['
      minimum ← parseDecRat
      _ ← char '|'
      maximum ← parseDecRat
      _ ← char ']'
      _ ← parseWSOpt
      unit ← parseStringLit
      _ ← parseWSOpt
      receivers ← parseReceiverList
      _ ← parseWSOpt
      _ ← parseNewline
      pure (mkRawSignal name mux startBit bitLength bo isSigned
                        factor offset minimum maximum unit
                        (stripVectorPlaceholder receivers))

    step16 : cont15 sb bl bo isSign facd offd ')' pos₁₅ step15-rest
           ≡ cont16 sb bl bo isSign facd offd (' ' ∷ []) pos₁₆ step16-rest
    step16 = bind-just-step parseWSOpt (cont16 sb bl bo isSign facd offd)
              pos₁₅ step15-rest (' ' ∷ []) pos₁₆ step16-rest
              (parseWSOpt-one-space pos₁₅ step16-rest (∷-stop refl))

    -- Step 17: char '['.
    cont17 : ℕ → ℕ → ByteOrder → Bool → DecRat → DecRat → Char → Parser RawSignal
    cont17 startBit bitLength bo isSigned factor offset _ = do
      minimum ← parseDecRat
      _ ← char '|'
      maximum ← parseDecRat
      _ ← char ']'
      _ ← parseWSOpt
      unit ← parseStringLit
      _ ← parseWSOpt
      receivers ← parseReceiverList
      _ ← parseWSOpt
      _ ← parseNewline
      pure (mkRawSignal name mux startBit bitLength bo isSigned
                        factor offset minimum maximum unit
                        (stripVectorPlaceholder receivers))

    step17 : cont16 sb bl bo isSign facd offd (' ' ∷ []) pos₁₆ step16-rest
           ≡ cont17 sb bl bo isSign facd offd '[' pos₁₇ step17-rest
    step17 = bind-just-step (char '[') (cont17 sb bl bo isSign facd offd)
              pos₁₆ step16-rest '[' pos₁₇ step17-rest
              (char-matches '[' pos₁₆ step17-rest)

    -- Step 18: parseDecRat min.
    cont18 : ℕ → ℕ → ByteOrder → Bool → DecRat → DecRat → DecRat → Parser RawSignal
    cont18 startBit bitLength bo isSigned factor offset minimum = do
      _ ← char '|'
      maximum ← parseDecRat
      _ ← char ']'
      _ ← parseWSOpt
      unit ← parseStringLit
      _ ← parseWSOpt
      receivers ← parseReceiverList
      _ ← parseWSOpt
      _ ← parseNewline
      pure (mkRawSignal name mux startBit bitLength bo isSigned
                        factor offset minimum maximum unit
                        (stripVectorPlaceholder receivers))

    step18 : cont17 sb bl bo isSign facd offd '[' pos₁₇ step17-rest
           ≡ cont18 sb bl bo isSign facd offd mind pos₁₈ step18-rest
    step18 = bind-just-step parseDecRat (cont18 sb bl bo isSign facd offd)
              pos₁₇ step17-rest mind pos₁₈ step18-rest
              (parseDecRat-roundtrip-suffix mind pos₁₇ step18-rest (∷-stop refl))

    -- Step 19: char '|'.
    cont19 : ℕ → ℕ → ByteOrder → Bool → DecRat → DecRat → DecRat → Char → Parser RawSignal
    cont19 startBit bitLength bo isSigned factor offset minimum _ = do
      maximum ← parseDecRat
      _ ← char ']'
      _ ← parseWSOpt
      unit ← parseStringLit
      _ ← parseWSOpt
      receivers ← parseReceiverList
      _ ← parseWSOpt
      _ ← parseNewline
      pure (mkRawSignal name mux startBit bitLength bo isSigned
                        factor offset minimum maximum unit
                        (stripVectorPlaceholder receivers))

    step19 : cont18 sb bl bo isSign facd offd mind pos₁₈ step18-rest
           ≡ cont19 sb bl bo isSign facd offd mind '|' pos₁₉ step19-rest
    step19 = bind-just-step (char '|') (cont19 sb bl bo isSign facd offd mind)
              pos₁₈ step18-rest '|' pos₁₉ step19-rest
              (char-matches '|' pos₁₈ step19-rest)

    -- Step 20: parseDecRat max.
    cont20 : ℕ → ℕ → ByteOrder → Bool → DecRat → DecRat → DecRat → DecRat → Parser RawSignal
    cont20 startBit bitLength bo isSigned factor offset minimum maximum = do
      _ ← char ']'
      _ ← parseWSOpt
      unit ← parseStringLit
      _ ← parseWSOpt
      receivers ← parseReceiverList
      _ ← parseWSOpt
      _ ← parseNewline
      pure (mkRawSignal name mux startBit bitLength bo isSigned
                        factor offset minimum maximum unit
                        (stripVectorPlaceholder receivers))

    step20 : cont19 sb bl bo isSign facd offd mind '|' pos₁₉ step19-rest
           ≡ cont20 sb bl bo isSign facd offd mind maxd pos₂₀ step20-rest
    step20 = bind-just-step parseDecRat (cont20 sb bl bo isSign facd offd mind)
              pos₁₉ step19-rest maxd pos₂₀ step20-rest
              (parseDecRat-roundtrip-suffix maxd pos₁₉ step20-rest (∷-stop refl))

    -- Step 21: char ']'.
    cont21 : ℕ → ℕ → ByteOrder → Bool → DecRat → DecRat → DecRat → DecRat → Char → Parser RawSignal
    cont21 startBit bitLength bo isSigned factor offset minimum maximum _ = do
      _ ← parseWSOpt
      unit ← parseStringLit
      _ ← parseWSOpt
      receivers ← parseReceiverList
      _ ← parseWSOpt
      _ ← parseNewline
      pure (mkRawSignal name mux startBit bitLength bo isSigned
                        factor offset minimum maximum unit
                        (stripVectorPlaceholder receivers))

    step21 : cont20 sb bl bo isSign facd offd mind maxd pos₂₀ step20-rest
           ≡ cont21 sb bl bo isSign facd offd mind maxd ']' pos₂₁ step21-rest
    step21 = bind-just-step (char ']') (cont21 sb bl bo isSign facd offd mind maxd)
              pos₂₀ step20-rest ']' pos₂₁ step21-rest
              (char-matches ']' pos₂₀ step21-rest)

    -- Step 22: parseWSOpt consumes ' ' (between ']' and '"').
    cont22 : ℕ → ℕ → ByteOrder → Bool → DecRat → DecRat → DecRat → DecRat → List Char → Parser RawSignal
    cont22 startBit bitLength bo isSigned factor offset minimum maximum _ = do
      unit ← parseStringLit
      _ ← parseWSOpt
      receivers ← parseReceiverList
      _ ← parseWSOpt
      _ ← parseNewline
      pure (mkRawSignal name mux startBit bitLength bo isSigned
                        factor offset minimum maximum unit
                        (stripVectorPlaceholder receivers))

    step22 : cont21 sb bl bo isSign facd offd mind maxd ']' pos₂₁ step21-rest
           ≡ cont22 sb bl bo isSign facd offd mind maxd (' ' ∷ []) pos₂₂ step22-rest
    step22 = bind-just-step parseWSOpt (cont22 sb bl bo isSign facd offd mind maxd)
              pos₂₁ step21-rest (' ' ∷ []) pos₂₂ step22-rest
              (parseWSOpt-one-space pos₂₁ step22-rest (∷-stop refl))

    -- Step 23: parseStringLit unit.
    cont23 : ℕ → ℕ → ByteOrder → Bool → DecRat → DecRat → DecRat → DecRat → List Char → Parser RawSignal
    cont23 startBit bitLength bo isSigned factor offset minimum maximum unit = do
      _ ← parseWSOpt
      receivers ← parseReceiverList
      _ ← parseWSOpt
      _ ← parseNewline
      pure (mkRawSignal name mux startBit bitLength bo isSigned
                        factor offset minimum maximum unit
                        (stripVectorPlaceholder receivers))

    step23 : cont22 sb bl bo isSign facd offd mind maxd (' ' ∷ []) pos₂₂ step22-rest
           ≡ cont23 sb bl bo isSign facd offd mind maxd unitS pos₂₃ step23-rest
    step23 = bind-just-step parseStringLit (cont23 sb bl bo isSign facd offd mind maxd)
              pos₂₂ step22-rest unitS pos₂₃ step23-rest
              (parseStringLit-roundtrip pos₂₂ unitS step23-rest (∷-stop refl))

    -- Step 24: parseWSOpt consumes ' ' (between unit and receivers).
    cont24 : ℕ → ℕ → ByteOrder → Bool → DecRat → DecRat → DecRat → DecRat → List Char → List Char → Parser RawSignal
    cont24 startBit bitLength bo isSigned factor offset minimum maximum unit _ = do
      receivers ← parseReceiverList
      _ ← parseWSOpt
      _ ← parseNewline
      pure (mkRawSignal name mux startBit bitLength bo isSigned
                        factor offset minimum maximum unit
                        (stripVectorPlaceholder receivers))

    step24 : cont23 sb bl bo isSign facd offd mind maxd unitS pos₂₃ step23-rest
           ≡ cont24 sb bl bo isSign facd offd mind maxd unitS (' ' ∷ []) pos₂₄ step24-rest
    step24 = bind-just-step parseWSOpt (cont24 sb bl bo isSign facd offd mind maxd unitS)
              pos₂₃ step23-rest (' ' ∷ []) pos₂₄ step24-rest
              (parseWSOpt-one-space pos₂₃ step24-rest recv-stop)

    -- Step 25: parseReceiverList — composes 3d.2's existential.
    cont25 : ℕ → ℕ → ByteOrder → Bool → DecRat → DecRat → DecRat → DecRat → List Char → List Identifier → Parser RawSignal
    cont25 startBit bitLength bo isSigned factor offset minimum maximum unit receivers = do
      _ ← parseWSOpt
      _ ← parseNewline
      pure (mkRawSignal name mux startBit bitLength bo isSigned
                        factor offset minimum maximum unit
                        (stripVectorPlaceholder receivers))

    step25 : cont24 sb bl bo isSign facd offd mind maxd unitS (' ' ∷ []) pos₂₄ step24-rest
           ≡ cont25 sb bl bo isSign facd offd mind maxd unitS parsedRs pos₂₅ step25-rest
    step25 = bind-just-step parseReceiverList
              (cont25 sb bl bo isSign facd offd mind maxd unitS)
              pos₂₄ step24-rest parsedRs pos₂₅ step25-rest
              parseRcv-eq

    -- Step 26: parseWSOpt consumes 0 chars (next is '\n').
    cont26 : ℕ → ℕ → ByteOrder → Bool → DecRat → DecRat → DecRat → DecRat → List Char → List Identifier → List Char → Parser RawSignal
    cont26 startBit bitLength bo isSigned factor offset minimum maximum unit receivers _ = do
      _ ← parseNewline
      pure (mkRawSignal name mux startBit bitLength bo isSigned
                        factor offset minimum maximum unit
                        (stripVectorPlaceholder receivers))

    step26 : cont25 sb bl bo isSign facd offd mind maxd unitS parsedRs pos₂₅ step25-rest
           ≡ cont26 sb bl bo isSign facd offd mind maxd unitS parsedRs [] pos₂₆ step26-rest
    step26 = bind-just-step parseWSOpt
              (cont26 sb bl bo isSign facd offd mind maxd unitS parsedRs)
              pos₂₅ step25-rest [] pos₂₆ step26-rest
              (parseWSOpt-zero pos₂₅ step26-rest (∷-stop refl))

    -- Step 27: parseNewline.
    cont27 : ℕ → ℕ → ByteOrder → Bool → DecRat → DecRat → DecRat → DecRat → List Char → List Identifier → Char → Parser RawSignal
    cont27 startBit bitLength bo isSigned factor offset minimum maximum unit receivers _ =
      pure (mkRawSignal name mux startBit bitLength bo isSigned
                        factor offset minimum maximum unit
                        (stripVectorPlaceholder receivers))

    step27 : cont26 sb bl bo isSign facd offd mind maxd unitS parsedRs [] pos₂₆ step26-rest
           ≡ cont27 sb bl bo isSign facd offd mind maxd unitS parsedRs '\n' pos₂₇ step27-rest
    step27 = bind-just-step parseNewline
              (cont27 sb bl bo isSign facd offd mind maxd unitS parsedRs)
              pos₂₆ step26-rest '\n' pos₂₇ step27-rest
              (parseNewline-match-LF pos₂₆ step27-rest)

    -- Step 28: pure.  Closes the chain by `cong` over the receivers
    -- field — `stripVectorPlaceholder parsedRs ≡ DBCSignal.receivers sig`
    -- via 3d.2's strip-eq.
    step28 : cont27 sb bl bo isSign facd offd mind maxd unitS parsedRs '\n' pos₂₇ step27-rest
           ≡ just (mkResult expectedRawHere pos₂₇ suffix)
    step28 = cong
      (λ rs → just (mkResult
                       (mkRawSignal name mux sb bl bo isSign facd offd mind maxd unitS rs)
                       pos₂₇ suffix))
      strip-eq

    proof : parseSignalTail name mux pos step1-input
          ≡ just (mkResult expectedRawHere pos₂₇ suffix)
    proof =
      trans step1
        (trans step2
          (trans step3
            (trans step4
              (trans step5
                (trans step6
                  (trans step7
                    (trans step8
                      (trans step9
                        (trans step10
                          (trans step11
                            (trans step12
                              (trans step13
                                (trans step14
                                  (trans step15
                                    (trans step16
                                      (trans step17
                                        (trans step18
                                          (trans step19
                                            (trans step20
                                              (trans step21
                                                (trans step22
                                                  (trans step23
                                                    (trans step24
                                                      (trans step25
                                                        (trans step26
                                                          (trans step27 step28))))))))))))))))))))))))))


-- ============================================================================
-- POSITION ALIGNMENT — TailPositions.pos₂₇ ≡ advancePositions pos tailBody
-- ============================================================================

-- Closed-string reduction sanity check.  `toList " SG_ "` reduces to its
-- cons literal under `--safe --without-K` (Agda's primStringToList fires
-- on closed strings).  All position alignments below depend on this.
private
  toList-SG_-spaces : toList " SG_ " ≡ ' ' ∷ 'S' ∷ 'G' ∷ '_' ∷ ' ' ∷ []
  toList-SG_-spaces = refl

  toList-SG_ : toList "SG_" ≡ 'S' ∷ 'G' ∷ '_' ∷ []
  toList-SG_ = refl

  toList-colon : toList " : " ≡ ' ' ∷ ':' ∷ ' ' ∷ []
  toList-colon = refl

-- Advance position-by-position through a list of segments.  Mirrors
-- `buildTail` but accumulates `Position` instead of `List Char`, and
-- closes the dispatchers' "chained TailPositions" form into
-- `advancePositions <pre-tail-pos> tailBody-chars`.
private
  walkSegments : Position → List (List Char) → Position
  walkSegments pos []         = pos
  walkSegments pos (s ∷ segs) = walkSegments (advancePositions pos s) segs

  -- Structural induction lemma: pushing `advancePositions` through the
  -- buildTail chain equals walking segment-by-segment then advancing
  -- through the trail.  One induction covers all 14 segments.
  walkSegments-buildTail : ∀ (pos : Position) (segs : List (List Char))
                            (trail : List Char)
    → advancePositions pos (buildTail segs trail)
      ≡ advancePositions (walkSegments pos segs) trail
  walkSegments-buildTail pos []         trail = refl
  walkSegments-buildTail pos (s ∷ segs) trail =
    trans (advancePositions-++ pos s (buildTail segs trail))
          (walkSegments-buildTail (advancePositions pos s) segs trail)

  -- The walkSegments / TailPositions.pos₂₆ alignment.  Both walk the same
  -- 14 segments by the same characters: closed strings (`toList " : "`,
  -- `toList " ("`, `toList ") "`, `toList "] "`) reduce to cons literals,
  -- explicit-cons segments (`'|' ∷ blCs`, `'@' ∷ boCs`, etc.) match
  -- TailPositions' two-step `advancePosition+advancePositions` exactly.
  -- Reduces by `refl`.
  walkSegments-pos₂₆ : ∀ (pos : Position) (sig : DBCSignal) (fb : ℕ)
    → walkSegments pos (tailBody-segments fb sig)
      ≡ TailPositions.pos₂₆ pos sig fb
  walkSegments-pos₂₆ pos sig fb = refl

  -- Compose: `advancePositions pos tailBody-chars ≡ TailPositions.pos₂₇`.
  tail-pos-end-eq : ∀ (pos : Position) (sig : DBCSignal) (fb : ℕ)
    → advancePositions pos (tailBody-chars fb sig)
      ≡ TailPositions.pos₂₇ pos sig fb
  tail-pos-end-eq pos sig fb =
    trans (cong (advancePositions pos) (tailBody-via-buildTail fb sig))
      (trans (walkSegments-buildTail pos (tailBody-segments fb sig) ('\n' ∷ []))
        (cong (λ p → advancePosition p '\n')
              (walkSegments-pos₂₆ pos sig fb)))


-- ============================================================================
-- HEAD POSITION ALIGNMENT
-- ============================================================================

-- The 4-step head consumes `' ' ∷ toList "SG_" ++ ' ' ∷ nameChars`.  We
-- track positions through it explicitly (mirrors TailPositions structure
-- but for the head segment) so each dispatcher proof can compose head +
-- mux + tail position chains into a single `advancePositions pos emit`.
private
  module HeadPositions
      (pos : Position) (sig : DBCSignal) where
    nameCs : List Char
    nameCs = Identifier.name (DBCSignal.name sig)

    -- pos after each head step.
    posH₁  = advancePosition  pos     ' '            -- after parseWSOpt
    posH₂  = advancePositions posH₁  (toList "SG_")  -- after string "SG_"
    posH₃  = advancePosition  posH₂  ' '             -- after parseWS
    posH₄  = advancePositions posH₃  nameCs          -- after parseIdentifier


-- ============================================================================
-- parseMuxMarker LEFT-BRANCH FAILS ON tailBody-with-suffix
-- ============================================================================
--
-- For NotMux dispatchers, we owe `parseMuxMarker-NotMux-roundtrip` a
-- proof that `parseMuxMarker-left-branch pos (tailBody-with-suffix ...) ≡
-- nothing`.  Since `tailBody-with-suffix fb sig suffix` starts
-- `' ' ∷ ':' ∷ ' ' ∷ <sb> ++ ...`, parseWS consumes the leading ' ' and
-- then both `char 'M'` and `char 'm'` fail on ':' — the inner alt is
-- `nothing`, propagating through `*>`/`<|>` reductions.

private
  -- After parseWS consumes one leading ' ', we are looking at ':' ∷ rest.
  -- char 'M' on (':' ∷ rest) reduces to nothing (closed-mismatch).
  char-M-fails-on-colon : ∀ (pos : Position) (rest : List Char)
    → char 'M' pos (':' ∷ rest) ≡ nothing
  char-M-fails-on-colon _ _ = refl

  char-m-fails-on-colon : ∀ (pos : Position) (rest : List Char)
    → char 'm' pos (':' ∷ rest) ≡ nothing
  char-m-fails-on-colon _ _ = refl

-- The whole left branch of parseMuxMarker fails on input starting with
-- ' ' ∷ ':' ∷ rest (the post-name suffix in NotMux dispatchers).
parseMuxMarker-fails-on-colon-tail :
    ∀ (pos : Position) (rest : List Char)
  → parseMuxMarker-left-branch pos (' ' ∷ ':' ∷ rest) ≡ nothing
parseMuxMarker-fails-on-colon-tail pos rest =
  trans step-parseWS step-inner
  where
    pos1 : Position
    pos1 = advancePosition pos ' '

    inner : Parser MuxMarker
    inner = (char 'M' *> pure IsMux) <|>
            (char 'm' *> parseNatural >>= λ n →
              (char 'M' *> pure (BothMux n)) <|>
              pure (SelBy n))

    step-parseWS :
      parseMuxMarker-left-branch pos (' ' ∷ ':' ∷ rest)
      ≡ inner pos1 (':' ∷ rest)
    step-parseWS =
      bind-just-step parseWS (λ _ → inner)
        pos (' ' ∷ ':' ∷ rest)
        (' ' ∷ []) pos1 (':' ∷ rest)
        (parseWS-one-space pos (':' ∷ rest) (∷-stop refl))

    -- char 'M' fails on ':', then `(char 'M' *> pure IsMux) ≡ nothing`
    -- via bind-nothing; left-of-<|> nothing means the alt reduces to its
    -- right side, which itself fails since `char 'm'` also fails on ':'.
    open import Aletheia.DBC.TextParser.Properties.Primitives using
      (alt-right-nothing; bind-nothing)

    branch-M-fails : (char 'M' *> pure IsMux) pos1 (':' ∷ rest) ≡ nothing
    branch-M-fails =
      bind-nothing (char 'M') (λ _ → pure IsMux)
        pos1 (':' ∷ rest)
        (char-M-fails-on-colon pos1 rest)

    branch-m-fails :
        (char 'm' *> parseNatural >>= λ n →
          (char 'M' *> pure (BothMux n)) <|>
          pure (SelBy n)) pos1 (':' ∷ rest)
      ≡ nothing
    branch-m-fails =
      bind-nothing (char 'm')
        (λ _ → parseNatural >>= λ n →
          (char 'M' *> pure (BothMux n)) <|>
          pure (SelBy n))
        pos1 (':' ∷ rest)
        (char-m-fails-on-colon pos1 rest)

    step-inner : inner pos1 (':' ∷ rest) ≡ nothing
    step-inner =
      trans (alt-right-nothing
              (char 'M' *> pure IsMux)
              (char 'm' *> parseNatural >>= λ n →
                (char 'M' *> pure (BothMux n)) <|>
                pure (SelBy n))
              pos1 (':' ∷ rest)
              branch-M-fails)
            branch-m-fails


-- The same for tailBody-with-suffix: its head is exactly ' ' ∷ ':' ∷ ...,
-- so the left branch fails.  Phrased over the explicit shape so the
-- NotMux dispatcher can apply by direct rewrite.
parseMuxMarker-fails-on-tail-with-suffix :
    ∀ (pos : Position) (fb : ℕ) (sig : DBCSignal) (suffix : List Char)
  → parseMuxMarker-left-branch pos
      (tailBody-with-suffix fb sig suffix)
    ≡ nothing
parseMuxMarker-fails-on-tail-with-suffix pos fb sig suffix =
  -- tailBody-with-suffix fb sig suffix reduces (closed segments + cons
  -- prefix) to ' ' ∷ ':' ∷ ' ' ∷ <body-rest>.  Apply the colon-tail lemma.
  parseMuxMarker-fails-on-colon-tail pos
    (' ' ∷ TailPositions.sbCs pos sig fb ++ₗ '|' ∷ TailPositions.blCs pos sig fb
      ++ₗ '@' ∷ TailPositions.boCs pos sig fb
      ++ₗ           TailPositions.sgnCs pos sig fb
      ++ₗ toList " (" ++ₗ TailPositions.facCs pos sig fb
      ++ₗ ',' ∷ TailPositions.offCs pos sig fb
      ++ₗ toList ") "
      ++ₗ '[' ∷ TailPositions.minCs pos sig fb
      ++ₗ '|' ∷ TailPositions.maxCs pos sig fb
      ++ₗ toList "] "
      ++ₗ TailPositions.untCs pos sig fb
      ++ₗ ' ' ∷ TailPositions.rcvCs pos sig fb
      ++ₗ '\n' ∷ suffix)


-- ============================================================================
-- INPUT SHAPE — emitSignalLine-chars ++ suffix → tail-with-suffix form
-- ============================================================================
--
-- Compose `emitSignalLine-chars-shape` (which leaves a trailing
-- `tailBody-chars ++ suffix` sub-expression) with `tailBody-shape` (which
-- pushes the `++ suffix` into `tailBody-with-suffix`), giving a single
-- form the dispatchers consume directly.
private
  emitSignalLine-chars-with-suffix-shape :
      ∀ (master : Maybe (List Char)) (frameBytes : ℕ) (sig : DBCSignal)
        (suffix : List Char)
    → emitSignalLine-chars master frameBytes sig ++ₗ suffix
      ≡ toList " SG_ " ++ₗ Identifier.name (DBCSignal.name sig)
          ++ₗ emitMuxMarker-chars master (Identifier.name (DBCSignal.name sig))
                (DBCSignal.presence sig)
          ++ₗ tailBody-with-suffix frameBytes sig suffix
  emitSignalLine-chars-with-suffix-shape master frameBytes sig suffix =
    trans (emitSignalLine-chars-shape master frameBytes sig suffix)
      (cong (λ x → toList " SG_ " ++ₗ Identifier.name (DBCSignal.name sig)
                     ++ₗ emitMuxMarker-chars master (Identifier.name (DBCSignal.name sig))
                           (DBCSignal.presence sig)
                     ++ₗ x)
            (tailBody-shape frameBytes sig suffix))


-- ============================================================================
-- PER-DISPATCHER MAIN THEOREM — IsMux
-- ============================================================================
--
-- When the formatter emits `' ' ∷ 'M' ∷ []` for the mux marker (i.e. the
-- signal is the multiplexor master, `master ≡ just (signalNameStr sig)`
-- and `presence ≡ Always`), `parseSignalLine` recovers a `RawSignal` with
-- `muxMarker ≡ IsMux`.

parseSignalLine-roundtrip-IsMux :
    ∀ (pos : Position) (master : Maybe (List Char)) (fb : ℕ)
      (sig : DBCSignal) (suffix : List Char)
  → emitMuxMarker-chars master (Identifier.name (DBCSignal.name sig)) (DBCSignal.presence sig)
    ≡ toList " M"
  → SignalNameStop sig
  → All (λ r → ¬ Identifier.name r ≡ toList "Vector__XXX") (CanonicalReceivers.list (DBCSignal.receivers sig))
  → SuffixStops isHSpace
      (emitReceivers-chars (CanonicalReceivers.list (DBCSignal.receivers sig)) ++ₗ '\n' ∷ suffix)
  → SuffixStops isReceiverCont suffix
  → parseSignalLine pos
      (emitSignalLine-chars master fb sig ++ₗ suffix)
    ≡ just (mkResult (expectedRaw IsMux sig fb)
             (advancePositions pos (emitSignalLine-chars master fb sig))
             suffix)
parseSignalLine-roundtrip-IsMux pos master fb sig suffix
                                   mux-eq (c , cs , name-eq , c-non-hs)
                                   novecxxx hs-stop recv-cont-stop =
  trans (cong (parseSignalLine pos)
              (emitSignalLine-chars-with-suffix-shape master fb sig suffix))
    (trans (parseSignalLine-decompose pos input-shaped)
      (trans step-parseWSOpt
        (trans step-string-SG_
          (trans step-parseWS
            (trans step-parseIdent
              (trans step-parseMux
                (trans step-parseTail
                       step-pos-align)))))))
  where
    open HeadPositions pos sig
    open import Aletheia.DBC.TextParser.Properties.Primitives using
      (string-success; alt-right-nothing; bind-nothing)

    nameCs-shape : List Char
    nameCs-shape = Identifier.name (DBCSignal.name sig)

    muxCs : List Char
    muxCs = emitMuxMarker-chars master (Identifier.name (DBCSignal.name sig))
              (DBCSignal.presence sig)

    -- Right-associated input form after emitSignalLine-chars-with-suffix-shape.
    input-shaped : List Char
    input-shaped =
      toList " SG_ " ++ₗ nameCs-shape
        ++ₗ muxCs
        ++ₗ tailBody-with-suffix fb sig suffix

    -- Per-step intermediate inputs/positions.
    rest-after-WSOpt : List Char
    rest-after-WSOpt =
      toList "SG_" ++ₗ ' ' ∷ nameCs-shape
        ++ₗ muxCs
        ++ₗ tailBody-with-suffix fb sig suffix

    rest-after-string : List Char
    rest-after-string =
      ' ' ∷ nameCs-shape ++ₗ muxCs
        ++ₗ tailBody-with-suffix fb sig suffix

    rest-after-parseWS : List Char
    rest-after-parseWS =
      nameCs-shape ++ₗ muxCs
        ++ₗ tailBody-with-suffix fb sig suffix

    rest-after-name : List Char
    rest-after-name =
      muxCs ++ₗ tailBody-with-suffix fb sig suffix

    rest-after-mux : List Char
    rest-after-mux = tailBody-with-suffix fb sig suffix

    -- Continuations after each head bind.
    cont-after-WSOpt : List Char → Parser RawSignal
    cont-after-WSOpt _ =
      string "SG_" >>= λ _ →
      parseWS >>= λ _ →
      parseIdentifier >>= λ name →
      parseMuxMarker >>= λ mux →
      parseSignalTail name mux

    cont-after-string : String → Parser RawSignal
    cont-after-string _ =
      parseWS >>= λ _ →
      parseIdentifier >>= λ name →
      parseMuxMarker >>= λ mux →
      parseSignalTail name mux

    cont-after-parseWS : List Char → Parser RawSignal
    cont-after-parseWS _ =
      parseIdentifier >>= λ name →
      parseMuxMarker >>= λ mux →
      parseSignalTail name mux

    cont-after-name : Identifier → Parser RawSignal
    cont-after-name name =
      parseMuxMarker >>= λ mux →
      parseSignalTail name mux

    cont-after-mux : Identifier → MuxMarker → Parser RawSignal
    cont-after-mux name mux = parseSignalTail name mux

    -- Step 1: parseWSOpt consumes one leading space.
    step-parseWSOpt :
      (parseWSOpt >>= λ _ → string "SG_" >>= λ _ → parseWS >>= λ _ →
        parseIdentifier >>= λ name → parseMuxMarker >>= λ mux →
        parseSignalTail name mux) pos input-shaped
      ≡ cont-after-WSOpt (' ' ∷ []) posH₁ rest-after-WSOpt
    step-parseWSOpt =
      bind-just-step parseWSOpt cont-after-WSOpt
        pos input-shaped (' ' ∷ []) posH₁ rest-after-WSOpt
        (parseWSOpt-one-space pos rest-after-WSOpt (∷-stop refl))

    -- Step 2: string "SG_" matches.
    step-string-SG_ :
      cont-after-WSOpt (' ' ∷ []) posH₁ rest-after-WSOpt
      ≡ cont-after-string "SG_" posH₂ rest-after-string
    step-string-SG_ =
      bind-just-step (string "SG_") cont-after-string
        posH₁ rest-after-WSOpt
        "SG_" posH₂ rest-after-string
        (string-success posH₁ "SG_" rest-after-string)

    -- Step 3: parseWS consumes the post-SG_ space.  Stop witness needs
    -- `SuffixStops isHSpace (nameCs-shape ++ ...)` — provided by
    -- SignalNameStop's c-non-hs witness.
    name-cs-stop : SuffixStops isHSpace
                     (nameCs-shape ++ₗ muxCs
                       ++ₗ tailBody-with-suffix fb sig suffix)
    name-cs-stop
      rewrite name-eq = ∷-stop c-non-hs

    step-parseWS :
      cont-after-string "SG_" posH₂ rest-after-string
      ≡ cont-after-parseWS (' ' ∷ []) posH₃ rest-after-parseWS
    step-parseWS =
      bind-just-step parseWS cont-after-parseWS
        posH₂ rest-after-string
        (' ' ∷ []) posH₃ rest-after-parseWS
        (parseWS-one-space posH₂ rest-after-parseWS name-cs-stop)

    -- Step 4: parseIdentifier consumes nameCs-shape; suffix is
    -- muxCs ++ tail, whose first char is ' ' (mux always starts with
    -- ' '), not isIdentCont.  After mux-eq rewrite, muxCs ≡ ' ' ∷ 'M' ∷ [].
    rest-after-name-shape : List Char
    rest-after-name-shape = ' ' ∷ 'M' ∷ tailBody-with-suffix fb sig suffix

    rest-after-name-eq : rest-after-name ≡ rest-after-name-shape
    rest-after-name-eq rewrite mux-eq = refl

    rest-after-name-stop : SuffixStops isIdentCont rest-after-name
    rest-after-name-stop
      rewrite mux-eq = ∷-stop refl

    step-parseIdent :
      cont-after-parseWS (' ' ∷ []) posH₃ rest-after-parseWS
      ≡ cont-after-name (DBCSignal.name sig) posH₄ rest-after-name
    step-parseIdent =
      bind-just-step parseIdentifier cont-after-name
        posH₃ rest-after-parseWS
        (DBCSignal.name sig) posH₄ rest-after-name
        (parseIdentifier-roundtrip posH₃ (DBCSignal.name sig)
           rest-after-name rest-after-name-stop)

    -- Step 5: parseMuxMarker recovers IsMux.  Input is ' ' ∷ 'M' ∷ tail
    -- (after rewriting muxCs ≡ toList " M").
    rest-after-mux-shape : List Char
    rest-after-mux-shape = tailBody-with-suffix fb sig suffix

    posH₅ : Position
    posH₅ = advancePositions posH₄ muxCs

    posH₅-shape : posH₅ ≡ advancePositions posH₄ (toList " M")
    posH₅-shape = cong (advancePositions posH₄) mux-eq

    step-parseMux :
      cont-after-name (DBCSignal.name sig) posH₄ rest-after-name
      ≡ cont-after-mux (DBCSignal.name sig) IsMux posH₅ rest-after-mux-shape
    step-parseMux =
      subst (λ rest →
              cont-after-name (DBCSignal.name sig) posH₄ rest
              ≡ cont-after-mux (DBCSignal.name sig) IsMux posH₅
                  rest-after-mux-shape)
            (sym rest-after-name-eq)
        (subst (λ p →
                 cont-after-name (DBCSignal.name sig) posH₄ rest-after-name-shape
                 ≡ cont-after-mux (DBCSignal.name sig) IsMux p
                     rest-after-mux-shape)
               (sym posH₅-shape)
          (bind-just-step parseMuxMarker
             (λ mux → parseSignalTail (DBCSignal.name sig) mux)
             posH₄ rest-after-name-shape
             IsMux (advancePositions posH₄ (toList " M")) rest-after-mux-shape
             (parseMuxMarker-IsMux-roundtrip posH₄
                (tailBody-with-suffix fb sig suffix))))

    -- Step 6: parseSignalTail closes the 28-step body.
    step-parseTail :
      cont-after-mux (DBCSignal.name sig) IsMux posH₅ rest-after-mux-shape
      ≡ just (mkResult (expectedRaw IsMux sig fb)
               (TailPositions.pos₂₇ posH₅ sig fb) suffix)
    step-parseTail =
      parseSignalTail-roundtrip posH₅ (DBCSignal.name sig) IsMux
        sig fb suffix novecxxx hs-stop recv-cont-stop

    -- Step 7: position alignment.  TailPositions.pos₂₇ posH₅ sig fb
    -- ≡ advancePositions pos (emitSignalLine-chars master fb sig).
    pos-align :
      TailPositions.pos₂₇ posH₅ sig fb
      ≡ advancePositions pos (emitSignalLine-chars master fb sig)
    pos-align =
      trans (sym (tail-pos-end-eq posH₅ sig fb))
        (trans (sym (advancePositions-++ posH₄ muxCs (tailBody-chars fb sig)))
          (trans (sym (advancePositions-++ posH₃ nameCs-shape
                         (muxCs ++ₗ tailBody-chars fb sig)))
            (trans (sym (advancePositions-++ pos (toList " SG_ ")
                           (nameCs-shape ++ₗ muxCs ++ₗ tailBody-chars fb sig)))
              (cong (advancePositions pos)
                    (emit-eq-shape)))))
      where
        -- `emitSignalLine-chars master fb sig
        --  ≡ toList " SG_ " ++ nameCs ++ muxCs ++ tailBody-chars fb sig`
        -- — same shape as `emitSignalLine-chars-shape` but without the
        -- outer suffix; specialize by applying with `suffix ≡ []` then
        -- rewriting `xs ++ [] ≡ xs`.
        emit-eq-shape :
            toList " SG_ " ++ₗ nameCs-shape
              ++ₗ muxCs ++ₗ tailBody-chars fb sig
            ≡ emitSignalLine-chars master fb sig
        emit-eq-shape = sym (emit-shape-no-suffix)
          where
            open import Data.List.Properties renaming (++-identityʳ to ++ₗ-identityʳ)

            emit-shape-no-suffix :
                emitSignalLine-chars master fb sig
                ≡ toList " SG_ " ++ₗ nameCs-shape
                    ++ₗ muxCs ++ₗ tailBody-chars fb sig
            emit-shape-no-suffix =
              trans (sym (++ₗ-identityʳ (emitSignalLine-chars master fb sig)))
                (trans (emitSignalLine-chars-shape master fb sig [])
                  (cong (λ x → toList " SG_ " ++ₗ nameCs-shape
                                ++ₗ muxCs ++ₗ x)
                        (++ₗ-identityʳ (tailBody-chars fb sig))))

    step-pos-align :
      just (mkResult (expectedRaw IsMux sig fb)
              (TailPositions.pos₂₇ posH₅ sig fb) suffix)
      ≡ just (mkResult (expectedRaw IsMux sig fb)
              (advancePositions pos (emitSignalLine-chars master fb sig))
              suffix)
    step-pos-align =
      cong (λ p → just (mkResult (expectedRaw IsMux sig fb) p suffix))
           pos-align


-- ============================================================================
-- PER-DISPATCHER MAIN THEOREM — NotMux
-- ============================================================================
--
-- When the formatter emits no mux marker bytes (i.e. NoVectorXXX-empty
-- presence with no master, OR `presence ≡ Always` with `master ≡ just m`
-- and `signalNameStr sig ≢ m`), `parseSignalLine` recovers a `RawSignal`
-- with `muxMarker ≡ NotMux`.  The post-name input is `tailBody-with-
-- suffix`, which starts with `' ' ∷ ':' ∷ ...` — Layer 2's
-- `parseMuxMarker-NotMux-roundtrip` fires through the colon-tail failure
-- helper above.

parseSignalLine-roundtrip-NotMux :
    ∀ (pos : Position) (master : Maybe (List Char)) (fb : ℕ)
      (sig : DBCSignal) (suffix : List Char)
  → emitMuxMarker-chars master (Identifier.name (DBCSignal.name sig)) (DBCSignal.presence sig)
    ≡ []
  → SignalNameStop sig
  → All (λ r → ¬ Identifier.name r ≡ toList "Vector__XXX") (CanonicalReceivers.list (DBCSignal.receivers sig))
  → SuffixStops isHSpace
      (emitReceivers-chars (CanonicalReceivers.list (DBCSignal.receivers sig)) ++ₗ '\n' ∷ suffix)
  → SuffixStops isReceiverCont suffix
  → parseSignalLine pos
      (emitSignalLine-chars master fb sig ++ₗ suffix)
    ≡ just (mkResult (expectedRaw NotMux sig fb)
             (advancePositions pos (emitSignalLine-chars master fb sig))
             suffix)
parseSignalLine-roundtrip-NotMux pos master fb sig suffix
                                    mux-eq (c , cs , name-eq , c-non-hs)
                                    novecxxx hs-stop recv-cont-stop =
  trans (cong (parseSignalLine pos)
              (emitSignalLine-chars-with-suffix-shape master fb sig suffix))
    (trans (parseSignalLine-decompose pos input-shaped)
      (trans step-parseWSOpt
        (trans step-string-SG_
          (trans step-parseWS
            (trans step-parseIdent
              (trans step-parseMux
                (trans step-parseTail
                       step-pos-align)))))))
  where
    open HeadPositions pos sig
    open import Aletheia.DBC.TextParser.Properties.Primitives using
      (string-success)

    nameCs-shape : List Char
    nameCs-shape = Identifier.name (DBCSignal.name sig)

    muxCs : List Char
    muxCs = emitMuxMarker-chars master (Identifier.name (DBCSignal.name sig))
              (DBCSignal.presence sig)

    input-shaped : List Char
    input-shaped =
      toList " SG_ " ++ₗ nameCs-shape
        ++ₗ muxCs
        ++ₗ tailBody-with-suffix fb sig suffix

    rest-after-WSOpt : List Char
    rest-after-WSOpt =
      toList "SG_" ++ₗ ' ' ∷ nameCs-shape
        ++ₗ muxCs
        ++ₗ tailBody-with-suffix fb sig suffix

    rest-after-string : List Char
    rest-after-string =
      ' ' ∷ nameCs-shape ++ₗ muxCs
        ++ₗ tailBody-with-suffix fb sig suffix

    rest-after-parseWS : List Char
    rest-after-parseWS =
      nameCs-shape ++ₗ muxCs
        ++ₗ tailBody-with-suffix fb sig suffix

    rest-after-name : List Char
    rest-after-name =
      muxCs ++ₗ tailBody-with-suffix fb sig suffix

    rest-after-mux : List Char
    rest-after-mux = tailBody-with-suffix fb sig suffix

    cont-after-WSOpt : List Char → Parser RawSignal
    cont-after-WSOpt _ =
      string "SG_" >>= λ _ →
      parseWS >>= λ _ →
      parseIdentifier >>= λ name →
      parseMuxMarker >>= λ mux →
      parseSignalTail name mux

    cont-after-string : String → Parser RawSignal
    cont-after-string _ =
      parseWS >>= λ _ →
      parseIdentifier >>= λ name →
      parseMuxMarker >>= λ mux →
      parseSignalTail name mux

    cont-after-parseWS : List Char → Parser RawSignal
    cont-after-parseWS _ =
      parseIdentifier >>= λ name →
      parseMuxMarker >>= λ mux →
      parseSignalTail name mux

    cont-after-name : Identifier → Parser RawSignal
    cont-after-name name =
      parseMuxMarker >>= λ mux →
      parseSignalTail name mux

    cont-after-mux : Identifier → MuxMarker → Parser RawSignal
    cont-after-mux name mux = parseSignalTail name mux

    step-parseWSOpt :
      (parseWSOpt >>= λ _ → string "SG_" >>= λ _ → parseWS >>= λ _ →
        parseIdentifier >>= λ name → parseMuxMarker >>= λ mux →
        parseSignalTail name mux) pos input-shaped
      ≡ cont-after-WSOpt (' ' ∷ []) posH₁ rest-after-WSOpt
    step-parseWSOpt =
      bind-just-step parseWSOpt cont-after-WSOpt
        pos input-shaped (' ' ∷ []) posH₁ rest-after-WSOpt
        (parseWSOpt-one-space pos rest-after-WSOpt (∷-stop refl))

    step-string-SG_ :
      cont-after-WSOpt (' ' ∷ []) posH₁ rest-after-WSOpt
      ≡ cont-after-string "SG_" posH₂ rest-after-string
    step-string-SG_ =
      bind-just-step (string "SG_") cont-after-string
        posH₁ rest-after-WSOpt
        "SG_" posH₂ rest-after-string
        (string-success posH₁ "SG_" rest-after-string)

    name-cs-stop : SuffixStops isHSpace
                     (nameCs-shape ++ₗ muxCs
                       ++ₗ tailBody-with-suffix fb sig suffix)
    name-cs-stop
      rewrite name-eq = ∷-stop c-non-hs

    step-parseWS :
      cont-after-string "SG_" posH₂ rest-after-string
      ≡ cont-after-parseWS (' ' ∷ []) posH₃ rest-after-parseWS
    step-parseWS =
      bind-just-step parseWS cont-after-parseWS
        posH₂ rest-after-string
        (' ' ∷ []) posH₃ rest-after-parseWS
        (parseWS-one-space posH₂ rest-after-parseWS name-cs-stop)

    -- Step 4: parseIdentifier consumes nameCs-shape; suffix is muxCs ++
    -- tail.  Mux is empty (mux-eq), so suffix is `tailBody-with-suffix`,
    -- whose head is ' ', not isIdentCont.
    rest-after-name-shape : List Char
    rest-after-name-shape = tailBody-with-suffix fb sig suffix

    rest-after-name-eq : rest-after-name ≡ rest-after-name-shape
    rest-after-name-eq rewrite mux-eq = refl

    rest-after-name-stop : SuffixStops isIdentCont rest-after-name
    rest-after-name-stop
      rewrite mux-eq = ∷-stop refl

    step-parseIdent :
      cont-after-parseWS (' ' ∷ []) posH₃ rest-after-parseWS
      ≡ cont-after-name (DBCSignal.name sig) posH₄ rest-after-name
    step-parseIdent =
      bind-just-step parseIdentifier cont-after-name
        posH₃ rest-after-parseWS
        (DBCSignal.name sig) posH₄ rest-after-name
        (parseIdentifier-roundtrip posH₃ (DBCSignal.name sig)
           rest-after-name rest-after-name-stop)

    -- Step 5: parseMuxMarker recovers NotMux via the left-branch failure
    -- on the colon-tail.  After mux-eq rewrite, the input is
    -- `tailBody-with-suffix fb sig suffix` directly (mux ≡ []).
    posH₅ : Position
    posH₅ = advancePositions posH₄ muxCs

    posH₅-eq-posH₄ : posH₅ ≡ posH₄
    posH₅-eq-posH₄ = cong (advancePositions posH₄) mux-eq

    step-parseMux :
      cont-after-name (DBCSignal.name sig) posH₄ rest-after-name
      ≡ cont-after-mux (DBCSignal.name sig) NotMux posH₅
          (tailBody-with-suffix fb sig suffix)
    step-parseMux =
      subst (λ rest →
              cont-after-name (DBCSignal.name sig) posH₄ rest
              ≡ cont-after-mux (DBCSignal.name sig) NotMux posH₅
                  (tailBody-with-suffix fb sig suffix))
            (sym rest-after-name-eq)
        (subst (λ p →
                 cont-after-name (DBCSignal.name sig) posH₄
                   (tailBody-with-suffix fb sig suffix)
                 ≡ cont-after-mux (DBCSignal.name sig) NotMux p
                     (tailBody-with-suffix fb sig suffix))
               (sym posH₅-eq-posH₄)
          (bind-just-step parseMuxMarker
             (λ mux → parseSignalTail (DBCSignal.name sig) mux)
             posH₄ (tailBody-with-suffix fb sig suffix)
             NotMux posH₄ (tailBody-with-suffix fb sig suffix)
             (parseMuxMarker-NotMux-roundtrip posH₄
                (tailBody-with-suffix fb sig suffix)
                (parseMuxMarker-fails-on-tail-with-suffix posH₄ fb sig suffix))))

    step-parseTail :
      cont-after-mux (DBCSignal.name sig) NotMux posH₅
        (tailBody-with-suffix fb sig suffix)
      ≡ just (mkResult (expectedRaw NotMux sig fb)
               (TailPositions.pos₂₇ posH₅ sig fb) suffix)
    step-parseTail =
      parseSignalTail-roundtrip posH₅ (DBCSignal.name sig) NotMux
        sig fb suffix novecxxx hs-stop recv-cont-stop

    pos-align :
      TailPositions.pos₂₇ posH₅ sig fb
      ≡ advancePositions pos (emitSignalLine-chars master fb sig)
    pos-align =
      trans (sym (tail-pos-end-eq posH₅ sig fb))
        (trans (sym (advancePositions-++ posH₄ muxCs (tailBody-chars fb sig)))
          (trans (sym (advancePositions-++ posH₃ nameCs-shape
                         (muxCs ++ₗ tailBody-chars fb sig)))
            (trans (sym (advancePositions-++ pos (toList " SG_ ")
                           (nameCs-shape ++ₗ muxCs ++ₗ tailBody-chars fb sig)))
              (cong (advancePositions pos) emit-eq-shape))))
      where
        open import Data.List.Properties renaming (++-identityʳ to ++ₗ-identityʳ)

        emit-eq-shape :
            toList " SG_ " ++ₗ nameCs-shape
              ++ₗ muxCs ++ₗ tailBody-chars fb sig
            ≡ emitSignalLine-chars master fb sig
        emit-eq-shape = sym emit-shape-no-suffix
          where
            emit-shape-no-suffix :
                emitSignalLine-chars master fb sig
                ≡ toList " SG_ " ++ₗ nameCs-shape
                    ++ₗ muxCs ++ₗ tailBody-chars fb sig
            emit-shape-no-suffix =
              trans (sym (++ₗ-identityʳ (emitSignalLine-chars master fb sig)))
                (trans (emitSignalLine-chars-shape master fb sig [])
                  (cong (λ x → toList " SG_ " ++ₗ nameCs-shape
                                ++ₗ muxCs ++ₗ x)
                        (++ₗ-identityʳ (tailBody-chars fb sig))))

    step-pos-align :
      just (mkResult (expectedRaw NotMux sig fb)
              (TailPositions.pos₂₇ posH₅ sig fb) suffix)
      ≡ just (mkResult (expectedRaw NotMux sig fb)
              (advancePositions pos (emitSignalLine-chars master fb sig))
              suffix)
    step-pos-align =
      cong (λ p → just (mkResult (expectedRaw NotMux sig fb) p suffix))
           pos-align


-- ============================================================================
-- PER-DISPATCHER MAIN THEOREM — SelBy
-- ============================================================================
--
-- When the formatter emits `' ' ∷ 'm' ∷ showℕ-dec-chars v` for the mux
-- marker (i.e. `presence ≡ When _ (v ∷ [])`), `parseSignalLine` recovers
-- a `RawSignal` with `muxMarker ≡ SelBy v`.

parseSignalLine-roundtrip-SelBy :
    ∀ (pos : Position) (master : Maybe (List Char)) (fb : ℕ)
      (sig : DBCSignal) (v : ℕ) (suffix : List Char)
  → emitMuxMarker-chars master (Identifier.name (DBCSignal.name sig)) (DBCSignal.presence sig)
    ≡ toList " m" ++ₗ showℕ-dec-chars v
  → SignalNameStop sig
  → All (λ r → ¬ Identifier.name r ≡ toList "Vector__XXX") (CanonicalReceivers.list (DBCSignal.receivers sig))
  → SuffixStops isHSpace
      (emitReceivers-chars (CanonicalReceivers.list (DBCSignal.receivers sig)) ++ₗ '\n' ∷ suffix)
  → SuffixStops isReceiverCont suffix
  → parseSignalLine pos
      (emitSignalLine-chars master fb sig ++ₗ suffix)
    ≡ just (mkResult (expectedRaw (SelBy v) sig fb)
             (advancePositions pos (emitSignalLine-chars master fb sig))
             suffix)
parseSignalLine-roundtrip-SelBy pos master fb sig v suffix
                                   mux-eq (c , cs , name-eq , c-non-hs)
                                   novecxxx hs-stop recv-cont-stop =
  trans (cong (parseSignalLine pos)
              (emitSignalLine-chars-with-suffix-shape master fb sig suffix))
    (trans (parseSignalLine-decompose pos input-shaped)
      (trans step-parseWSOpt
        (trans step-string-SG_
          (trans step-parseWS
            (trans step-parseIdent
              (trans step-parseMux
                (trans step-parseTail
                       step-pos-align)))))))
  where
    open HeadPositions pos sig
    open import Aletheia.DBC.TextParser.Properties.Primitives using
      (string-success)

    nameCs-shape : List Char
    nameCs-shape = Identifier.name (DBCSignal.name sig)

    muxCs : List Char
    muxCs = emitMuxMarker-chars master (Identifier.name (DBCSignal.name sig))
              (DBCSignal.presence sig)

    input-shaped : List Char
    input-shaped =
      toList " SG_ " ++ₗ nameCs-shape
        ++ₗ muxCs
        ++ₗ tailBody-with-suffix fb sig suffix

    rest-after-WSOpt : List Char
    rest-after-WSOpt =
      toList "SG_" ++ₗ ' ' ∷ nameCs-shape
        ++ₗ muxCs
        ++ₗ tailBody-with-suffix fb sig suffix

    rest-after-string : List Char
    rest-after-string =
      ' ' ∷ nameCs-shape ++ₗ muxCs
        ++ₗ tailBody-with-suffix fb sig suffix

    rest-after-parseWS : List Char
    rest-after-parseWS =
      nameCs-shape ++ₗ muxCs
        ++ₗ tailBody-with-suffix fb sig suffix

    rest-after-name : List Char
    rest-after-name =
      muxCs ++ₗ tailBody-with-suffix fb sig suffix

    cont-after-WSOpt : List Char → Parser RawSignal
    cont-after-WSOpt _ =
      string "SG_" >>= λ _ →
      parseWS >>= λ _ →
      parseIdentifier >>= λ name →
      parseMuxMarker >>= λ mux →
      parseSignalTail name mux

    cont-after-string : String → Parser RawSignal
    cont-after-string _ =
      parseWS >>= λ _ →
      parseIdentifier >>= λ name →
      parseMuxMarker >>= λ mux →
      parseSignalTail name mux

    cont-after-parseWS : List Char → Parser RawSignal
    cont-after-parseWS _ =
      parseIdentifier >>= λ name →
      parseMuxMarker >>= λ mux →
      parseSignalTail name mux

    cont-after-name : Identifier → Parser RawSignal
    cont-after-name name =
      parseMuxMarker >>= λ mux →
      parseSignalTail name mux

    cont-after-mux : Identifier → MuxMarker → Parser RawSignal
    cont-after-mux name mux = parseSignalTail name mux

    step-parseWSOpt :
      (parseWSOpt >>= λ _ → string "SG_" >>= λ _ → parseWS >>= λ _ →
        parseIdentifier >>= λ name → parseMuxMarker >>= λ mux →
        parseSignalTail name mux) pos input-shaped
      ≡ cont-after-WSOpt (' ' ∷ []) posH₁ rest-after-WSOpt
    step-parseWSOpt =
      bind-just-step parseWSOpt cont-after-WSOpt
        pos input-shaped (' ' ∷ []) posH₁ rest-after-WSOpt
        (parseWSOpt-one-space pos rest-after-WSOpt (∷-stop refl))

    step-string-SG_ :
      cont-after-WSOpt (' ' ∷ []) posH₁ rest-after-WSOpt
      ≡ cont-after-string "SG_" posH₂ rest-after-string
    step-string-SG_ =
      bind-just-step (string "SG_") cont-after-string
        posH₁ rest-after-WSOpt
        "SG_" posH₂ rest-after-string
        (string-success posH₁ "SG_" rest-after-string)

    name-cs-stop : SuffixStops isHSpace
                     (nameCs-shape ++ₗ muxCs
                       ++ₗ tailBody-with-suffix fb sig suffix)
    name-cs-stop
      rewrite name-eq = ∷-stop c-non-hs

    step-parseWS :
      cont-after-string "SG_" posH₂ rest-after-string
      ≡ cont-after-parseWS (' ' ∷ []) posH₃ rest-after-parseWS
    step-parseWS =
      bind-just-step parseWS cont-after-parseWS
        posH₂ rest-after-string
        (' ' ∷ []) posH₃ rest-after-parseWS
        (parseWS-one-space posH₂ rest-after-parseWS name-cs-stop)

    -- Step 4: parseIdentifier; post-name suffix starts with ' ' (head of
    -- " m" ++ digits ++ ...), not isIdentCont.
    rest-after-name-stop : SuffixStops isIdentCont rest-after-name
    rest-after-name-stop
      rewrite mux-eq = ∷-stop refl

    step-parseIdent :
      cont-after-parseWS (' ' ∷ []) posH₃ rest-after-parseWS
      ≡ cont-after-name (DBCSignal.name sig) posH₄ rest-after-name
    step-parseIdent =
      bind-just-step parseIdentifier cont-after-name
        posH₃ rest-after-parseWS
        (DBCSignal.name sig) posH₄ rest-after-name
        (parseIdentifier-roundtrip posH₃ (DBCSignal.name sig)
           rest-after-name rest-after-name-stop)

    -- Step 5: parseMuxMarker recovers SelBy v via Layer 2 lemma.  Input
    -- shape after mux-eq rewrite: `' ' ∷ 'm' ∷ showℕ-dec-chars v ++ tail`.
    rest-after-name-shape : List Char
    rest-after-name-shape =
      ' ' ∷ 'm' ∷ showℕ-dec-chars v ++ₗ tailBody-with-suffix fb sig suffix

    rest-after-name-eq : rest-after-name ≡ rest-after-name-shape
    rest-after-name-eq
      rewrite mux-eq = sym (++ₗ-assoc (toList " m") (showℕ-dec-chars v)
                                       (tailBody-with-suffix fb sig suffix))

    -- SelBy preconditions: tail is a tail-with-suffix, head is ' '.
    digit-stop-tail : SuffixStops isDigit (tailBody-with-suffix fb sig suffix)
    digit-stop-tail = ∷-stop refl

    m-stop-tail : SuffixStops (λ ch → ch ≈ᵇ 'M') (tailBody-with-suffix fb sig suffix)
    m-stop-tail = ∷-stop refl

    posH₅ : Position
    posH₅ = advancePositions posH₄ muxCs

    posH₅-eq : posH₅
             ≡ advancePositions posH₄
                 (toList " m" ++ₗ showℕ-dec-chars v)
    posH₅-eq = cong (advancePositions posH₄) mux-eq

    step-parseMux :
      cont-after-name (DBCSignal.name sig) posH₄ rest-after-name
      ≡ cont-after-mux (DBCSignal.name sig) (SelBy v) posH₅
          (tailBody-with-suffix fb sig suffix)
    step-parseMux =
      subst (λ rest →
              cont-after-name (DBCSignal.name sig) posH₄ rest
              ≡ cont-after-mux (DBCSignal.name sig) (SelBy v) posH₅
                  (tailBody-with-suffix fb sig suffix))
            (sym rest-after-name-eq)
        (subst (λ p →
                 cont-after-name (DBCSignal.name sig) posH₄ rest-after-name-shape
                 ≡ cont-after-mux (DBCSignal.name sig) (SelBy v) p
                     (tailBody-with-suffix fb sig suffix))
               (sym posH₅-eq)
          (bind-just-step parseMuxMarker
             (λ mux → parseSignalTail (DBCSignal.name sig) mux)
             posH₄ rest-after-name-shape
             (SelBy v)
             (advancePositions posH₄ (toList " m" ++ₗ showℕ-dec-chars v))
             (tailBody-with-suffix fb sig suffix)
             (parseMuxMarker-SelBy-roundtrip posH₄ v
                (tailBody-with-suffix fb sig suffix)
                digit-stop-tail m-stop-tail)))

    step-parseTail :
      cont-after-mux (DBCSignal.name sig) (SelBy v) posH₅
        (tailBody-with-suffix fb sig suffix)
      ≡ just (mkResult (expectedRaw (SelBy v) sig fb)
               (TailPositions.pos₂₇ posH₅ sig fb) suffix)
    step-parseTail =
      parseSignalTail-roundtrip posH₅ (DBCSignal.name sig) (SelBy v)
        sig fb suffix novecxxx hs-stop recv-cont-stop

    pos-align :
      TailPositions.pos₂₇ posH₅ sig fb
      ≡ advancePositions pos (emitSignalLine-chars master fb sig)
    pos-align =
      trans (sym (tail-pos-end-eq posH₅ sig fb))
        (trans (sym (advancePositions-++ posH₄ muxCs (tailBody-chars fb sig)))
          (trans (sym (advancePositions-++ posH₃ nameCs-shape
                         (muxCs ++ₗ tailBody-chars fb sig)))
            (trans (sym (advancePositions-++ pos (toList " SG_ ")
                           (nameCs-shape ++ₗ muxCs ++ₗ tailBody-chars fb sig)))
              (cong (advancePositions pos) emit-eq-shape))))
      where
        open import Data.List.Properties renaming (++-identityʳ to ++ₗ-identityʳ)

        emit-eq-shape :
            toList " SG_ " ++ₗ nameCs-shape
              ++ₗ muxCs ++ₗ tailBody-chars fb sig
            ≡ emitSignalLine-chars master fb sig
        emit-eq-shape = sym emit-shape-no-suffix
          where
            emit-shape-no-suffix :
                emitSignalLine-chars master fb sig
                ≡ toList " SG_ " ++ₗ nameCs-shape
                    ++ₗ muxCs ++ₗ tailBody-chars fb sig
            emit-shape-no-suffix =
              trans (sym (++ₗ-identityʳ (emitSignalLine-chars master fb sig)))
                (trans (emitSignalLine-chars-shape master fb sig [])
                  (cong (λ x → toList " SG_ " ++ₗ nameCs-shape
                                ++ₗ muxCs ++ₗ x)
                        (++ₗ-identityʳ (tailBody-chars fb sig))))

    step-pos-align :
      just (mkResult (expectedRaw (SelBy v) sig fb)
              (TailPositions.pos₂₇ posH₅ sig fb) suffix)
      ≡ just (mkResult (expectedRaw (SelBy v) sig fb)
              (advancePositions pos (emitSignalLine-chars master fb sig))
              suffix)
    step-pos-align =
      cong (λ p → just (mkResult (expectedRaw (SelBy v) sig fb) p suffix))
           pos-align
