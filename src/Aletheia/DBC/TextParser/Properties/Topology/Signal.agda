{-# OPTIONS --without-K #-}

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
  (DBCSignal; SignalPresence; Always; When; signalNameStr)

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
    (toList (signalNameStr sig) ≡ c ∷ cs) × (isHSpace c ≡ false)


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
    (DBCSignal.receivers sig)


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
    nameChars = toList (signalNameStr sig)

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
    recvChars = emitReceivers-chars (DBCSignal.receivers sig)

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
      ∀ (master : Maybe String) (frameBytes : ℕ) (sig : DBCSignal)
        (suffix : List Char)
    → emitSignalLine-chars master frameBytes sig ++ₗ suffix
      ≡ toList " SG_ " ++ₗ nameChars sig frameBytes
          ++ₗ emitMuxMarker-chars master (signalNameStr sig)
                (DBCSignal.presence sig)
          ++ₗ tailBody-chars frameBytes sig ++ₗ suffix
  emitSignalLine-chars-shape master frameBytes sig suffix =
    trans (++ₗ-assoc (toList " SG_ ")
                     (toList (signalNameStr sig) ++ₗ
                      emitMuxMarker-chars master (signalNameStr sig)
                        (DBCSignal.presence sig) ++ₗ
                      tailBody-chars frameBytes sig)
                     suffix)
      (cong (toList " SG_ " ++ₗ_)
        (trans (++ₗ-assoc (toList (signalNameStr sig))
                          (emitMuxMarker-chars master (signalNameStr sig)
                             (DBCSignal.presence sig) ++ₗ
                           tailBody-chars frameBytes sig)
                          suffix)
          (cong (toList (signalNameStr sig) ++ₗ_)
            (++ₗ-assoc (emitMuxMarker-chars master (signalNameStr sig)
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
    rcvCs  = emitReceivers-chars (DBCSignal.receivers sig)

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
-- 3d.3 status: the per-MuxMarker-shape `parseSignalTail-roundtrip` and
-- per-dispatcher (`parseSignalLine-roundtrip-{NotMux,IsMux,SelBy}`)
-- theorems are scaffolded above (decompose lemma `parseSignalLine-decompose`
-- closes by `refl`; `parseSignalTail` definition + `expectedRaw` shape +
-- `tailBody-chars` shape + 28-step `TailPositions` cursor track all
-- compiled).  The 28-step bind-just-step chain that closes
-- `parseSignalTail-roundtrip` is the next sub-commit (see session-state.md).
-- ============================================================================
