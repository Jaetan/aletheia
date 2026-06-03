-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- B.3.d Layer 3 3d.8 — `parseMessage`-roundtrip composer.
--
-- Closes the BO_ block roundtrip: header (via DSL `messageHeaderFmt`) +
-- SG_ block (via 3d.6 `parseSignalLines-roundtrip`) + trailing newline +
-- `buildMessage` (via 3d.7 `resolveSignalList-roundtrip` + Layer-2
-- `buildCANId-rawCanIdℕ` + `bytesToValidDLC-roundtrip`).
--
-- Composition strategy: 4 `bind-just-step` calls peel off the four chained
-- binds in `parseMessage`'s body (post-3d.8 refactor: `parse
-- messageHeaderFmt >>= λ hdr → many parseSignalLine >>= λ raws → many
-- parseNewline *> buildMessage rawId msgName rawDlc msgSender raws`).
--
-- Bridge `emit-emitMessage-chars-eq` decomposes `emitMessage-chars msg`
-- into `emit messageHeaderFmt hdr ++ <SG_ block> ++ '\n' ∷ []`, exposing
-- the input shape that `roundtrip messageHeaderFmt` consumes; the SG_
-- block then matches `parseSignalLines-roundtrip`'s expected shape.
--
-- Layer 4 will lift this to `parseMessages-roundtrip` over a list of
-- DBCMessages via `manyHelper`-induction.
module Aletheia.DBC.TextParser.Properties.Topology.Message where

open import Data.Bool using (false)
open import Data.Char using (Char)
open import Data.List using (List; []; _∷_; foldr; length; map)
  renaming (_++_ to _++ₗ_)
open import Data.List.Properties renaming (++-assoc to ++ₗ-assoc)
open import Data.List.Relation.Unary.All as All using (All)
open import Data.List.Relation.Unary.AllPairs using (AllPairs)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; _≤_; _<_; s≤s; z≤n)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ)
open import Data.String using (toList)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; subst)

open import Aletheia.Parser.Combinators using
  (Parser; Position; mkResult; advancePosition; advancePositions;
   _>>=_; _*>_; many)
open import Aletheia.DBC.Identifier using (Identifier)
open import Aletheia.DBC.Types using
  (DBCMessage; DBCSignal; clearVds; clearVdsMsg)
open import Aletheia.CAN.DLC using (dlcBytes)
open import Aletheia.CAN.DLC.Properties using (bytesToValidDLC-roundtrip)

open import Aletheia.DBC.TextFormatter.Emitter using (showNat-chars)
open import Aletheia.DBC.TextFormatter.Topology using
  (emitSignalLine-chars; emitMessage-chars; findMuxMaster; rawCanIdℕ)

open import Aletheia.DBC.Formatter.WellFormed using
  (WellFormedSignal; PhysicallyValid)
open import Aletheia.DBC.Formatter.WellFormedText using
  (WellFormedTextPresence;
   MasterCoherent)

open import Aletheia.DBC.TextParser.Topology.Foundations using
  (RawSignal)
open import Aletheia.DBC.TextParser.Topology using
  (parseSignalLine; parseMessage; buildMessage)

open import Aletheia.DBC.TextParser.Lexer using (isHSpace; parseNewline)
open import Aletheia.DBC.TextParser.Format using
  (emit; parse; EmitsOK; ParseFailsAt; roundtrip)
  renaming ()
open import Aletheia.DBC.TextParser.Format.Message using (messageHeaderFmt)
open import Aletheia.DBC.TextParser.Format.SignalLine using (signalLineFmt)

open import Aletheia.DBC.TextParser.DecRatParse.Properties using
  (SuffixStops; ∷-stop; bind-just-step; advancePositions-++; showNat-chars-head)
open import Aletheia.DBC.TextParser.Properties.Attributes.Assign.Common using
  (digitChar-not-isHSpace)
open import Aletheia.DBC.TextParser.Properties.Preamble.Newline using
  (many-parseNewline-one-LF-stop;
   isNewlineStart)
open import Aletheia.DBC.TextParser.Properties.Comments.Comment using
  (buildCANId-rawCanIdℕ)
open import Aletheia.DBC.TextParser.Properties.Topology.SignalList using
  (SignalLineWF; expectedRawOfDBC; parseSignalLines-roundtrip)
open import Aletheia.DBC.TextParser.Properties.Topology.Resolve using
  (resolveSignalList-roundtrip)


-- ============================================================================
-- BRIDGE: emit messageHeaderFmt ≡ <header part of emitMessage-chars>
-- ============================================================================

-- DSL emit on `(rawId , msgName , rawDlc , msgSender)` reduces (through
-- nested `iso → withPrefix → withWS → pair`) to a flat string matching
-- the formatter's `toList "BO_ " ++ ... ++ '\n' ∷ []` shape.  Cons-on-`++`
-- and `[] ++ X` reductions collapse the intermediate `' ' ∷ []` and `[]`
-- emit slots; `toList "BO_" ++ ' ' ∷ [] ≡ toList "BO_ "` and `':' ∷ ' ' ∷
-- X ≡ toList ": " ++ X` close by Agda's primitive `toList` reducing on
-- closed string literals.
emit-messageHeaderFmt-flat :
    ∀ (rawId : ℕ) (msgName : Identifier) (rawDlc : ℕ) (msgSender : Identifier)
  → emit messageHeaderFmt (rawId , msgName , rawDlc , msgSender)
    ≡ toList "BO_ " ++ₗ showNat-chars rawId ++ₗ
      ' ' ∷ Identifier.name msgName ++ₗ
      toList ": " ++ₗ
      showNat-chars rawDlc ++ₗ
      ' ' ∷ Identifier.name msgSender ++ₗ
      '\n' ∷ []
emit-messageHeaderFmt-flat rawId msgName rawDlc msgSender = refl

-- ============================================================================
-- DECOMPOSE: emitMessage-chars msg ≡ emit messageHeaderFmt hdr ++ body
-- ============================================================================
--
-- Express the header chain as a `foldr` over a list of chunks.  Both
-- `emit messageHeaderFmt` and the prefix of `emitMessage-chars` reduce
-- (definitionally, via cons-on-`++` reduction) to `foldr _++_ tail
-- chunks`, with `tail = '\n' ∷ []` for the DSL form and `tail = '\n' ∷
-- body ++ '\n' ∷ []` for the formatter form.  A single `flatten-spine`
-- application bridges them, no hand-nested `trans/cong` ladder required.

private
  -- The 6 ordered atoms of the BO_ header line.  Two `' ' ∷ _` cons
  -- positions are kept as conses (definitionally equal to `(' ' ∷ []) ++
  -- _` through the `foldr _++_ tail` reduction below).
  headerChunks : ℕ → Identifier → ℕ → Identifier → List (List Char)
  headerChunks rawId msgName rawDlc msgSender =
    toList "BO_ "                          ∷
    showNat-chars rawId                    ∷
    (' ' ∷ Identifier.name msgName)        ∷
    toList ": "                            ∷
    showNat-chars rawDlc                   ∷
    (' ' ∷ Identifier.name msgSender)      ∷
    []

  -- Push a suffix `X` through a `_++_` spine of "chunks" terminated by
  -- `tail`: `(foldr _++_ tail xs) ++ X ≡ foldr _++_ (tail ++ X) xs`.
  -- One `++-assoc` per chunk, propagated through `cong (x ++_)`.  Avoids
  -- hand-piling deep `trans/cong` blocks; one structurally-recursive
  -- definition handles any chain length.
  flatten-spine : ∀ (xs : List (List Char)) (tail X : List Char)
    → (foldr _++ₗ_ tail xs) ++ₗ X ≡ foldr _++ₗ_ (tail ++ₗ X) xs
  flatten-spine []       tail X = refl
  flatten-spine (x ∷ xs) tail X =
    trans (++ₗ-assoc x (foldr _++ₗ_ tail xs) X)
          (cong (x ++ₗ_) (flatten-spine xs tail X))

-- DSL emit on `(rawId , msgName , rawDlc , msgSender)` reduces (through
-- nested `iso → withPrefix → withWS → pair`) to the same right-leaning
-- `foldr _++_ ('\n' ∷ []) chunks` shape as the parser-side spine.  Cons-
-- on-`++` and `[] ++ X = X` reductions collapse the `' ' ∷ []`/`[]`
-- emit slots; `toList "BO_" ++ ' ' ∷ X = toList "BO_ " ++ X` and `':' ∷
-- ' ' ∷ X = toList ": " ++ X` close by Agda's primitive `toList`
-- reducing on closed string literals.
emit-messageHeaderFmt-as-spine :
    ∀ (rawId : ℕ) (msgName : Identifier) (rawDlc : ℕ) (msgSender : Identifier)
  → emit messageHeaderFmt (rawId , msgName , rawDlc , msgSender)
    ≡ foldr _++ₗ_ ('\n' ∷ []) (headerChunks rawId msgName rawDlc msgSender)
emit-messageHeaderFmt-as-spine _ _ _ _ = refl

-- `emitMessage-chars msg`'s header part reduces (through right-leaning
-- `_++_` and cons-on-`++`) to `foldr _++_ ('\n' ∷ body ++ '\n' ∷ [])
-- chunks` directly — same spine, different terminator.
emitMessage-chars-as-spine :
    ∀ (msg : DBCMessage)
  → emitMessage-chars msg
    ≡ foldr _++ₗ_
        ('\n' ∷ foldr (λ s acc → emitSignalLine-chars
                                    (findMuxMaster (DBCMessage.signals msg))
                                    (dlcBytes (DBCMessage.dlc msg))
                                    s ++ₗ acc)
                      [] (DBCMessage.signals msg)
              ++ₗ '\n' ∷ [])
        (headerChunks (rawCanIdℕ (DBCMessage.id msg))
                       (DBCMessage.name msg)
                       (dlcBytes (DBCMessage.dlc msg))
                       (DBCMessage.sender msg))
emitMessage-chars-as-spine _ = refl

-- Top-level decompose: `emitMessage-chars msg ≡ emit messageHeaderFmt
-- hdr ++ body ++ '\n' ∷ []`.  Three steps: spine LHS, then via bridge
-- spine the RHS, then close via `flatten-spine`.  Cons-reduction
-- (`'\n' ∷ [] ++ Y ≡ '\n' ∷ Y`) is definitional.
emitMessage-chars-decompose :
    ∀ (msg : DBCMessage)
  → emitMessage-chars msg
    ≡ emit messageHeaderFmt
        (rawCanIdℕ (DBCMessage.id msg) ,
         DBCMessage.name msg ,
         dlcBytes (DBCMessage.dlc msg) ,
         DBCMessage.sender msg)
      ++ₗ
      foldr (λ s acc → emitSignalLine-chars
                          (findMuxMaster (DBCMessage.signals msg))
                          (dlcBytes (DBCMessage.dlc msg))
                          s ++ₗ acc)
            [] (DBCMessage.signals msg)
      ++ₗ '\n' ∷ []
emitMessage-chars-decompose msg =
  trans (emitMessage-chars-as-spine msg)
        (sym (trans
          (cong (_++ₗ tail-X)
                (emit-messageHeaderFmt-as-spine rawId msgName rawDlc msgSender))
          (flatten-spine
            (headerChunks rawId msgName rawDlc msgSender)
            ('\n' ∷ []) tail-X)))
  where
    rawId     = rawCanIdℕ (DBCMessage.id msg)
    msgName   = DBCMessage.name msg
    rawDlc    = dlcBytes (DBCMessage.dlc msg)
    msgSender = DBCMessage.sender msg
    master    = findMuxMaster (DBCMessage.signals msg)
    body      = foldr (λ s acc → emitSignalLine-chars master rawDlc s ++ₗ acc)
                      [] (DBCMessage.signals msg)
    tail-X    = body ++ₗ '\n' ∷ []


-- ============================================================================
-- buildMessage-roundtrip
-- ============================================================================

-- `buildMessage` succeeds with `just (clearVdsMsg msg)` when:
--   * `buildCANId (rawCanIdℕ msg.id) ≡ just msg.id` (Layer-2: canid-roundtrip)
--   * `bytesToValidDLC (dlcBytes msg.dlc) ≡ just msg.dlc` (Layer-2: dlc-roundtrip)
--   * `resolveSignalList (dlcBytes msg.dlc) (map ...) ≡ just (map clearVds msg.signals)`
--     (3d.7: resolveSignalList-roundtrip; E.9a returns the cleared form)
--   * `msg.senders ≡ []` (the formatter doesn't emit BO_TX_BU_; see
--     `WellFormedTextMessage`'s `senders-empty` field)
-- Three sequential `rewrite` steps thread the with-clauses; record-η
-- closes the final equation modulo `senders-empty`.
--
-- E.9a: `vds-eq` precondition removed; result is `clearVdsMsg msg`
-- because `resolveSignalList` returns `map clearVds msg.signals` and
-- the BO_/SG_ block carries no VAL_ data.  The Universal layer threads
-- `attachValueDescs ∘ collectFromMessages ≡ id` to recover the original
-- per-message vds.
buildMessage-roundtrip :
    ∀ (msg : DBCMessage) (pos : Position) (rest : List Char)
  → DBCMessage.senders msg ≡ []
  → dlcBytes (DBCMessage.dlc msg) ≤ 64
  → All WellFormedSignal (DBCMessage.signals msg)
  → All (PhysicallyValid (dlcBytes (DBCMessage.dlc msg))) (DBCMessage.signals msg)
  → All (λ s → WellFormedTextPresence (DBCSignal.presence s)) (DBCMessage.signals msg)
  → MasterCoherent (DBCMessage.signals msg)
  → buildMessage
      (rawCanIdℕ (DBCMessage.id msg))
      (DBCMessage.name msg)
      (dlcBytes (DBCMessage.dlc msg))
      (DBCMessage.sender msg)
      (map (expectedRawOfDBC
              (findMuxMaster (DBCMessage.signals msg))
              (dlcBytes (DBCMessage.dlc msg)))
           (DBCMessage.signals msg))
      pos rest
    ≡ just (mkResult (clearVdsMsg msg) pos rest)
buildMessage-roundtrip msg pos rest senders-empty fb≤64 wf-sigs pvs wfps mc
  rewrite buildCANId-rawCanIdℕ (DBCMessage.id msg)
        | bytesToValidDLC-roundtrip (DBCMessage.dlc msg)
        | resolveSignalList-roundtrip
            (dlcBytes (DBCMessage.dlc msg))
            (DBCMessage.signals msg) fb≤64 wf-sigs pvs wfps mc
  = cong (λ ss → just (mkResult
            (record { id      = DBCMessage.id msg
                    ; name    = DBCMessage.name msg
                    ; dlc     = DBCMessage.dlc msg
                    ; sender  = DBCMessage.sender msg
                    ; senders = ss
                    ; signals = map clearVds (DBCMessage.signals msg)
                    })
            pos rest))
         (sym senders-empty)


-- ============================================================================
-- DOMAIN PRECONDITION — first char of an Identifier name is non-hspace
-- ============================================================================

-- Used at the two `withWS ident`/`pair … ident` slots in `messageHeaderFmt`
-- where the parser/formatter boundary follows a single space and the next
-- chunk is an identifier name.  Owed by Layer 4 via the
-- `isIdentStart→¬isHSpace` bridge (every valid Identifier starts with
-- alpha or underscore, and neither is hspace); carried as a precondition
-- here so 3d.8 doesn't pull in Layer 4 obligations.
IdentHeadNonHSpace : Identifier → Set
IdentHeadNonHSpace i =
  Σ Char (λ c → Σ (List Char) (λ cs →
    (Identifier.name i ≡ c ∷ cs) × (isHSpace c ≡ false)))


-- ============================================================================
-- LOCAL DOUBLE-STOP HELPER
-- ============================================================================

-- `EmitsOK (pair nat F) (n , v) suffix`'s left slot has type `SuffixStops
-- isHSpace ((showNat-chars n ++ emit F v) ++ suffix)` — left-leaning at
-- the outer `++ suffix`.  `showNat-chars-head-stop-isHSpace` only
-- discharges the right-leaning form `showNat-chars n ++ rest`.  Bridge
-- via the `head` decomposition: get `showNat-chars n ≡ d ∷ tail` with
-- `isHSpace d ≡ false`, substitute, and the head reduces to `d` after
-- two `++` cons-reductions.  Mirrors η's `showNat-double-stop`.
private
  showNat-double-stop : ∀ (n : ℕ) (rest1 rest2 : List Char)
    → SuffixStops isHSpace ((showNat-chars n ++ₗ rest1) ++ₗ rest2)
  showNat-double-stop n rest1 rest2 with showNat-chars-head n
  ... | d , tail , _ , eq =
        subst (λ xs → SuffixStops isHSpace ((xs ++ₗ rest1) ++ₗ rest2))
              (sym eq)
              (∷-stop (digitChar-not-isHSpace d))

  -- Same shape for an identifier name's first char.  The
  -- `IdentHeadNonHSpace` precondition supplies `Identifier.name i ≡ c ∷
  -- cs` + `isHSpace c ≡ false`; substitute to expose the cons head, then
  -- discharge with `∷-stop`.
  ident-double-stop :
      ∀ (i : Identifier) (rest1 rest2 : List Char)
    → IdentHeadNonHSpace i
    → SuffixStops isHSpace ((Identifier.name i ++ₗ rest1) ++ₗ rest2)
  ident-double-stop i rest1 rest2 (c , cs , name-eq , c-non-hs) =
    subst (λ xs → SuffixStops isHSpace ((xs ++ₗ rest1) ++ₗ rest2))
          (sym name-eq)
          (∷-stop c-non-hs)


-- ============================================================================
-- EmitsOK ASSEMBLY
-- ============================================================================

-- Build `EmitsOK messageHeaderFmt hdr suffix` from the two
-- `IdentHeadNonHSpace` preconditions.  All other conditions reduce by
-- known-literal-head pattern matching:
--   * isHSpace stops at digit-heads (`showNat-chars-head-stop-isHSpace`).
--   * isDigit / isHSpace / isIdentCont stops at literal heads (' ', ':',
--     '\n') reduce via `∷-stop refl`.
--   * `newlineFmt`'s alt-fail (parse "\r\n" on '\n' ∷ ...) reduces via
--     `λ pos → refl`.
build-messageHeaderFmt-EmitsOK :
    ∀ (rawId : ℕ) (msgName : Identifier) (rawDlc : ℕ) (msgSender : Identifier)
      (suffix : List Char)
  → IdentHeadNonHSpace msgName
  → IdentHeadNonHSpace msgSender
  → EmitsOK messageHeaderFmt (rawId , msgName , rawDlc , msgSender) suffix
build-messageHeaderFmt-EmitsOK rawId msgName rawDlc msgSender suffix
                                 name-pre send-pre =
  -- 13-slot EmitsOK assembly.  Each line below is one condition; trivial
  -- ⊤ slots are written `tt`.  Helpers discharge the four non-trivial
  -- left-leaning slots; literal-head slots use `∷-stop refl`.
  tt ,                                                          -- literal "BO_"
  showNat-double-stop rawId _ _ ,                                -- ws after "BO_"
  ∷-stop refl ,                                                 -- nat rawId
  ident-double-stop msgName _ _ name-pre ,                       -- ws between rawId+name
  ∷-stop refl ,                                                 -- ident msgName
  ∷-stop refl ,                                                 -- wsOpt before ":"
  tt ,                                                          -- literal ":"
  showNat-double-stop rawDlc _ _ ,                               -- ws after ":"
  ∷-stop refl ,                                                 -- nat rawDlc
  ident-double-stop msgSender _ _ send-pre ,                     -- ws between rawDlc+sender
  ∷-stop refl ,                                                 -- ident msgSender
  ∷-stop refl ,                                                 -- wsOpt before "\n"
  tt ,                                                          -- literal "\n" (newlineFmt inner)
  λ _ → refl                                                    -- alt-fail "\r\n"


-- ============================================================================
-- messageHeader-roundtrip — slim wrapper over universal `roundtrip`
-- ============================================================================

messageHeader-roundtrip :
    ∀ (pos : Position) (rawId : ℕ) (msgName : Identifier) (rawDlc : ℕ)
      (msgSender : Identifier) (suffix : List Char)
  → IdentHeadNonHSpace msgName
  → IdentHeadNonHSpace msgSender
  → parse messageHeaderFmt pos
       (emit messageHeaderFmt (rawId , msgName , rawDlc , msgSender) ++ₗ suffix)
    ≡ just (mkResult (rawId , msgName , rawDlc , msgSender)
             (advancePositions pos
               (emit messageHeaderFmt (rawId , msgName , rawDlc , msgSender)))
             suffix)
messageHeader-roundtrip pos rawId msgName rawDlc msgSender suffix name-stop send-stop =
  roundtrip messageHeaderFmt pos
            (rawId , msgName , rawDlc , msgSender) suffix
            (build-messageHeaderFmt-EmitsOK rawId msgName rawDlc msgSender suffix
              name-stop send-stop)


-- ============================================================================
-- TOP-LEVEL: parseMessage-roundtrip
-- ============================================================================

-- Compose: rewrite input via `emitMessage-chars-decompose`, then peel
-- four binds (header, SG_ block, trailing newline, buildMessage) via
-- `bind-just-step`.  Each peel uses the corresponding sub-roundtrip
-- (`messageHeader-roundtrip`, `parseSignalLines-roundtrip`, `many-
-- parseNewline-one-LF-stop`, `buildMessage-roundtrip`).
parseMessage-roundtrip :
    ∀ (pos : Position) (msg : DBCMessage) (outer-suffix : List Char)
  → DBCMessage.senders msg ≡ []
  → dlcBytes (DBCMessage.dlc msg) ≤ 64
  → All WellFormedSignal (DBCMessage.signals msg)
  → All (PhysicallyValid (dlcBytes (DBCMessage.dlc msg))) (DBCMessage.signals msg)
  → All (λ s → WellFormedTextPresence (DBCSignal.presence s)) (DBCMessage.signals msg)
  → MasterCoherent (DBCMessage.signals msg)
  → IdentHeadNonHSpace (DBCMessage.name msg)
  → IdentHeadNonHSpace (DBCMessage.sender msg)
  → All SignalLineWF (DBCMessage.signals msg)
  → ParseFailsAt signalLineFmt ('\n' ∷ outer-suffix)
  → SuffixStops isNewlineStart outer-suffix
  → parseMessage pos (emitMessage-chars msg ++ₗ outer-suffix)
    ≡ just (mkResult (clearVdsMsg msg)
             (advancePositions pos (emitMessage-chars msg))
             outer-suffix)
parseMessage-roundtrip pos msg outer-suffix
    senders-empty fb≤64 wf-sigs pvs wfps mc
    name-pre send-pre item-pres tf nl-stop =
  trans
    (cong (λ inp → parseMessage pos inp)
          shape-bridge)
    (trans step-header
      (trans step-signals
        (trans step-newline
               step-build)))
  where
    rawId     = rawCanIdℕ (DBCMessage.id msg)
    msgName   = DBCMessage.name msg
    rawDlc    = dlcBytes (DBCMessage.dlc msg)
    msgSender = DBCMessage.sender msg
    sigs      = DBCMessage.signals msg
    master    = findMuxMaster sigs
    body      = foldr (λ s acc → emitSignalLine-chars master rawDlc s ++ₗ acc)
                      [] sigs
    raws      = map (expectedRawOfDBC master rawDlc) sigs

    -- Shape: input = emit messageHeaderFmt hdr ++ body ++ '\n' ∷ outer-suffix.
    -- After decompose: emitMessage-chars msg = emit messageHeaderFmt hdr
    -- ++ body ++ '\n' ∷ [], so concat with outer-suffix yields the
    -- expected form.
    shape-bridge : emitMessage-chars msg ++ₗ outer-suffix
                 ≡ emit messageHeaderFmt (rawId , msgName , rawDlc , msgSender)
                   ++ₗ body ++ₗ '\n' ∷ outer-suffix
    shape-bridge =
      trans (cong (_++ₗ outer-suffix) (emitMessage-chars-decompose msg))
            (trans (++ₗ-assoc
                     (emit messageHeaderFmt (rawId , msgName , rawDlc , msgSender))
                     (body ++ₗ '\n' ∷ []) outer-suffix)
                   (cong (emit messageHeaderFmt (rawId , msgName , rawDlc , msgSender) ++ₗ_)
                         (++ₗ-assoc body ('\n' ∷ []) outer-suffix)))

    -- Positions through the chain.
    pos-after-hdr  = advancePositions pos
                       (emit messageHeaderFmt (rawId , msgName , rawDlc , msgSender))
    pos-after-sigs = advancePositions pos-after-hdr body
    pos-after-nl   = advancePosition  pos-after-sigs '\n'

    -- Continuations.
    cont-after-hdr : (ℕ × Identifier × ℕ × Identifier) → Parser DBCMessage
    cont-after-hdr hdr =
      let r = proj₁ hdr
          n = proj₁ (proj₂ hdr)
          d = proj₁ (proj₂ (proj₂ hdr))
          s = proj₂ (proj₂ (proj₂ hdr))
      in many parseSignalLine >>= λ rs →
         many parseNewline *>
         buildMessage r n d s rs

    cont-after-sigs : List RawSignal → Parser DBCMessage
    cont-after-sigs rs =
      many parseNewline *>
      buildMessage rawId msgName rawDlc msgSender rs

    cont-after-nl : List Char → Parser DBCMessage
    cont-after-nl _ =
      buildMessage rawId msgName rawDlc msgSender raws

    -- Step 1: peel parse messageHeaderFmt via universal roundtrip.
    step-header :
      parseMessage pos
        (emit messageHeaderFmt (rawId , msgName , rawDlc , msgSender)
         ++ₗ body ++ₗ '\n' ∷ outer-suffix)
      ≡ cont-after-hdr (rawId , msgName , rawDlc , msgSender)
          pos-after-hdr (body ++ₗ '\n' ∷ outer-suffix)
    step-header =
      bind-just-step (parse messageHeaderFmt) cont-after-hdr
        pos
        (emit messageHeaderFmt (rawId , msgName , rawDlc , msgSender)
         ++ₗ body ++ₗ '\n' ∷ outer-suffix)
        (rawId , msgName , rawDlc , msgSender)
        pos-after-hdr
        (body ++ₗ '\n' ∷ outer-suffix)
        (messageHeader-roundtrip pos rawId msgName rawDlc msgSender
          (body ++ₗ '\n' ∷ outer-suffix) name-pre send-pre)

    -- Step 2: peel many parseSignalLine via 3d.6.
    step-signals :
      cont-after-hdr (rawId , msgName , rawDlc , msgSender)
        pos-after-hdr (body ++ₗ '\n' ∷ outer-suffix)
      ≡ cont-after-sigs raws pos-after-sigs ('\n' ∷ outer-suffix)
    step-signals =
      bind-just-step (many parseSignalLine) cont-after-sigs
        pos-after-hdr
        (body ++ₗ '\n' ∷ outer-suffix)
        raws pos-after-sigs ('\n' ∷ outer-suffix)
        (parseSignalLines-roundtrip pos-after-hdr master rawDlc sigs
          ('\n' ∷ outer-suffix) item-pres tf (∷-stop refl))

    -- Step 3: peel many parseNewline (consumes single '\n').
    step-newline :
      cont-after-sigs raws pos-after-sigs ('\n' ∷ outer-suffix)
      ≡ cont-after-nl ('\n' ∷ []) pos-after-nl outer-suffix
    step-newline =
      bind-just-step (many parseNewline) cont-after-nl
        pos-after-sigs ('\n' ∷ outer-suffix)
        ('\n' ∷ []) pos-after-nl outer-suffix
        (many-parseNewline-one-LF-stop pos-after-sigs outer-suffix
          (length outer-suffix) nl-stop)

    -- Step 4: apply buildMessage-roundtrip; bridge the goal's position
    -- to the canonical `advancePositions pos (emitMessage-chars msg)`
    -- form (so Layer 4's `parseMessages-roundtrip` doesn't need a
    -- per-message bridge).  Two-stage chain:
    --   (a) Two `advancePositions-++` applications collapse
    --       `pos-after-nl` to `advancePositions pos (hdr ++ body ++ '\n' ∷ [])`.
    --   (b) One `cong (advancePositions pos)` step with
    --       `sym (emitMessage-chars-decompose msg)` bridges to the
    --       canonical `emitMessage-chars msg` form.
    pos-eq : pos-after-nl ≡ advancePositions pos (emitMessage-chars msg)
    pos-eq =
      trans
        (sym (trans
          (advancePositions-++ pos
             (emit messageHeaderFmt (rawId , msgName , rawDlc , msgSender))
             (body ++ₗ '\n' ∷ []))
          (advancePositions-++
             (advancePositions pos
               (emit messageHeaderFmt (rawId , msgName , rawDlc , msgSender)))
             body ('\n' ∷ []))))
        (cong (advancePositions pos)
              (sym (emitMessage-chars-decompose msg)))

    step-build :
      cont-after-nl ('\n' ∷ []) pos-after-nl outer-suffix
      ≡ just (mkResult (clearVdsMsg msg)
                (advancePositions pos (emitMessage-chars msg))
                outer-suffix)
    step-build =
      trans (buildMessage-roundtrip msg pos-after-nl outer-suffix
              senders-empty fb≤64 wf-sigs pvs wfps mc)
            (cong (λ p → just (mkResult (clearVdsMsg msg) p outer-suffix)) pos-eq)


-- ============================================================================
-- LIST-LEVEL ROUNDTRIP — `many parseMessage` over a BO_ block
-- ============================================================================

-- All per-message preconditions consumed by `parseMessage-roundtrip`.
-- Bundled so the polymorphic `many-η-roundtrip` helper sees a single
-- `Stop : DBCMessage → Set`.
--
-- E.9a (2026-05-07): `vds-empty` removed.  The text round-trip's
-- per-message claim now reads `parseMessage … ≡ just (mkResult
-- (clearVdsMsg msg) … …)`, NOT `mkResult msg`, since `buildSignal`
-- hardcodes `valueDescriptions = []` and the parser cannot recover the
-- field from the BO_/SG_ block alone (VAL_ entries arrive at the
-- DBC level via `TVD` top-stmts).  The Universal layer threads
-- `attachValueDescs ∘ collectFromMessages ≡ id` (Refine bridge) post
-- buildDBC to recover the original messages from the cleared form.
record MessageWF (msg : DBCMessage) : Set where
  field
    senders-empty : DBCMessage.senders msg ≡ []
    fb-bound      : dlcBytes (DBCMessage.dlc msg) ≤ 64
    wf-sigs       : All WellFormedSignal (DBCMessage.signals msg)
    pvs           : All (PhysicallyValid (dlcBytes (DBCMessage.dlc msg)))
                       (DBCMessage.signals msg)
    wfps          : All (λ s → WellFormedTextPresence (DBCSignal.presence s))
                       (DBCMessage.signals msg)
    mc            : MasterCoherent (DBCMessage.signals msg)
    name-pre      : IdentHeadNonHSpace (DBCMessage.name msg)
    send-pre      : IdentHeadNonHSpace (DBCMessage.sender msg)
    item-pres     : All SignalLineWF (DBCMessage.signals msg)
    -- E.6: signal-name uniqueness within this message.  Required by
    -- `attachValueDescs ∘ collectFromMessages ≡ id` (the inverse-bridge
    -- in `Properties.Aggregator.Refine.ValueDescriptions`): two distinct
    -- signals with the same name would have their per-signal VAL_
    -- entries collapse onto whichever signal `lookup-vd` finds first,
    -- breaking the round-trip.  Validator's CHECK 23 enforces this at
    -- DBC-load time.
    sig-names-unique : AllPairs _≢_ (map DBCSignal.name (DBCMessage.signals msg))


-- `parse signalLineFmt pos ('\n' ∷ s) ≡ nothing` for any `s, pos` —
-- `signalLineFmt` opens with `withWSCanonOne (withPrefix "SG_" …)` and
-- the `withPrefix "SG_"` consumer rejects `'\n'` immediately after the
-- (zero-or-more) leading whitespace step.  Closes by Agda reduction —
-- both `withWSCanonOne` (zero-iteration kleene) and `withPrefix` reduce
-- on the literal `'\n'` cons.
signalLineFmt-fails-on-newline :
    ∀ (pos : Position) (s : List Char)
  → parse signalLineFmt pos ('\n' ∷ s) ≡ nothing
signalLineFmt-fails-on-newline _ _ = refl


-- `0 < length (emitMessage-chars msg)` — the literal `"BO_ "` prefix
-- gives a 4-byte head.
emitMessage-chars-nonzero : ∀ (msg : DBCMessage)
  → 0 < length (emitMessage-chars msg)
emitMessage-chars-nonzero _ = s≤s z≤n


-- Head of `emitMessage-chars msg` is `'B'` — not a newline-start.
emitMessage-chars-head-not-newline :
    ∀ (msg : DBCMessage) (suffix : List Char)
  → SuffixStops isNewlineStart (emitMessage-chars msg ++ₗ suffix)
emitMessage-chars-head-not-newline _ _ = ∷-stop refl


-- Wrapper: same shape as `parseMessage-roundtrip` but with all per-
-- message preconditions bundled into `MessageWF` and the
-- `ParseFailsAt signalLineFmt ('\n' ∷ outer-suffix)` precondition
-- discharged universally via `signalLineFmt-fails-on-newline`.  The
-- polymorphic helper sees only `Stop = MessageWF` + the standard
-- `SuffixStops isNewlineStart` outer condition.
--
-- E.9a: result is `mkResult (clearVdsMsg msg) …`; the Universal
-- threads `attachValueDescs ∘ collectFromMessages ≡ id` post-parse to
-- recover the original.
parseMessage-roundtrip-bundled :
    ∀ (pos : Position) (msg : DBCMessage) (outer-suffix : List Char)
  → MessageWF msg
  → SuffixStops isNewlineStart outer-suffix
  → parseMessage pos (emitMessage-chars msg ++ₗ outer-suffix)
    ≡ just (mkResult (clearVdsMsg msg)
             (advancePositions pos (emitMessage-chars msg))
             outer-suffix)
parseMessage-roundtrip-bundled pos msg outer-suffix wf nl-stop =
  parseMessage-roundtrip pos msg outer-suffix
    (MessageWF.senders-empty wf)
    (MessageWF.fb-bound      wf)
    (MessageWF.wf-sigs       wf)
    (MessageWF.pvs           wf)
    (MessageWF.wfps          wf)
    (MessageWF.mc            wf)
    (MessageWF.name-pre      wf)
    (MessageWF.send-pre      wf)
    (MessageWF.item-pres     wf)
    (λ pos₁ → signalLineFmt-fails-on-newline pos₁ outer-suffix)
    nl-stop


-- E.9a: result list is `map clearVdsMsg msgs`, not `msgs`.  Per-element
-- `parseMessage-roundtrip-bundled` emits `mkResult (clearVdsMsg msg) …`,
-- so the polymorphic helper `many-η-roundtrip-with-lift` (with `L =
-- clearVdsMsg`) lifts it to the list level.  The Universal threads
-- `attachValueDescs ∘ collectFromMessages ≡ id` post-buildDBC to recover
-- the original.
parseMessages-roundtrip :
    ∀ (pos : Position) (msgs : List DBCMessage) (outer-suffix : List Char)
  → All MessageWF msgs
  → SuffixStops isNewlineStart outer-suffix
  → (∀ (pos' : Position) → parseMessage pos' outer-suffix ≡ nothing)
  → many parseMessage pos
      (foldr (λ m acc → emitMessage-chars m ++ₗ acc) [] msgs ++ₗ outer-suffix)
    ≡ just (mkResult (map clearVdsMsg msgs)
             (advancePositions pos
               (foldr (λ m acc → emitMessage-chars m ++ₗ acc) [] msgs))
             outer-suffix)
parseMessages-roundtrip pos msgs outer-suffix msgs-stops os pf =
  many-η-roundtrip-with-lift
    parseMessage
    emitMessage-chars
    MessageWF
    clearVdsMsg
    parseMessage-roundtrip-bundled
    emitMessage-chars-nonzero
    emitMessage-chars-head-not-newline
    pos msgs outer-suffix msgs-stops os pf
  where
    open import Aletheia.DBC.TextParser.Properties.ManyRoundtrip using
      (many-η-roundtrip-with-lift)

