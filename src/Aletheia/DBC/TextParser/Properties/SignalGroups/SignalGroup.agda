{-# OPTIONS --safe --without-K #-}

-- B.3.d Layer 4a — slim `parseSignalGroup-roundtrip` derived from the
-- universal Format DSL roundtrip.
--
-- Layer 3 carry-over: `SignalGroup` was the last per-line construct
-- without a Format DSL form.  The slim is shaped identically to
-- `parseValueTable-roundtrip` and `parseEnvVar-roundtrip`.
--
-- Wrap-shaped: `parseSignalGroup = parse signalGroupFmt >>= λ sg →
-- many parseNewline >>= λ _ → pure sg` (in `TextParser.SignalGroups`).
-- Roundtrip decomposes into:
--   1. Bridge `emit signalGroupFmt sg ≡ emitSignalGroup-chars sg`
--      (a structural induction over the signal list folding `concatMap`
--      to `foldr` — same shape as `Properties/ValueTables/ValueTable`'s
--      `emit-many-eq-foldr`).
--   2. The universal `parseSignalGroup-format-roundtrip` (from
--      `Format.SignalGroup`).
--   3. The trailing `many parseNewline` consuming zero from suffix
--      (via `manyHelper-parseNewline-exhaust` + the existing
--      `SuffixStops isNewlineStart suffix` precondition).
--
-- The two preconditions (`SignalGroupNameStop` + `All SigNameStop` over
-- `signals`) migrate upstream to `Format.SignalGroup`; this module
-- re-exports them for source compatibility with the section facade.
module Aletheia.DBC.TextParser.Properties.SignalGroups.SignalGroup where

open import Data.Char using (Char)
open import Data.Nat using (_<_; s≤s; z≤n)
open import Data.List using (List; []; _∷_; foldr; concatMap; length; map)
  renaming (_++_ to _++ₗ_)
open import Data.List.Properties using () renaming (++-assoc to ++ₗ-assoc)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong)

open import Aletheia.Parser.Combinators using
  (Parser; Position; ParseResult; mkResult; advancePositions;
   pure; _>>=_; many)
open import Aletheia.DBC.Identifier using (Identifier)
open import Aletheia.DBC.Types using (SignalGroup)
open import Aletheia.DBC.TextParser.Lexer using (parseNewline)
open import Aletheia.DBC.TextParser.SignalGroups using (parseSignalGroup)
open import Aletheia.DBC.TextFormatter.SignalGroups
  using (emitSignalGroup-chars; emitSignalNames-chars)

open import Aletheia.DBC.TextParser.DecRatParse.Properties using
  (SuffixStops; bind-just-step; ∷-stop)
open import Aletheia.DBC.TextParser.Properties.Preamble.Newline using
  (isNewlineStart; manyHelper-parseNewline-exhaust)

open import Aletheia.DBC.TextParser.Format using
  (Format; emit; parse)
  renaming (many to manyF)
open import Aletheia.DBC.TextParser.Format.SignalGroup as FmtSG using
  (signalGroupFmt; sigEntry-format; parseSignalGroup-format-roundtrip)

-- ============================================================================
-- RE-EXPORTS — `SignalGroupNameStop` / `SigNameStop` migrated to `Format.SignalGroup`
-- ============================================================================

open import Aletheia.DBC.TextParser.Format.SignalGroup public
  using (SignalGroupNameStop; SigNameStop)

-- ============================================================================
-- BRIDGE: DSL emit ≡ existing emitSignalGroup-chars
-- ============================================================================

-- Per-entry: `emit sigEntry-format i = ' ' ∷ Identifier.name i`,
-- definitionally equal to the body of `emitSignalNames-chars`'s foldr.
emit-sigEntry-format-eq : ∀ (i : Identifier)
  → emit sigEntry-format i ≡ ' ' ∷ Identifier.name i
emit-sigEntry-format-eq i = refl

-- Signal-list fold: `emit (many sigEntry-format) sigs ++ terminator
-- ≡ foldr (λ s acc → ' ' ∷ Identifier.name s ++ acc) terminator sigs`.
-- Closes by structural induction; the cons case unfolds `concatMap` then
-- re-associates `++` to push `terminator` inside the recursion.
emit-many-eq-foldr : ∀ (sigs : List Identifier) (terminator : List Char)
  → emit (manyF sigEntry-format) sigs ++ₗ terminator
    ≡ foldr (λ s acc → ' ' ∷ Identifier.name s ++ₗ acc) terminator sigs
emit-many-eq-foldr [] terminator = refl
emit-many-eq-foldr (i ∷ rest) terminator =
  trans (++ₗ-assoc (emit sigEntry-format i)
                    (emit (manyF sigEntry-format) rest)
                    terminator)
        (cong (emit sigEntry-format i ++ₗ_)
              (emit-many-eq-foldr rest terminator))

-- foldr-distributivity: foldr g T xs ≡ foldr g [] xs ++ T, where g
-- prepends a fixed prefix per element.  Closes the "terminator inside
-- foldr" vs "terminator outside foldr" mismatch between the DSL emit
-- (terminator inside) and the existing `emitSignalGroup-chars` (which
-- structures it as `emitSignalNames-chars sigs ++ toList ";\n"` with
-- `[]` inside the foldr).  Standard structural induction with one
-- `++-assoc` step on the cons case.
foldr-emit-distrib-append : ∀ (sigs : List Identifier) (terminator : List Char)
  → foldr (λ s acc → ' ' ∷ Identifier.name s ++ₗ acc) terminator sigs
    ≡ foldr (λ s acc → ' ' ∷ Identifier.name s ++ₗ acc) [] sigs ++ₗ terminator
foldr-emit-distrib-append [] terminator = refl
foldr-emit-distrib-append (i ∷ rest) terminator =
  trans
    (cong (λ x → ' ' ∷ Identifier.name i ++ₗ x)
          (foldr-emit-distrib-append rest terminator))
    (cong (' ' ∷_)
          (sym (++ₗ-assoc (Identifier.name i)
                          (foldr (λ s acc → ' ' ∷ Identifier.name s ++ₗ acc)
                                 [] rest)
                          terminator)))

-- Top-level bridge: full `emit signalGroupFmt sg ≡ emitSignalGroup-chars sg`.
-- LHS reduces (through nested isos) to:
--   "SIG_GROUP_" ++ ' ' ∷ '0' ∷ ' ' ∷ name ++ ' ' ∷ '1' ∷ ' ' ∷ ':' ∷
--   <foldr-with-';\n'-terminator>
-- RHS reduces to:
--   toList "SIG_GROUP_ 0 " ++ name ++ toList " 1 :" ++ <foldr-with-[]> ++ toList ";\n"
-- The literal-prefix reductions match definitionally; the foldr-vs-
-- foldr++term mismatch is bridged by `foldr-emit-distrib-append`.
emit-signalGroupFmt-eq-emitSignalGroup-chars : ∀ (sg : SignalGroup)
  → emit signalGroupFmt sg ≡ emitSignalGroup-chars sg
emit-signalGroupFmt-eq-emitSignalGroup-chars sg =
  trans (cong (λ x → 'S' ∷ 'I' ∷ 'G' ∷ '_' ∷ 'G' ∷ 'R' ∷ 'O' ∷ 'U' ∷ 'P' ∷ '_'
                     ∷ ' ' ∷ '0' ∷ ' ' ∷ Identifier.name (SignalGroup.name sg)
                     ++ₗ ' ' ∷ '1' ∷ ' ' ∷ ':' ∷ x)
              (emit-many-eq-foldr (SignalGroup.signals sg) (';' ∷ '\n' ∷ [])))
        (cong (λ x → 'S' ∷ 'I' ∷ 'G' ∷ '_' ∷ 'G' ∷ 'R' ∷ 'O' ∷ 'U' ∷ 'P' ∷ '_'
                     ∷ ' ' ∷ '0' ∷ ' ' ∷ Identifier.name (SignalGroup.name sg)
                     ++ₗ ' ' ∷ '1' ∷ ' ' ∷ ':' ∷ x)
              (foldr-emit-distrib-append (SignalGroup.signals sg) (';' ∷ '\n' ∷ [])))

-- ============================================================================
-- SLIM `parseSignalGroup-roundtrip`
-- ============================================================================

-- Wrap-shaped: `parseSignalGroup = parse signalGroupFmt >>= λ sg →
-- many parseNewline >>= λ _ → pure sg`.  Composition decomposes into:
--
--   1. `parse signalGroupFmt pos (emit signalGroupFmt sg ++ suffix)` via
--      `parseSignalGroup-format-roundtrip`.
--   2. `many parseNewline pos' suffix` returning `[]`-no-consume via
--      `manyHelper-parseNewline-exhaust` + `nl-stop` precondition.
--   3. `pure sg` returns the input value at the resulting position.
--
-- `subst` on input/output positions converts between `emit signalGroupFmt
-- sg` and `emitSignalGroup-chars sg` via the bridge.
parseSignalGroup-roundtrip :
    ∀ (pos : Position) (sg : SignalGroup) (suffix : List Char)
  → SignalGroupNameStop sg
  → All SigNameStop (SignalGroup.signals sg)
  → SuffixStops isNewlineStart suffix
  → parseSignalGroup pos (emitSignalGroup-chars sg ++ₗ suffix)
    ≡ just (mkResult sg
             (advancePositions pos (emitSignalGroup-chars sg))
             suffix)
parseSignalGroup-roundtrip pos sg suffix nameStop sigs-stops nl-stop =
  trans (cong (λ inp → parseSignalGroup pos (inp ++ₗ suffix))
              (sym bridge))
    (trans step-format
      (trans step-many-newline
        step-pure))
  where
    bridge : emit signalGroupFmt sg ≡ emitSignalGroup-chars sg
    bridge = emit-signalGroupFmt-eq-emitSignalGroup-chars sg

    pos-line : Position
    pos-line = advancePositions pos (emit signalGroupFmt sg)

    cont-line : SignalGroup → Parser SignalGroup
    cont-line v = many parseNewline >>= λ _ → pure v

    cont-blanks : List Char → Parser SignalGroup
    cont-blanks _ = pure sg

    -- Step 1: parse signalGroupFmt succeeds via the universal roundtrip.
    step-format :
      parseSignalGroup pos (emit signalGroupFmt sg ++ₗ suffix)
      ≡ cont-line sg pos-line suffix
    step-format =
      bind-just-step (parse signalGroupFmt)
                     cont-line
                     pos (emit signalGroupFmt sg ++ₗ suffix)
                     sg pos-line suffix
                     (parseSignalGroup-format-roundtrip pos sg suffix
                        nameStop sigs-stops)

    -- Step 2: many parseNewline consumes zero from `suffix`.
    step-many-newline :
      cont-line sg pos-line suffix
      ≡ cont-blanks [] pos-line suffix
    step-many-newline =
      bind-just-step (many parseNewline)
                     cont-blanks
                     pos-line suffix
                     [] pos-line suffix
                     (manyHelper-parseNewline-exhaust
                       pos-line suffix (length suffix) nl-stop)

    -- Step 3: pure sg returns just (mkResult sg pos-line suffix); convert
    -- pos-line back to `advancePositions pos (emitSignalGroup-chars sg)`
    -- via the bridge.
    step-pure :
      cont-blanks [] pos-line suffix
      ≡ just (mkResult sg
               (advancePositions pos (emitSignalGroup-chars sg))
               suffix)
    step-pure =
      cong (λ p → just (mkResult sg p suffix))
           (cong (advancePositions pos) bridge)


-- ============================================================================
-- LIST-LEVEL ROUNDTRIP — `many parseSignalGroup` over a SIG_GROUP_ block
-- ============================================================================

-- Bundle of per-element preconditions consumed by `parseSignalGroup-
-- roundtrip`.  Lifted to `All SignalGroupWF sgs` at the call site so the
-- polymorphic `many-η-roundtrip` helper can pull a single `Stop : X → Set`.
record SignalGroupWF (sg : SignalGroup) : Set where
  field
    name-stop  : SignalGroupNameStop sg
    sigs-stops : All SigNameStop (SignalGroup.signals sg)

-- `0 < length (emitSignalGroup-chars sg)` — the literal `"SIG_GROUP_"`
-- prefix gives a 10-byte head.  Pattern-match on `sg` to expose the
-- `mkSignalGroup` projection so Agda reduces the `toList` literal.
emitSignalGroup-chars-nonzero : ∀ (sg : SignalGroup)
  → 0 < length (emitSignalGroup-chars sg)
emitSignalGroup-chars-nonzero _ = s≤s z≤n

-- Head of `emitSignalGroup-chars sg` is `'S'` — not a newline-start.
-- `SuffixStops isNewlineStart (emitSignalGroup-chars sg ++ suffix)`
-- discharges by `∷-stop refl` after Agda reduces the literal cons.
emitSignalGroup-chars-head-not-newline :
    ∀ (sg : SignalGroup) (suffix : List Char)
  → SuffixStops isNewlineStart (emitSignalGroup-chars sg ++ₗ suffix)
emitSignalGroup-chars-head-not-newline _ _ = ∷-stop refl


parseSignalGroups-roundtrip :
    ∀ (pos : Position) (sgs : List SignalGroup) (outer-suffix : List Char)
  → All SignalGroupWF sgs
  → SuffixStops isNewlineStart outer-suffix
  → (∀ (pos' : Position) → parseSignalGroup pos' outer-suffix ≡ nothing)
  → many parseSignalGroup pos
      (foldr (λ sg acc → emitSignalGroup-chars sg ++ₗ acc) [] sgs ++ₗ outer-suffix)
    ≡ just (mkResult sgs
             (advancePositions pos
               (foldr (λ sg acc → emitSignalGroup-chars sg ++ₗ acc) [] sgs))
             outer-suffix)
parseSignalGroups-roundtrip pos sgs outer-suffix sgs-wfs os pf =
  many-η-roundtrip
    parseSignalGroup
    emitSignalGroup-chars
    SignalGroupWF
    rt
    emitSignalGroup-chars-nonzero
    emitSignalGroup-chars-head-not-newline
    pos sgs outer-suffix sgs-wfs os pf
  where
    open import Aletheia.DBC.TextParser.Properties.ManyRoundtrip using
      (many-η-roundtrip)

    rt : ∀ (pos₁ : Position) (sg : SignalGroup) (suffix : List Char)
       → SignalGroupWF sg
       → SuffixStops isNewlineStart suffix
       → parseSignalGroup pos₁ (emitSignalGroup-chars sg ++ₗ suffix)
         ≡ just (mkResult sg (advancePositions pos₁ (emitSignalGroup-chars sg)) suffix)
    rt pos₁ sg suffix wf nl-stop =
      parseSignalGroup-roundtrip pos₁ sg suffix
        (SignalGroupWF.name-stop wf)
        (SignalGroupWF.sigs-stops wf)
        nl-stop
