{-# OPTIONS --safe --without-K #-}

-- Sound compositionality combinators for four-valued monitoring soundness.
--
-- Extracted from Aletheia.LTL.Adequacy to separate the algebraic
-- compositionality layer (Sound datatype + identity lemmas + combinators)
-- from the proof-specific adequacy machinery (decomposition, metric helpers,
-- main theorem).
--
-- Exports:
--   Sound       — datatype (6 constructors)
--   sound-not   — negation combinator
--   sound-and   — conjunction combinator
--   sound-or    — disjunction combinator
--   sound-or-false-l, sound-or-false-r   — absorbing ∨ combinators
--   sound-and-true-l, sound-and-true-r   — absorbing ∧ combinators
module Aletheia.LTL.Adequacy.SoundOps where

open import Aletheia.Prelude
open import Aletheia.LTL.SignalPredicate using (TruthVal; True; False; Unknown; Pending;
  notTV; _∧TV_; _∨TV_)
open import Aletheia.LTL.TruthVal.Properties using
  (∧TV-false-r; ∨TV-true-r; ∨TV-false-r; ∧TV-true-l; ∧TV-true-r; ∨TV-false-l)

-- ============================================================================
-- MONITORING SOUNDNESS (Sound)
-- ============================================================================

-- Sound m d means "m is a sound monitoring result for denotation d."
--
-- Definite agreement:    Sound True True, Sound False False
-- Denotation uncertain:  Sound m Unknown, Sound m Pending  (any monitor result OK)
-- Monitor uncertain:     Sound Unknown d, Sound Pending d  (admits ignorance)
--
-- Key exclusions: NOT Sound True False, NOT Sound False True
-- (the monitor NEVER gives a wrong definite answer)

data Sound : TruthVal → TruthVal → Set where
  sound-tt    : Sound True True
  sound-ff    : Sound False False
  sound-unk   : ∀ {m} → Sound m Unknown
  sound-pen   : ∀ {m} → Sound m Pending
  sound-m-unk : ∀ {d} → Sound Unknown d
  sound-m-pen : ∀ {d} → Sound Pending d

-- ============================================================================
-- FOUR-VALUED IDENTITY LEMMAS
-- ============================================================================

-- Kleene logic identity/absorb laws. These are needed because Agda's
-- overlapping clause patterns for ∧TV/∨TV prevent automatic reduction
-- when one argument is abstract (e.g., True ∧TV y doesn't reduce since
-- clause 1 checks first-arg=False, blocking clause 2's match on y).

-- ============================================================================
-- SOUND COMPOSITIONALITY LEMMAS
-- ============================================================================

-- These let us compose Sound proofs through propositional connectives.
--
-- Design note (finding A24): sound-and and sound-or share a superficially
-- similar 6x6 case structure, each containing 8 local helpers with 4x4
-- truth tables. Extracting a generic `sound-binop` parameterized by the
-- binary TV operation (∧TV/∨TV), absorber (False/True), and identity laws
-- was investigated but rejected because:
--
--   1. ∧TV/∨TV have overlapping clause patterns (e.g., False ∧TV _ = False
--      AND _ ∧TV False = False). Agda cannot reduce `C ∧TV a` when C is
--      Unknown or Pending and a is abstract — reduction is blocked on a.
--      This is the fundamental reason the 4x4 truth-table helpers exist.
--
--   2. A generic combinator would still need the same 4x4 case analysis
--      per (monitor-uncertain, denotation-uncertain) pair. The parameters
--      (op, absorber) would make each case MORE complex to state and verify
--      without reducing the total number of cases.
--
--   3. The two functions differ in their absorber patterns: sound-and
--      short-circuits on sound-ff (any second arg), sound-or on sound-tt.
--      This asymmetry means the top-level dispatch differs structurally.
--
-- The current structure (two parallel 6x6 functions) is the simplest that
-- Agda can type-check without stuck reductions in downstream consumers.

sound-not : ∀ {m d} → Sound m d → Sound (notTV m) (notTV d)
sound-not sound-tt    = sound-ff
sound-not sound-ff    = sound-tt
sound-not sound-unk   = sound-unk
sound-not sound-pen   = sound-pen
sound-not sound-m-unk = sound-m-unk
sound-not sound-m-pen = sound-m-pen

sound-and : ∀ {m₁ d₁ m₂ d₂} → Sound m₁ d₁ → Sound m₂ d₂ → Sound (m₁ ∧TV m₂) (d₁ ∧TV d₂)
sound-and sound-tt sound-tt = sound-tt
sound-and sound-tt sound-ff = sound-ff
sound-and sound-tt sound-unk = sound-unk
sound-and sound-tt sound-pen = sound-pen
sound-and sound-tt sound-m-unk = sound-m-unk
sound-and sound-tt sound-m-pen = sound-m-pen
sound-and sound-ff _ = sound-ff
sound-and sound-unk sound-tt = sound-unk
sound-and {m₁} sound-unk sound-ff rewrite ∧TV-false-r m₁ = sound-ff
sound-and sound-unk sound-unk = sound-unk
sound-and sound-unk sound-pen = sound-pen
sound-and {m₁} {_} {_} {d₂} sound-unk sound-m-unk = unk-and-unk m₁ d₂
  where
    unk-and-unk : ∀ a b → Sound (a ∧TV Unknown) (Unknown ∧TV b)
    unk-and-unk True    True    = sound-unk
    unk-and-unk True    False   = sound-m-unk
    unk-and-unk True    Unknown = sound-unk
    unk-and-unk True    Pending = sound-pen
    unk-and-unk False   True    = sound-unk
    unk-and-unk False   False   = sound-ff
    unk-and-unk False   Unknown = sound-unk
    unk-and-unk False   Pending = sound-pen
    unk-and-unk Unknown True    = sound-unk
    unk-and-unk Unknown False   = sound-m-unk
    unk-and-unk Unknown Unknown = sound-unk
    unk-and-unk Unknown Pending = sound-pen
    unk-and-unk Pending True    = sound-unk
    unk-and-unk Pending False   = sound-m-pen
    unk-and-unk Pending Unknown = sound-unk
    unk-and-unk Pending Pending = sound-pen
sound-and {m₁} {_} {_} {d₂} sound-unk sound-m-pen = unk-and-pen m₁ d₂
  where
    unk-and-pen : ∀ a b → Sound (a ∧TV Pending) (Unknown ∧TV b)
    unk-and-pen True    True    = sound-unk
    unk-and-pen True    False   = sound-m-pen
    unk-and-pen True    Unknown = sound-unk
    unk-and-pen True    Pending = sound-pen
    unk-and-pen False   True    = sound-unk
    unk-and-pen False   False   = sound-ff
    unk-and-pen False   Unknown = sound-unk
    unk-and-pen False   Pending = sound-pen
    unk-and-pen Unknown True    = sound-unk
    unk-and-pen Unknown False   = sound-m-pen
    unk-and-pen Unknown Unknown = sound-unk
    unk-and-pen Unknown Pending = sound-pen
    unk-and-pen Pending True    = sound-unk
    unk-and-pen Pending False   = sound-m-pen
    unk-and-pen Pending Unknown = sound-unk
    unk-and-pen Pending Pending = sound-pen
sound-and sound-pen sound-tt = sound-pen
sound-and {m₁} sound-pen sound-ff rewrite ∧TV-false-r m₁ = sound-ff
sound-and sound-pen sound-unk = sound-pen
sound-and sound-pen sound-pen = sound-pen
sound-and {m₁} {_} {_} {d₂} sound-pen sound-m-unk = pen-and-unk m₁ d₂
  where
    pen-and-unk : ∀ a b → Sound (a ∧TV Unknown) (Pending ∧TV b)
    pen-and-unk True    True    = sound-pen
    pen-and-unk True    False   = sound-m-unk
    pen-and-unk True    Unknown = sound-pen
    pen-and-unk True    Pending = sound-pen
    pen-and-unk False   True    = sound-pen
    pen-and-unk False   False   = sound-ff
    pen-and-unk False   Unknown = sound-pen
    pen-and-unk False   Pending = sound-pen
    pen-and-unk Unknown True    = sound-pen
    pen-and-unk Unknown False   = sound-m-unk
    pen-and-unk Unknown Unknown = sound-pen
    pen-and-unk Unknown Pending = sound-pen
    pen-and-unk Pending True    = sound-pen
    pen-and-unk Pending False   = sound-m-pen
    pen-and-unk Pending Unknown = sound-pen
    pen-and-unk Pending Pending = sound-pen
sound-and {m₁} {_} {_} {d₂} sound-pen sound-m-pen = pen-and-pen m₁ d₂
  where
    pen-and-pen : ∀ a b → Sound (a ∧TV Pending) (Pending ∧TV b)
    pen-and-pen True    True    = sound-pen
    pen-and-pen True    False   = sound-m-pen
    pen-and-pen True    Unknown = sound-pen
    pen-and-pen True    Pending = sound-pen
    pen-and-pen False   True    = sound-pen
    pen-and-pen False   False   = sound-ff
    pen-and-pen False   Unknown = sound-pen
    pen-and-pen False   Pending = sound-pen
    pen-and-pen Unknown True    = sound-pen
    pen-and-pen Unknown False   = sound-m-pen
    pen-and-pen Unknown Unknown = sound-pen
    pen-and-pen Unknown Pending = sound-pen
    pen-and-pen Pending True    = sound-pen
    pen-and-pen Pending False   = sound-m-pen
    pen-and-pen Pending Unknown = sound-pen
    pen-and-pen Pending Pending = sound-pen
sound-and sound-m-unk sound-tt = sound-m-unk
sound-and {_} {d₁} sound-m-unk sound-ff rewrite ∧TV-false-r d₁ = sound-ff
sound-and {_} {d₁} {m₂} {_} sound-m-unk sound-unk = munk-and-unk m₂ d₁
  where
    munk-and-unk : ∀ a b → Sound (Unknown ∧TV a) (b ∧TV Unknown)
    munk-and-unk True    True    = sound-unk
    munk-and-unk True    False   = sound-m-unk
    munk-and-unk True    Unknown = sound-unk
    munk-and-unk True    Pending = sound-pen
    munk-and-unk False   True    = sound-unk
    munk-and-unk False   False   = sound-ff
    munk-and-unk False   Unknown = sound-unk
    munk-and-unk False   Pending = sound-pen
    munk-and-unk Unknown True    = sound-unk
    munk-and-unk Unknown False   = sound-m-unk
    munk-and-unk Unknown Unknown = sound-unk
    munk-and-unk Unknown Pending = sound-pen
    munk-and-unk Pending True    = sound-unk
    munk-and-unk Pending False   = sound-m-pen
    munk-and-unk Pending Unknown = sound-unk
    munk-and-unk Pending Pending = sound-pen
sound-and {_} {d₁} {m₂} {_} sound-m-unk sound-pen = munk-and-pen m₂ d₁
  where
    munk-and-pen : ∀ a b → Sound (Unknown ∧TV a) (b ∧TV Pending)
    munk-and-pen True    True    = sound-pen
    munk-and-pen True    False   = sound-m-unk
    munk-and-pen True    Unknown = sound-pen
    munk-and-pen True    Pending = sound-pen
    munk-and-pen False   True    = sound-pen
    munk-and-pen False   False   = sound-ff
    munk-and-pen False   Unknown = sound-pen
    munk-and-pen False   Pending = sound-pen
    munk-and-pen Unknown True    = sound-pen
    munk-and-pen Unknown False   = sound-m-unk
    munk-and-pen Unknown Unknown = sound-pen
    munk-and-pen Unknown Pending = sound-pen
    munk-and-pen Pending True    = sound-pen
    munk-and-pen Pending False   = sound-m-pen
    munk-and-pen Pending Unknown = sound-pen
    munk-and-pen Pending Pending = sound-pen
sound-and sound-m-unk sound-m-unk = sound-m-unk
sound-and sound-m-unk sound-m-pen = sound-m-pen
sound-and sound-m-pen sound-tt = sound-m-pen
sound-and {_} {d₁} sound-m-pen sound-ff rewrite ∧TV-false-r d₁ = sound-ff
sound-and {_} {d₁} {m₂} {_} sound-m-pen sound-unk = mpen-and-unk m₂ d₁
  where
    mpen-and-unk : ∀ a b → Sound (Pending ∧TV a) (b ∧TV Unknown)
    mpen-and-unk True    True    = sound-unk
    mpen-and-unk True    False   = sound-m-pen
    mpen-and-unk True    Unknown = sound-unk
    mpen-and-unk True    Pending = sound-pen
    mpen-and-unk False   True    = sound-unk
    mpen-and-unk False   False   = sound-ff
    mpen-and-unk False   Unknown = sound-unk
    mpen-and-unk False   Pending = sound-pen
    mpen-and-unk Unknown True    = sound-unk
    mpen-and-unk Unknown False   = sound-m-pen
    mpen-and-unk Unknown Unknown = sound-unk
    mpen-and-unk Unknown Pending = sound-pen
    mpen-and-unk Pending True    = sound-unk
    mpen-and-unk Pending False   = sound-m-pen
    mpen-and-unk Pending Unknown = sound-unk
    mpen-and-unk Pending Pending = sound-pen
sound-and {_} {d₁} {m₂} {_} sound-m-pen sound-pen = mpen-and-pen m₂ d₁
  where
    mpen-and-pen : ∀ a b → Sound (Pending ∧TV a) (b ∧TV Pending)
    mpen-and-pen True    True    = sound-pen
    mpen-and-pen True    False   = sound-m-pen
    mpen-and-pen True    Unknown = sound-pen
    mpen-and-pen True    Pending = sound-pen
    mpen-and-pen False   True    = sound-pen
    mpen-and-pen False   False   = sound-ff
    mpen-and-pen False   Unknown = sound-pen
    mpen-and-pen False   Pending = sound-pen
    mpen-and-pen Unknown True    = sound-pen
    mpen-and-pen Unknown False   = sound-m-pen
    mpen-and-pen Unknown Unknown = sound-pen
    mpen-and-pen Unknown Pending = sound-pen
    mpen-and-pen Pending True    = sound-pen
    mpen-and-pen Pending False   = sound-m-pen
    mpen-and-pen Pending Unknown = sound-pen
    mpen-and-pen Pending Pending = sound-pen
sound-and sound-m-pen sound-m-unk = sound-m-pen
sound-and sound-m-pen sound-m-pen = sound-m-pen

sound-or : ∀ {m₁ d₁ m₂ d₂} → Sound m₁ d₁ → Sound m₂ d₂ → Sound (m₁ ∨TV m₂) (d₁ ∨TV d₂)
sound-or sound-tt _ = sound-tt
sound-or sound-ff sound-tt = sound-tt
sound-or sound-ff sound-ff = sound-ff
sound-or sound-ff sound-unk = sound-unk
sound-or sound-ff sound-pen = sound-pen
sound-or sound-ff sound-m-unk = sound-m-unk
sound-or sound-ff sound-m-pen = sound-m-pen
sound-or {m₁} sound-unk sound-tt rewrite ∨TV-true-r m₁ = sound-tt
sound-or sound-unk sound-ff = sound-unk
sound-or sound-unk sound-unk = sound-unk
sound-or sound-unk sound-pen = sound-pen
sound-or {m₁} {_} {_} {d₂} sound-unk sound-m-unk = unk-or-unk m₁ d₂
  where
    unk-or-unk : ∀ a b → Sound (a ∨TV Unknown) (Unknown ∨TV b)
    unk-or-unk True    True    = sound-tt
    unk-or-unk True    False   = sound-unk
    unk-or-unk True    Unknown = sound-unk
    unk-or-unk True    Pending = sound-pen
    unk-or-unk False   True    = sound-m-unk
    unk-or-unk False   False   = sound-unk
    unk-or-unk False   Unknown = sound-unk
    unk-or-unk False   Pending = sound-pen
    unk-or-unk Unknown True    = sound-m-unk
    unk-or-unk Unknown False   = sound-unk
    unk-or-unk Unknown Unknown = sound-unk
    unk-or-unk Unknown Pending = sound-pen
    unk-or-unk Pending True    = sound-m-pen
    unk-or-unk Pending False   = sound-unk
    unk-or-unk Pending Unknown = sound-unk
    unk-or-unk Pending Pending = sound-pen
sound-or {m₁} {_} {_} {d₂} sound-unk sound-m-pen = unk-or-pen m₁ d₂
  where
    unk-or-pen : ∀ a b → Sound (a ∨TV Pending) (Unknown ∨TV b)
    unk-or-pen True    True    = sound-tt
    unk-or-pen True    False   = sound-unk
    unk-or-pen True    Unknown = sound-unk
    unk-or-pen True    Pending = sound-pen
    unk-or-pen False   True    = sound-m-pen
    unk-or-pen False   False   = sound-unk
    unk-or-pen False   Unknown = sound-unk
    unk-or-pen False   Pending = sound-pen
    unk-or-pen Unknown True    = sound-m-pen
    unk-or-pen Unknown False   = sound-unk
    unk-or-pen Unknown Unknown = sound-unk
    unk-or-pen Unknown Pending = sound-pen
    unk-or-pen Pending True    = sound-m-pen
    unk-or-pen Pending False   = sound-unk
    unk-or-pen Pending Unknown = sound-unk
    unk-or-pen Pending Pending = sound-pen
sound-or {m₁} sound-pen sound-tt rewrite ∨TV-true-r m₁ = sound-tt
sound-or {m₁} sound-pen sound-ff rewrite ∨TV-false-r m₁ = sound-pen
sound-or sound-pen sound-unk = sound-pen
sound-or sound-pen sound-pen = sound-pen
sound-or {m₁} {_} {_} {d₂} sound-pen sound-m-unk = pen-or-unk m₁ d₂
  where
    pen-or-unk : ∀ a b → Sound (a ∨TV Unknown) (Pending ∨TV b)
    pen-or-unk True    True    = sound-tt
    pen-or-unk True    False   = sound-pen
    pen-or-unk True    Unknown = sound-pen
    pen-or-unk True    Pending = sound-pen
    pen-or-unk False   True    = sound-m-unk
    pen-or-unk False   False   = sound-pen
    pen-or-unk False   Unknown = sound-pen
    pen-or-unk False   Pending = sound-pen
    pen-or-unk Unknown True    = sound-m-unk
    pen-or-unk Unknown False   = sound-pen
    pen-or-unk Unknown Unknown = sound-pen
    pen-or-unk Unknown Pending = sound-pen
    pen-or-unk Pending True    = sound-m-pen
    pen-or-unk Pending False   = sound-pen
    pen-or-unk Pending Unknown = sound-pen
    pen-or-unk Pending Pending = sound-pen
sound-or {m₁} {_} {_} {d₂} sound-pen sound-m-pen = pen-or-pen m₁ d₂
  where
    pen-or-pen : ∀ a b → Sound (a ∨TV Pending) (Pending ∨TV b)
    pen-or-pen True    True    = sound-tt
    pen-or-pen True    False   = sound-pen
    pen-or-pen True    Unknown = sound-pen
    pen-or-pen True    Pending = sound-pen
    pen-or-pen False   True    = sound-m-pen
    pen-or-pen False   False   = sound-pen
    pen-or-pen False   Unknown = sound-pen
    pen-or-pen False   Pending = sound-pen
    pen-or-pen Unknown True    = sound-m-pen
    pen-or-pen Unknown False   = sound-pen
    pen-or-pen Unknown Unknown = sound-pen
    pen-or-pen Unknown Pending = sound-pen
    pen-or-pen Pending True    = sound-m-pen
    pen-or-pen Pending False   = sound-pen
    pen-or-pen Pending Unknown = sound-pen
    pen-or-pen Pending Pending = sound-pen
sound-or {_} {d₁} sound-m-unk sound-tt rewrite ∨TV-true-r d₁ = sound-tt
sound-or sound-m-unk sound-ff = sound-m-unk
sound-or {_} {d₁} {m₂} {_} sound-m-unk sound-unk = munk-or-unk m₂ d₁
  where
    munk-or-unk : ∀ a b → Sound (Unknown ∨TV a) (b ∨TV Unknown)
    munk-or-unk True    True    = sound-tt
    munk-or-unk True    False   = sound-unk
    munk-or-unk True    Unknown = sound-unk
    munk-or-unk True    Pending = sound-pen
    munk-or-unk False   True    = sound-m-unk
    munk-or-unk False   False   = sound-unk
    munk-or-unk False   Unknown = sound-unk
    munk-or-unk False   Pending = sound-pen
    munk-or-unk Unknown True    = sound-m-unk
    munk-or-unk Unknown False   = sound-unk
    munk-or-unk Unknown Unknown = sound-unk
    munk-or-unk Unknown Pending = sound-pen
    munk-or-unk Pending True    = sound-m-pen
    munk-or-unk Pending False   = sound-unk
    munk-or-unk Pending Unknown = sound-unk
    munk-or-unk Pending Pending = sound-pen
sound-or {_} {d₁} {m₂} {_} sound-m-unk sound-pen = munk-or-pen m₂ d₁
  where
    munk-or-pen : ∀ a b → Sound (Unknown ∨TV a) (b ∨TV Pending)
    munk-or-pen True    True    = sound-tt
    munk-or-pen True    False   = sound-pen
    munk-or-pen True    Unknown = sound-pen
    munk-or-pen True    Pending = sound-pen
    munk-or-pen False   True    = sound-m-unk
    munk-or-pen False   False   = sound-pen
    munk-or-pen False   Unknown = sound-pen
    munk-or-pen False   Pending = sound-pen
    munk-or-pen Unknown True    = sound-m-unk
    munk-or-pen Unknown False   = sound-pen
    munk-or-pen Unknown Unknown = sound-pen
    munk-or-pen Unknown Pending = sound-pen
    munk-or-pen Pending True    = sound-m-pen
    munk-or-pen Pending False   = sound-pen
    munk-or-pen Pending Unknown = sound-pen
    munk-or-pen Pending Pending = sound-pen
sound-or sound-m-unk sound-m-unk = sound-m-unk
sound-or sound-m-unk sound-m-pen = sound-m-pen
sound-or {_} {d₁} sound-m-pen sound-tt rewrite ∨TV-true-r d₁ = sound-tt
sound-or {_} {d₁} sound-m-pen sound-ff rewrite ∨TV-false-r d₁ = sound-m-pen
sound-or {_} {d₁} {m₂} {_} sound-m-pen sound-unk = mpen-or-unk m₂ d₁
  where
    mpen-or-unk : ∀ a b → Sound (Pending ∨TV a) (b ∨TV Unknown)
    mpen-or-unk True    True    = sound-tt
    mpen-or-unk True    False   = sound-unk
    mpen-or-unk True    Unknown = sound-unk
    mpen-or-unk True    Pending = sound-pen
    mpen-or-unk False   True    = sound-m-pen
    mpen-or-unk False   False   = sound-unk
    mpen-or-unk False   Unknown = sound-unk
    mpen-or-unk False   Pending = sound-pen
    mpen-or-unk Unknown True    = sound-m-pen
    mpen-or-unk Unknown False   = sound-unk
    mpen-or-unk Unknown Unknown = sound-unk
    mpen-or-unk Unknown Pending = sound-pen
    mpen-or-unk Pending True    = sound-m-pen
    mpen-or-unk Pending False   = sound-unk
    mpen-or-unk Pending Unknown = sound-unk
    mpen-or-unk Pending Pending = sound-pen
sound-or {_} {d₁} {m₂} {_} sound-m-pen sound-pen = mpen-or-pen m₂ d₁
  where
    mpen-or-pen : ∀ a b → Sound (Pending ∨TV a) (b ∨TV Pending)
    mpen-or-pen True    True    = sound-tt
    mpen-or-pen True    False   = sound-pen
    mpen-or-pen True    Unknown = sound-pen
    mpen-or-pen True    Pending = sound-pen
    mpen-or-pen False   True    = sound-m-pen
    mpen-or-pen False   False   = sound-pen
    mpen-or-pen False   Unknown = sound-pen
    mpen-or-pen False   Pending = sound-pen
    mpen-or-pen Unknown True    = sound-m-pen
    mpen-or-pen Unknown False   = sound-pen
    mpen-or-pen Unknown Unknown = sound-pen
    mpen-or-pen Unknown Pending = sound-pen
    mpen-or-pen Pending True    = sound-m-pen
    mpen-or-pen Pending False   = sound-pen
    mpen-or-pen Pending Unknown = sound-pen
    mpen-or-pen Pending Pending = sound-pen
sound-or sound-m-pen sound-m-unk = sound-m-pen
sound-or sound-m-pen sound-m-pen = sound-m-pen

-- Derived combinators: sound-or/sound-and with one absorbing argument.
-- These avoid stuck ∨TV/∧TV reductions (False ∨TV abstract, True ∧TV abstract)
-- by pattern matching on Sound constructors so both sides are concrete.
--
-- Why pattern matching (not subst): When the result of sound-or-false-l is passed
-- to sound-and or other combinators, the monitor component must be fully concrete.
-- subst leaves an abstract ∨TV/∧TV expression that blocks downstream unification.
-- Pattern matching computes the result directly — no stuck terms.

sound-or-false-l : ∀ {d₁ d₂ m₂} → Sound False d₁ → Sound m₂ d₂ → Sound m₂ (d₁ ∨TV d₂)
-- m₂ abstract: result independent of ∨TV computation
sound-or-false-l _         sound-m-unk = sound-m-unk
sound-or-false-l _         sound-m-pen = sound-m-pen
-- Both d₁ and d₂ concrete: ∨TV reduces, result mirrors output
sound-or-false-l sound-ff  sound-tt    = sound-tt
sound-or-false-l sound-ff  sound-ff    = sound-ff
sound-or-false-l sound-ff  sound-unk   = sound-unk
sound-or-false-l sound-ff  sound-pen   = sound-pen
sound-or-false-l sound-unk sound-tt    = sound-tt
sound-or-false-l sound-unk sound-ff    = sound-unk
sound-or-false-l sound-unk sound-unk   = sound-unk
sound-or-false-l sound-unk sound-pen   = sound-pen
sound-or-false-l sound-pen sound-tt    = sound-tt
sound-or-false-l sound-pen sound-ff    = sound-pen
sound-or-false-l sound-pen sound-unk   = sound-pen
sound-or-false-l sound-pen sound-pen   = sound-pen

sound-or-false-r : ∀ {d₁ d₂ m₁} → Sound m₁ d₁ → Sound False d₂ → Sound m₁ (d₁ ∨TV d₂)
sound-or-false-r sound-m-unk _         = sound-m-unk
sound-or-false-r sound-m-pen _         = sound-m-pen
sound-or-false-r sound-tt    _         = sound-tt
sound-or-false-r sound-ff  sound-ff    = sound-ff
sound-or-false-r sound-ff  sound-unk   = sound-unk
sound-or-false-r sound-ff  sound-pen   = sound-pen
sound-or-false-r sound-unk sound-ff    = sound-unk
sound-or-false-r sound-unk sound-unk   = sound-unk
sound-or-false-r sound-unk sound-pen   = sound-pen
sound-or-false-r sound-pen sound-ff    = sound-pen
sound-or-false-r sound-pen sound-unk   = sound-pen
sound-or-false-r sound-pen sound-pen   = sound-pen

sound-and-true-l : ∀ {d₁ d₂ m₂} → Sound True d₁ → Sound m₂ d₂ → Sound m₂ (d₁ ∧TV d₂)
sound-and-true-l _         sound-m-unk = sound-m-unk
sound-and-true-l _         sound-m-pen = sound-m-pen
sound-and-true-l sound-tt  sound-tt    = sound-tt
sound-and-true-l sound-tt  sound-ff    = sound-ff
sound-and-true-l sound-tt  sound-unk   = sound-unk
sound-and-true-l sound-tt  sound-pen   = sound-pen
sound-and-true-l sound-unk sound-tt    = sound-unk
sound-and-true-l sound-unk sound-ff    = sound-ff
sound-and-true-l sound-unk sound-unk   = sound-unk
sound-and-true-l sound-unk sound-pen   = sound-pen
sound-and-true-l sound-pen sound-tt    = sound-pen
sound-and-true-l sound-pen sound-ff    = sound-ff
sound-and-true-l sound-pen sound-unk   = sound-pen
sound-and-true-l sound-pen sound-pen   = sound-pen

sound-and-true-r : ∀ {d₁ d₂ m₁} → Sound m₁ d₁ → Sound True d₂ → Sound m₁ (d₁ ∧TV d₂)
sound-and-true-r sound-m-unk _         = sound-m-unk
sound-and-true-r sound-m-pen _         = sound-m-pen
sound-and-true-r sound-ff    _         = sound-ff
sound-and-true-r sound-tt  sound-tt    = sound-tt
sound-and-true-r sound-tt  sound-unk   = sound-unk
sound-and-true-r sound-tt  sound-pen   = sound-pen
sound-and-true-r sound-unk sound-tt    = sound-unk
sound-and-true-r sound-unk sound-unk   = sound-unk
sound-and-true-r sound-unk sound-pen   = sound-pen
sound-and-true-r sound-pen sound-tt    = sound-pen
sound-and-true-r sound-pen sound-unk   = sound-pen
sound-and-true-r sound-pen sound-pen   = sound-pen
