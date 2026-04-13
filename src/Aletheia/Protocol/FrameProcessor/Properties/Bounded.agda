{-# OPTIONS --safe --without-K #-}

-- Atom-index bound proofs for the LTL frame processor.
--
-- Combines two property groups that share the `flattenAtoms`/`AllBelow`
-- machinery and the `lookupAtom` totality lemma:
--
--   PROPERTY 9  — `mkPredTable` faithfulness:
--     atom indices assigned by `indexHelper`/`indexFormula` line up with
--     the predicates returned by `lookupAtom (collectAtoms φ)`.
--
--   PROPERTY 27 — atom-index bound:
--     every atom index in any LTL ℕ formula reachable from `indexFormula`
--     stays strictly below `length (collectAtoms φ)`. The bound is
--     preserved through `simplify` and `stepL`, so the `nothing → Unknown`
--     branch in `mkPredTable` is provably dead code on the streaming
--     hot path.
--
-- These two property groups live together because P27's terminal
-- `mkPredTable-bounded` corollary uses P9's `lookupAtom-total` and
-- `mkPredTable-lookup` lemmas to discharge the lookup obligation.
--
-- Public API consumed downstream:
--   - `AllBelow` (used by `Protocol.Adequacy.WarmCache`)
--   - `mkPredTable-lookup` (used by `Protocol.Adequacy.WarmCache`)
module Aletheia.Protocol.FrameProcessor.Properties.Bounded where

open import Aletheia.Protocol.StreamState.Internals
    using (mkPredTable; collectAtoms; indexFormula; collectAtomsAcc; indexHelper; lookupAtom)
open import Aletheia.LTL.Coalgebra using (LTLProc; PredTable; stepL; combineAnd; combineOr)
open import Aletheia.LTL.Simplify using (simplify; absorb; _≡ᵇ-proc_; finalizesHolds; finalizesFails)
open import Aletheia.LTL.Syntax using (LTL; Atomic; Not; And; Or; Next; Always; Eventually;
    Until; Release; MetricEventually; MetricAlways; MetricUntil; MetricRelease;
    decodeStart)
open import Aletheia.LTL.Incremental using (StepResult; Continue; Violated; Satisfied)
open import Aletheia.LTL.SignalPredicate
    using (SignalPredicate; evalPredicateTV;
           True; False; Unknown; Pending)
open import Aletheia.Trace.CANTrace using (TimedFrame; timestampℕ)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.Maybe using (just)
open import Data.List using (List; []; _∷_; length) renaming (_++_ to _++ₗ_)
open import Data.List.Properties using (++-assoc; ++-identityʳ; length-++; length-++-≤ˡ)
open import Data.Nat using (ℕ; zero; suc; _+_; _<_; _≤_; s≤s; z≤n; _∸_; _≤ᵇ_)
open import Data.Nat.Properties using (+-assoc; +-comm; +-identityʳ;
    ≤-refl; ≤-trans; n≤1+n)
open import Data.Bool using (true; false)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

-- ============================================================================
-- PROPERTY 9: mkPredTable faithfulness (atom indexing consistency)
-- ============================================================================
--
-- Proves that indexHelper and collectAtomsAcc assign indices and collect
-- atoms in the same left-to-right order, so mkPredTable evaluates
-- the correct signal predicate for each atom index.

-- Forward specification: atoms in left-to-right order (no accumulator).
flattenAtoms : LTL SignalPredicate → List SignalPredicate
flattenAtoms (Atomic a)               = a ∷ []
flattenAtoms (Not φ)                  = flattenAtoms φ
flattenAtoms (And φ ψ)               = flattenAtoms φ ++ₗ flattenAtoms ψ
flattenAtoms (Or φ ψ)                = flattenAtoms φ ++ₗ flattenAtoms ψ
flattenAtoms (Next φ)                 = flattenAtoms φ
flattenAtoms (Always φ)               = flattenAtoms φ
flattenAtoms (Eventually φ)           = flattenAtoms φ
flattenAtoms (Until φ ψ)             = flattenAtoms φ ++ₗ flattenAtoms ψ
flattenAtoms (Release φ ψ)           = flattenAtoms φ ++ₗ flattenAtoms ψ
flattenAtoms (MetricEventually _ _ φ) = flattenAtoms φ
flattenAtoms (MetricAlways _ _ φ)     = flattenAtoms φ
flattenAtoms (MetricUntil _ _ φ ψ)   = flattenAtoms φ ++ₗ flattenAtoms ψ
flattenAtoms (MetricRelease _ _ φ ψ) = flattenAtoms φ ++ₗ flattenAtoms ψ

-- List lookup over concatenation: left part.
lookupAtom-++-left : ∀ (xs ys : List SignalPredicate) k
  → k < length xs → lookupAtom (xs ++ₗ ys) k ≡ lookupAtom xs k
lookupAtom-++-left []       ys k       ()
lookupAtom-++-left (x ∷ xs) ys zero    _         = refl
lookupAtom-++-left (x ∷ xs) ys (suc k) (s≤s k<n) = lookupAtom-++-left xs ys k k<n

-- List lookup over concatenation: right part.
lookupAtom-++-right : ∀ (xs ys : List SignalPredicate) k
  → lookupAtom (xs ++ₗ ys) (length xs + k) ≡ lookupAtom ys k
lookupAtom-++-right []       ys k = refl
lookupAtom-++-right (x ∷ xs) ys k = lookupAtom-++-right xs ys k

private
  -- Arithmetic: b + (a + n) ≡ (a + b) + n
  +-swap-sum : ∀ a b n → b + (a + n) ≡ (a + b) + n
  +-swap-sum a b n = trans (sym (+-assoc b a n)) (cong (_+ n) (+-comm b a))

  -- Arithmetic: (a + k) + n ≡ k + (a + n)
  ψ-index-eq : ∀ a k n → (a + k) + n ≡ k + (a + n)
  ψ-index-eq a k n = trans (cong (_+ n) (+-comm a k)) (+-assoc k a n)

  -- Extend k < |xs| to k < |xs ++ₗ ys|
  extend-< : ∀ {k} (xs ys : List SignalPredicate)
    → k < length xs → k < length (xs ++ₗ ys)
  extend-< xs ys k< = ≤-trans k< (length-++-≤ˡ xs)

  -- Shift k < |ys| to |xs| + k < |xs ++ₗ ys|
  shift-< : ∀ (xs ys : List SignalPredicate) {k}
    → k < length ys → length xs + k < length (xs ++ₗ ys)
  shift-< []       ys k< = k<
  shift-< (x ∷ xs) ys k< = s≤s (shift-< xs ys k<)

-- Counter increment equals atom count.
indexHelper-counter : ∀ (φ : LTL SignalPredicate) n
  → proj₂ (indexHelper φ n) ≡ length (flattenAtoms φ) + n
indexHelper-counter (Atomic _) n            = refl
indexHelper-counter (Not φ) n               = indexHelper-counter φ n
indexHelper-counter (And φ ψ) n
  rewrite indexHelper-counter φ n
  | indexHelper-counter ψ (length (flattenAtoms φ) + n)
  | length-++ (flattenAtoms φ) {flattenAtoms ψ}
  = +-swap-sum (length (flattenAtoms φ)) (length (flattenAtoms ψ)) n
indexHelper-counter (Or φ ψ) n
  rewrite indexHelper-counter φ n
  | indexHelper-counter ψ (length (flattenAtoms φ) + n)
  | length-++ (flattenAtoms φ) {flattenAtoms ψ}
  = +-swap-sum (length (flattenAtoms φ)) (length (flattenAtoms ψ)) n
indexHelper-counter (Next φ) n              = indexHelper-counter φ n
indexHelper-counter (Always φ) n            = indexHelper-counter φ n
indexHelper-counter (Eventually φ) n        = indexHelper-counter φ n
indexHelper-counter (Until φ ψ) n
  rewrite indexHelper-counter φ n
  | indexHelper-counter ψ (length (flattenAtoms φ) + n)
  | length-++ (flattenAtoms φ) {flattenAtoms ψ}
  = +-swap-sum (length (flattenAtoms φ)) (length (flattenAtoms ψ)) n
indexHelper-counter (Release φ ψ) n
  rewrite indexHelper-counter φ n
  | indexHelper-counter ψ (length (flattenAtoms φ) + n)
  | length-++ (flattenAtoms φ) {flattenAtoms ψ}
  = +-swap-sum (length (flattenAtoms φ)) (length (flattenAtoms ψ)) n
indexHelper-counter (MetricEventually _ _ φ) n = indexHelper-counter φ n
indexHelper-counter (MetricAlways _ _ φ) n     = indexHelper-counter φ n
indexHelper-counter (MetricUntil _ _ φ ψ) n
  rewrite indexHelper-counter φ n
  | indexHelper-counter ψ (length (flattenAtoms φ) + n)
  | length-++ (flattenAtoms φ) {flattenAtoms ψ}
  = +-swap-sum (length (flattenAtoms φ)) (length (flattenAtoms ψ)) n
indexHelper-counter (MetricRelease _ _ φ ψ) n
  rewrite indexHelper-counter φ n
  | indexHelper-counter ψ (length (flattenAtoms φ) + n)
  | length-++ (flattenAtoms φ) {flattenAtoms ψ}
  = +-swap-sum (length (flattenAtoms φ)) (length (flattenAtoms ψ)) n

-- Per-index correctness: each atom index maps to the right predicate.
-- Faithful atoms φ n holds when every Atomic k assigned by indexHelper φ n
-- satisfies lookupAtom atoms k ≡ just pred.
Faithful : List SignalPredicate → LTL SignalPredicate → ℕ → Set
Faithful atoms (Atomic a) n               = lookupAtom atoms n ≡ just a
Faithful atoms (Not φ) n                  = Faithful atoms φ n
Faithful atoms (And φ ψ) n               = Faithful atoms φ n × Faithful atoms ψ (proj₂ (indexHelper φ n))
Faithful atoms (Or φ ψ) n                = Faithful atoms φ n × Faithful atoms ψ (proj₂ (indexHelper φ n))
Faithful atoms (Next φ) n                 = Faithful atoms φ n
Faithful atoms (Always φ) n               = Faithful atoms φ n
Faithful atoms (Eventually φ) n           = Faithful atoms φ n
Faithful atoms (Until φ ψ) n             = Faithful atoms φ n × Faithful atoms ψ (proj₂ (indexHelper φ n))
Faithful atoms (Release φ ψ) n           = Faithful atoms φ n × Faithful atoms ψ (proj₂ (indexHelper φ n))
Faithful atoms (MetricEventually _ _ φ) n = Faithful atoms φ n
Faithful atoms (MetricAlways _ _ φ) n     = Faithful atoms φ n
Faithful atoms (MetricUntil _ _ φ ψ) n   = Faithful atoms φ n × Faithful atoms ψ (proj₂ (indexHelper φ n))
Faithful atoms (MetricRelease _ _ φ ψ) n = Faithful atoms φ n × Faithful atoms ψ (proj₂ (indexHelper φ n))

-- Hypothesis constructors for binary formula cases.
private
  mk-φ-hyp : ∀ {n} ga (φ ψ : LTL SignalPredicate) →
    (∀ k → k < length (flattenAtoms φ ++ₗ flattenAtoms ψ) →
       lookupAtom ga (k + n) ≡ lookupAtom (flattenAtoms φ ++ₗ flattenAtoms ψ) k) →
    ∀ k → k < length (flattenAtoms φ) → lookupAtom ga (k + n) ≡ lookupAtom (flattenAtoms φ) k
  mk-φ-hyp ga φ ψ hyp k k< =
    trans (hyp k (extend-< (flattenAtoms φ) (flattenAtoms ψ) k<))
          (lookupAtom-++-left (flattenAtoms φ) (flattenAtoms ψ) k k<)

  mk-ψ-hyp : ∀ ga (φ ψ : LTL SignalPredicate) n →
    (∀ k → k < length (flattenAtoms φ ++ₗ flattenAtoms ψ) →
       lookupAtom ga (k + n) ≡ lookupAtom (flattenAtoms φ ++ₗ flattenAtoms ψ) k) →
    ∀ k → k < length (flattenAtoms ψ) →
    lookupAtom ga (k + proj₂ (indexHelper φ n)) ≡ lookupAtom (flattenAtoms ψ) k
  mk-ψ-hyp ga φ ψ n hyp k k<
    rewrite indexHelper-counter φ n
    | sym (ψ-index-eq (length (flattenAtoms φ)) k n)
    = trans (hyp (length (flattenAtoms φ) + k) (shift-< (flattenAtoms φ) (flattenAtoms ψ) k<))
            (lookupAtom-++-right (flattenAtoms φ) (flattenAtoms ψ) k)

-- Generalized faithfulness: if the atom list matches flattenAtoms at offset n,
-- then every atom index in the indexed formula looks up correctly.
faithful-gen : ∀ ga (φ : LTL SignalPredicate) n →
  (∀ k → k < length (flattenAtoms φ) → lookupAtom ga (k + n) ≡ lookupAtom (flattenAtoms φ) k) →
  Faithful ga φ n
faithful-gen ga (Atomic _) n hyp             = hyp 0 (s≤s z≤n)
faithful-gen ga (Not φ) n hyp                = faithful-gen ga φ n hyp
faithful-gen ga (And φ ψ) n hyp =
  faithful-gen ga φ n (mk-φ-hyp ga φ ψ hyp) ,
  faithful-gen ga ψ _ (mk-ψ-hyp ga φ ψ n hyp)
faithful-gen ga (Or φ ψ) n hyp =
  faithful-gen ga φ n (mk-φ-hyp ga φ ψ hyp) ,
  faithful-gen ga ψ _ (mk-ψ-hyp ga φ ψ n hyp)
faithful-gen ga (Next φ) n hyp               = faithful-gen ga φ n hyp
faithful-gen ga (Always φ) n hyp             = faithful-gen ga φ n hyp
faithful-gen ga (Eventually φ) n hyp         = faithful-gen ga φ n hyp
faithful-gen ga (Until φ ψ) n hyp =
  faithful-gen ga φ n (mk-φ-hyp ga φ ψ hyp) ,
  faithful-gen ga ψ _ (mk-ψ-hyp ga φ ψ n hyp)
faithful-gen ga (Release φ ψ) n hyp =
  faithful-gen ga φ n (mk-φ-hyp ga φ ψ hyp) ,
  faithful-gen ga ψ _ (mk-ψ-hyp ga φ ψ n hyp)
faithful-gen ga (MetricEventually _ _ φ) n hyp = faithful-gen ga φ n hyp
faithful-gen ga (MetricAlways _ _ φ) n hyp     = faithful-gen ga φ n hyp
faithful-gen ga (MetricUntil _ _ φ ψ) n hyp =
  faithful-gen ga φ n (mk-φ-hyp ga φ ψ hyp) ,
  faithful-gen ga ψ _ (mk-ψ-hyp ga φ ψ n hyp)
faithful-gen ga (MetricRelease _ _ φ ψ) n hyp =
  faithful-gen ga φ n (mk-φ-hyp ga φ ψ hyp) ,
  faithful-gen ga ψ _ (mk-ψ-hyp ga φ ψ n hyp)

-- collectAtomsAcc matches the flattenAtoms specification.
collectAtomsAcc-spec : ∀ φ acc → collectAtomsAcc φ acc ≡ flattenAtoms φ ++ₗ acc
collectAtomsAcc-spec (Atomic _) acc           = refl
collectAtomsAcc-spec (Not φ) acc              = collectAtomsAcc-spec φ acc
collectAtomsAcc-spec (And φ ψ) acc
  rewrite collectAtomsAcc-spec ψ acc
  | collectAtomsAcc-spec φ (flattenAtoms ψ ++ₗ acc)
  = sym (++-assoc (flattenAtoms φ) (flattenAtoms ψ) acc)
collectAtomsAcc-spec (Or φ ψ) acc
  rewrite collectAtomsAcc-spec ψ acc
  | collectAtomsAcc-spec φ (flattenAtoms ψ ++ₗ acc)
  = sym (++-assoc (flattenAtoms φ) (flattenAtoms ψ) acc)
collectAtomsAcc-spec (Next φ) acc             = collectAtomsAcc-spec φ acc
collectAtomsAcc-spec (Always φ) acc           = collectAtomsAcc-spec φ acc
collectAtomsAcc-spec (Eventually φ) acc       = collectAtomsAcc-spec φ acc
collectAtomsAcc-spec (Until φ ψ) acc
  rewrite collectAtomsAcc-spec ψ acc
  | collectAtomsAcc-spec φ (flattenAtoms ψ ++ₗ acc)
  = sym (++-assoc (flattenAtoms φ) (flattenAtoms ψ) acc)
collectAtomsAcc-spec (Release φ ψ) acc
  rewrite collectAtomsAcc-spec ψ acc
  | collectAtomsAcc-spec φ (flattenAtoms ψ ++ₗ acc)
  = sym (++-assoc (flattenAtoms φ) (flattenAtoms ψ) acc)
collectAtomsAcc-spec (MetricEventually _ _ φ) acc = collectAtomsAcc-spec φ acc
collectAtomsAcc-spec (MetricAlways _ _ φ) acc     = collectAtomsAcc-spec φ acc
collectAtomsAcc-spec (MetricUntil _ _ φ ψ) acc
  rewrite collectAtomsAcc-spec ψ acc
  | collectAtomsAcc-spec φ (flattenAtoms ψ ++ₗ acc)
  = sym (++-assoc (flattenAtoms φ) (flattenAtoms ψ) acc)
collectAtomsAcc-spec (MetricRelease _ _ φ ψ) acc
  rewrite collectAtomsAcc-spec ψ acc
  | collectAtomsAcc-spec φ (flattenAtoms ψ ++ₗ acc)
  = sym (++-assoc (flattenAtoms φ) (flattenAtoms ψ) acc)

-- collectAtoms is exactly flattenAtoms.
collectAtoms-is-flattenAtoms : ∀ φ → collectAtoms φ ≡ flattenAtoms φ
collectAtoms-is-flattenAtoms φ =
  trans (collectAtomsAcc-spec φ []) (++-identityʳ (flattenAtoms φ))

-- Main theorem: atom indices in indexFormula look up correctly in collectAtoms.
collectAtoms-faithful : ∀ φ → Faithful (collectAtoms φ) φ 0
collectAtoms-faithful φ rewrite collectAtoms-is-flattenAtoms φ =
  faithful-gen (flattenAtoms φ) φ 0
    (λ k _ → cong (lookupAtom (flattenAtoms φ)) (+-identityʳ k))

-- mkPredTable evaluates the predicate found by lookupAtom.
mkPredTable-lookup : ∀ dbc cache atoms k pred frame →
  lookupAtom atoms k ≡ just pred →
  mkPredTable dbc cache atoms k frame ≡ evalPredicateTV dbc cache pred (TimedFrame.frame frame)
mkPredTable-lookup dbc cache atoms k pred frame eq rewrite eq = refl

-- ============================================================================
-- PROPERTY 27: indexHelper bound — atom indices stay below the counter
-- ============================================================================
--
-- Proves that every atom index in a stepped formula is < length atoms.
-- Justifies the dead-code claim for the `nothing → Unknown` branch in
-- mkPredTable: lookupAtom is total over reachable indices.
--
-- Layered structure:
--   1. AllBelow predicate: every Atomic in an LTL ℕ has index < bound
--   2. indexHelper-bound: indexHelper produces a formula bounded by its counter
--   3. simplify preserves AllBelow (absorb only drops/rearranges atoms)
--   4. stepL preserves AllBelow (Continue branches keep the same atom indices)
--   5. lookupAtom is total whenever the index is in range
--   6. Composed corollary: mkPredTable on a bounded index agrees with the
--      direct evaluator (no nothing fallback fires)

-- Every Atomic in the formula has index strictly below the bound.
AllBelow : ℕ → LTL ℕ → Set
AllBelow b (Atomic n)                  = n < b
AllBelow b (Not φ)                     = AllBelow b φ
AllBelow b (And φ ψ)                   = AllBelow b φ × AllBelow b ψ
AllBelow b (Or φ ψ)                    = AllBelow b φ × AllBelow b ψ
AllBelow b (Next φ)                    = AllBelow b φ
AllBelow b (Always φ)                  = AllBelow b φ
AllBelow b (Eventually φ)              = AllBelow b φ
AllBelow b (Until φ ψ)                 = AllBelow b φ × AllBelow b ψ
AllBelow b (Release φ ψ)               = AllBelow b φ × AllBelow b ψ
AllBelow b (MetricEventually _ _ φ)    = AllBelow b φ
AllBelow b (MetricAlways _ _ φ)        = AllBelow b φ
AllBelow b (MetricUntil _ _ φ ψ)       = AllBelow b φ × AllBelow b ψ
AllBelow b (MetricRelease _ _ φ ψ)     = AllBelow b φ × AllBelow b ψ

-- Weakening: a smaller bound implies a larger bound.
AllBelow-mono : ∀ {b₁ b₂} φ → b₁ ≤ b₂ → AllBelow b₁ φ → AllBelow b₂ φ
AllBelow-mono (Atomic n) b₁≤b₂ n<b₁                  = ≤-trans n<b₁ b₁≤b₂
AllBelow-mono (Not φ) b₁≤b₂ p                        = AllBelow-mono φ b₁≤b₂ p
AllBelow-mono (And φ ψ) b₁≤b₂ (pφ , pψ)              =
  AllBelow-mono φ b₁≤b₂ pφ , AllBelow-mono ψ b₁≤b₂ pψ
AllBelow-mono (Or φ ψ) b₁≤b₂ (pφ , pψ)               =
  AllBelow-mono φ b₁≤b₂ pφ , AllBelow-mono ψ b₁≤b₂ pψ
AllBelow-mono (Next φ) b₁≤b₂ p                       = AllBelow-mono φ b₁≤b₂ p
AllBelow-mono (Always φ) b₁≤b₂ p                     = AllBelow-mono φ b₁≤b₂ p
AllBelow-mono (Eventually φ) b₁≤b₂ p                 = AllBelow-mono φ b₁≤b₂ p
AllBelow-mono (Until φ ψ) b₁≤b₂ (pφ , pψ)            =
  AllBelow-mono φ b₁≤b₂ pφ , AllBelow-mono ψ b₁≤b₂ pψ
AllBelow-mono (Release φ ψ) b₁≤b₂ (pφ , pψ)          =
  AllBelow-mono φ b₁≤b₂ pφ , AllBelow-mono ψ b₁≤b₂ pψ
AllBelow-mono (MetricEventually _ _ φ) b₁≤b₂ p       = AllBelow-mono φ b₁≤b₂ p
AllBelow-mono (MetricAlways _ _ φ) b₁≤b₂ p           = AllBelow-mono φ b₁≤b₂ p
AllBelow-mono (MetricUntil _ _ φ ψ) b₁≤b₂ (pφ , pψ)  =
  AllBelow-mono φ b₁≤b₂ pφ , AllBelow-mono ψ b₁≤b₂ pψ
AllBelow-mono (MetricRelease _ _ φ ψ) b₁≤b₂ (pφ , pψ) =
  AllBelow-mono φ b₁≤b₂ pφ , AllBelow-mono ψ b₁≤b₂ pψ

-- The counter never decreases.
indexHelper-mono : ∀ (φ : LTL SignalPredicate) start → start ≤ proj₂ (indexHelper φ start)
indexHelper-mono (Atomic _) start                    = n≤1+n start
indexHelper-mono (Not φ) start                       = indexHelper-mono φ start
indexHelper-mono (And φ ψ) start                     =
  ≤-trans (indexHelper-mono φ start)
          (indexHelper-mono ψ (proj₂ (indexHelper φ start)))
indexHelper-mono (Or φ ψ) start                      =
  ≤-trans (indexHelper-mono φ start)
          (indexHelper-mono ψ (proj₂ (indexHelper φ start)))
indexHelper-mono (Next φ) start                      = indexHelper-mono φ start
indexHelper-mono (Always φ) start                    = indexHelper-mono φ start
indexHelper-mono (Eventually φ) start                = indexHelper-mono φ start
indexHelper-mono (Until φ ψ) start                   =
  ≤-trans (indexHelper-mono φ start)
          (indexHelper-mono ψ (proj₂ (indexHelper φ start)))
indexHelper-mono (Release φ ψ) start                 =
  ≤-trans (indexHelper-mono φ start)
          (indexHelper-mono ψ (proj₂ (indexHelper φ start)))
indexHelper-mono (MetricEventually _ _ φ) start      = indexHelper-mono φ start
indexHelper-mono (MetricAlways _ _ φ) start          = indexHelper-mono φ start
indexHelper-mono (MetricUntil _ _ φ ψ) start         =
  ≤-trans (indexHelper-mono φ start)
          (indexHelper-mono ψ (proj₂ (indexHelper φ start)))
indexHelper-mono (MetricRelease _ _ φ ψ) start       =
  ≤-trans (indexHelper-mono φ start)
          (indexHelper-mono ψ (proj₂ (indexHelper φ start)))

-- Main theorem: every atom in the indexed formula is bounded by the final counter.
indexHelper-bound : ∀ (φ : LTL SignalPredicate) start →
  AllBelow (proj₂ (indexHelper φ start)) (proj₁ (indexHelper φ start))
indexHelper-bound (Atomic _) start                   = ≤-refl
indexHelper-bound (Not φ) start                      = indexHelper-bound φ start
indexHelper-bound (And φ ψ) start                    =
  AllBelow-mono (proj₁ (indexHelper φ start))
    (indexHelper-mono ψ (proj₂ (indexHelper φ start)))
    (indexHelper-bound φ start)
  , indexHelper-bound ψ (proj₂ (indexHelper φ start))
indexHelper-bound (Or φ ψ) start                     =
  AllBelow-mono (proj₁ (indexHelper φ start))
    (indexHelper-mono ψ (proj₂ (indexHelper φ start)))
    (indexHelper-bound φ start)
  , indexHelper-bound ψ (proj₂ (indexHelper φ start))
indexHelper-bound (Next φ) start                     = indexHelper-bound φ start
indexHelper-bound (Always φ) start                   = indexHelper-bound φ start
indexHelper-bound (Eventually φ) start               = indexHelper-bound φ start
indexHelper-bound (Until φ ψ) start                  =
  AllBelow-mono (proj₁ (indexHelper φ start))
    (indexHelper-mono ψ (proj₂ (indexHelper φ start)))
    (indexHelper-bound φ start)
  , indexHelper-bound ψ (proj₂ (indexHelper φ start))
indexHelper-bound (Release φ ψ) start                =
  AllBelow-mono (proj₁ (indexHelper φ start))
    (indexHelper-mono ψ (proj₂ (indexHelper φ start)))
    (indexHelper-bound φ start)
  , indexHelper-bound ψ (proj₂ (indexHelper φ start))
indexHelper-bound (MetricEventually _ _ φ) start     = indexHelper-bound φ start
indexHelper-bound (MetricAlways _ _ φ) start         = indexHelper-bound φ start
indexHelper-bound (MetricUntil _ _ φ ψ) start        =
  AllBelow-mono (proj₁ (indexHelper φ start))
    (indexHelper-mono ψ (proj₂ (indexHelper φ start)))
    (indexHelper-bound φ start)
  , indexHelper-bound ψ (proj₂ (indexHelper φ start))
indexHelper-bound (MetricRelease _ _ φ ψ) start      =
  AllBelow-mono (proj₁ (indexHelper φ start))
    (indexHelper-mono ψ (proj₂ (indexHelper φ start)))
    (indexHelper-bound φ start)
  , indexHelper-bound ψ (proj₂ (indexHelper φ start))

-- Corollary: indexFormula is bounded by length (collectAtoms φ).
indexFormula-bound : ∀ (φ : LTL SignalPredicate) →
  AllBelow (length (collectAtoms φ)) (indexFormula φ)
indexFormula-bound φ
  rewrite collectAtoms-is-flattenAtoms φ
  | sym (+-identityʳ (length (flattenAtoms φ)))
  | sym (indexHelper-counter φ 0)
  = indexHelper-bound φ 0

-- ============================================================================
-- PROPERTY 27 (continued): simplify and stepL preserve AllBelow
-- ============================================================================

-- ResultBound lifts AllBelow to StepResult: terminal results carry no atom
-- payload, so they're trivially bounded; only Continue carries a formula
-- that needs the AllBelow proof.
ResultBound : ℕ → StepResult LTLProc → Set
ResultBound _ (Violated _)    = ⊤
ResultBound _ Satisfied       = ⊤
ResultBound b (Continue _ φ)  = AllBelow b φ

-- combineAnd preserves the bound: it only short-circuits or wraps in And.
combineAnd-bound : ∀ {b} (r₁ r₂ : StepResult LTLProc) →
  ResultBound b r₁ → ResultBound b r₂ → ResultBound b (combineAnd r₁ r₂)
combineAnd-bound (Violated _) (Violated _)   _   _   = tt
combineAnd-bound (Violated _) Satisfied      _   _   = tt
combineAnd-bound (Violated _) (Continue _ _) _   _   = tt
combineAnd-bound Satisfied    (Violated _)   _   _   = tt
combineAnd-bound Satisfied    Satisfied      _   _   = tt
combineAnd-bound Satisfied    (Continue _ _) _   p₂  = p₂
combineAnd-bound (Continue _ _) (Violated _) _   _   = tt
combineAnd-bound (Continue _ _) Satisfied    p₁  _   = p₁
combineAnd-bound (Continue _ _) (Continue _ _) p₁ p₂ = (p₁ , p₂)

-- combineOr preserves the bound: dual of combineAnd, with Satisfied/Violated roles swapped.
combineOr-bound : ∀ {b} (r₁ r₂ : StepResult LTLProc) →
  ResultBound b r₁ → ResultBound b r₂ → ResultBound b (combineOr r₁ r₂)
combineOr-bound Satisfied      _              _  _   = tt
combineOr-bound (Violated _)   Satisfied      _  _   = tt
combineOr-bound (Continue _ _) Satisfied      _  _   = tt
combineOr-bound (Violated _)   (Violated _)   _  _   = tt
combineOr-bound (Violated _)   (Continue _ _) _  p₂  = p₂
combineOr-bound (Continue _ _) (Violated _)   p₁ _   = p₁
combineOr-bound (Continue _ _) (Continue _ _) p₁ p₂  = (p₁ , p₂)

-- absorb only drops or rearranges existing subformulas; it never introduces
-- new atoms. We split into per-And/Or helpers so each clause mirrors absorb's
-- pattern matching exactly.
private
  absorb-And-bound : ∀ {b} φ ψ → AllBelow b (And φ ψ) → AllBelow b (absorb (And φ ψ))
  absorb-And-bound φ (Atomic _)              p          = p
  absorb-And-bound φ (Not _)                 p          = p
  absorb-And-bound φ (And b' c) (pφ , (pb , pc)) with φ ≡ᵇ-proc b'
  ... | true  = (pφ , pc)
  ... | false = (pφ , (pb , pc))
  absorb-And-bound φ (Or _ _)                p          = p
  absorb-And-bound φ (Next _)                p          = p
  absorb-And-bound φ (Always ψ') (pφ , pψ') with φ ≡ᵇ-proc ψ' | finalizesHolds φ
  ... | true  | true  = pψ'
  ... | true  | false = (pφ , pψ')
  ... | false | true  = (pφ , pψ')
  ... | false | false = (pφ , pψ')
  absorb-And-bound φ (Eventually _)          p          = p
  absorb-And-bound φ (Until _ _)             p          = p
  absorb-And-bound φ (Release _ _)           p          = p
  absorb-And-bound φ (MetricEventually _ _ _) p         = p
  absorb-And-bound φ (MetricAlways _ _ _)    p          = p
  absorb-And-bound φ (MetricUntil _ _ _ _)   p          = p
  absorb-And-bound φ (MetricRelease _ _ _ _) p          = p

  absorb-Or-bound : ∀ {b} φ ψ → AllBelow b (Or φ ψ) → AllBelow b (absorb (Or φ ψ))
  absorb-Or-bound φ (Atomic _)               p          = p
  absorb-Or-bound φ (Not _)                  p          = p
  absorb-Or-bound φ (And _ _)                p          = p
  absorb-Or-bound φ (Or b' c) (pφ , (pb , pc)) with φ ≡ᵇ-proc b'
  ... | true  = (pφ , pc)
  ... | false = (pφ , (pb , pc))
  absorb-Or-bound φ (Next _)                 p          = p
  absorb-Or-bound φ (Always _)               p          = p
  absorb-Or-bound φ (Eventually ψ') (pφ , pψ') with φ ≡ᵇ-proc ψ' | finalizesFails φ
  ... | true  | true  = pψ'
  ... | true  | false = (pφ , pψ')
  ... | false | true  = (pφ , pψ')
  ... | false | false = (pφ , pψ')
  absorb-Or-bound φ (Until _ _)              p          = p
  absorb-Or-bound φ (Release _ _)            p          = p
  absorb-Or-bound φ (MetricEventually _ _ _) p          = p
  absorb-Or-bound φ (MetricAlways _ _ _)     p          = p
  absorb-Or-bound φ (MetricUntil _ _ _ _)    p          = p
  absorb-Or-bound φ (MetricRelease _ _ _ _)  p          = p

absorb-bound : ∀ {b} φ → AllBelow b φ → AllBelow b (absorb φ)
absorb-bound (And φ ψ) p                     = absorb-And-bound φ ψ p
absorb-bound (Or φ ψ) p                      = absorb-Or-bound φ ψ p
absorb-bound (Atomic _) p                    = p
absorb-bound (Not _) p                       = p
absorb-bound (Next _) p                      = p
absorb-bound (Always _) p                    = p
absorb-bound (Eventually _) p                = p
absorb-bound (Until _ _) p                   = p
absorb-bound (Release _ _) p                 = p
absorb-bound (MetricEventually _ _ _) p      = p
absorb-bound (MetricAlways _ _ _) p          = p
absorb-bound (MetricUntil _ _ _ _) p         = p
absorb-bound (MetricRelease _ _ _ _) p       = p

-- simplify recurses into right children of And/Or only, then absorbs.
simplify-bound : ∀ {b} φ → AllBelow b φ → AllBelow b (simplify φ)
simplify-bound (And a b) (pa , pb)           =
  absorb-bound (And a (simplify b)) (pa , simplify-bound b pb)
simplify-bound (Or a b) (pa , pb)            =
  absorb-bound (Or a (simplify b)) (pa , simplify-bound b pb)
simplify-bound (Atomic _) p                  = p
simplify-bound (Not _) p                     = p
simplify-bound (Next _) p                    = p
simplify-bound (Always _) p                  = p
simplify-bound (Eventually _) p              = p
simplify-bound (Until _ _) p                 = p
simplify-bound (Release _ _) p               = p
simplify-bound (MetricEventually _ _ _) p    = p
simplify-bound (MetricAlways _ _ _) p        = p
simplify-bound (MetricUntil _ _ _ _) p       = p
simplify-bound (MetricRelease _ _ _ _) p     = p

-- stepL never introduces new atom indices: every Continue branch reuses
-- the input formula's atoms (possibly stripping subformulas via combine).
stepL-bound : ∀ {b} (φ : LTLProc) (table : PredTable) (frame : TimedFrame) →
  AllBelow b φ → ResultBound b (stepL table φ frame)
stepL-bound (Atomic n) table frame n<b with table n frame
... | True    = tt
... | False   = tt
... | Unknown = n<b
... | Pending = n<b
stepL-bound (Not φ) table frame p
  with stepL table φ frame | stepL-bound φ table frame p
... | Continue _ _ | ih = ih
... | Violated _   | _  = tt
... | Satisfied    | _  = tt
stepL-bound (And φ ψ) table frame (pφ , pψ) =
  combineAnd-bound (stepL table φ frame) (stepL table ψ frame)
    (stepL-bound φ table frame pφ)
    (stepL-bound ψ table frame pψ)
stepL-bound (Or φ ψ) table frame (pφ , pψ) =
  combineOr-bound (stepL table φ frame) (stepL table ψ frame)
    (stepL-bound φ table frame pφ)
    (stepL-bound ψ table frame pψ)
stepL-bound (Next φ) table frame p = p
stepL-bound (Always φ) table frame p =
  combineAnd-bound (stepL table φ frame) (Continue 0 (Always φ))
    (stepL-bound φ table frame p)
    p
stepL-bound (Eventually φ) table frame p =
  combineOr-bound (stepL table φ frame) (Continue 0 (Eventually φ))
    (stepL-bound φ table frame p)
    p
stepL-bound (Until φ ψ) table frame (pφ , pψ) =
  combineOr-bound (stepL table ψ frame)
                  (combineAnd (stepL table φ frame) (Continue 0 (Until φ ψ)))
    (stepL-bound ψ table frame pψ)
    (combineAnd-bound (stepL table φ frame) (Continue 0 (Until φ ψ))
       (stepL-bound φ table frame pφ)
       (pφ , pψ))
stepL-bound (Release φ ψ) table frame (pφ , pψ) =
  combineAnd-bound (stepL table ψ frame)
                   (combineOr (stepL table φ frame) (Continue 0 (Release φ ψ)))
    (stepL-bound ψ table frame pψ)
    (combineOr-bound (stepL table φ frame) (Continue 0 (Release φ ψ))
       (stepL-bound φ table frame pφ)
       (pφ , pψ))
stepL-bound (MetricEventually w s φ) table frame p
  with (timestampℕ frame ∸ decodeStart s (timestampℕ frame)) ≤ᵇ w
... | false = tt
... | true  =
  combineOr-bound (stepL table φ frame)
                  (Continue _ (MetricEventually w (suc (decodeStart s (timestampℕ frame))) φ))
    (stepL-bound φ table frame p)
    p
stepL-bound (MetricAlways w s φ) table frame p
  with (timestampℕ frame ∸ decodeStart s (timestampℕ frame)) ≤ᵇ w
... | false = tt
... | true  =
  combineAnd-bound (stepL table φ frame)
                   (Continue _ (MetricAlways w (suc (decodeStart s (timestampℕ frame))) φ))
    (stepL-bound φ table frame p)
    p
stepL-bound (MetricUntil w s φ ψ) table frame (pφ , pψ)
  with (timestampℕ frame ∸ decodeStart s (timestampℕ frame)) ≤ᵇ w
... | false = tt
... | true  =
  combineOr-bound (stepL table ψ frame)
                  (combineAnd (stepL table φ frame)
                              (Continue _ (MetricUntil w (suc (decodeStart s (timestampℕ frame))) φ ψ)))
    (stepL-bound ψ table frame pψ)
    (combineAnd-bound (stepL table φ frame)
                      (Continue _ (MetricUntil w (suc (decodeStart s (timestampℕ frame))) φ ψ))
       (stepL-bound φ table frame pφ)
       (pφ , pψ))
stepL-bound (MetricRelease w s φ ψ) table frame (pφ , pψ)
  with (timestampℕ frame ∸ decodeStart s (timestampℕ frame)) ≤ᵇ w
... | false = tt
... | true  =
  combineAnd-bound (stepL table ψ frame)
                   (combineOr (stepL table φ frame)
                              (Continue _ (MetricRelease w (suc (decodeStart s (timestampℕ frame))) φ ψ)))
    (stepL-bound ψ table frame pψ)
    (combineOr-bound (stepL table φ frame)
                     (Continue _ (MetricRelease w (suc (decodeStart s (timestampℕ frame))) φ ψ))
       (stepL-bound φ table frame pφ)
       (pφ , pψ))

-- ============================================================================
-- PROPERTY 27 (continued): lookupAtom totality + mkPredTable corollary
-- ============================================================================

-- lookupAtom is total whenever the index is in range.
lookupAtom-total : ∀ (atoms : List SignalPredicate) k → k < length atoms →
  ∃[ pred ] lookupAtom atoms k ≡ just pred
lookupAtom-total []       k       ()
lookupAtom-total (x ∷ xs) zero    _         = x , refl
lookupAtom-total (x ∷ xs) (suc k) (s≤s k<n) = lookupAtom-total xs k k<n

-- Composed corollary: for any in-range index, mkPredTable evaluates the
-- looked-up predicate (the `nothing → Unknown` branch is unreachable).
mkPredTable-bounded : ∀ dbc cache atoms k frame → k < length atoms →
  ∃[ pred ] (lookupAtom atoms k ≡ just pred ×
             mkPredTable dbc cache atoms k frame
               ≡ evalPredicateTV dbc cache pred (TimedFrame.frame frame))
mkPredTable-bounded dbc cache atoms k frame k< =
  let (pred , eq) = lookupAtom-total atoms k k<
  in pred , eq , mkPredTable-lookup dbc cache atoms k pred frame eq
