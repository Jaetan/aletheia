{-# OPTIONS --safe --without-K #-}

-- B.3.d Layer 3 3d.5.c-γ.3 — DSL-based receivers roundtrip.
--
-- The universal property `∀ pos cr suffix → SuffixStops isReceiverCont
-- suffix → parse canonicalReceiversFmt pos (emit canonicalReceiversFmt
-- cr ++ suffix) ≡ just (mkResult cr …)` discharged via the framework's
-- `roundtrip canonicalReceiversFmt` plus an `EmitsOK` constructor.
--
-- Gate measurement vs the pre-ε.3 per-construct proof in
-- `Properties/Topology/Receivers.agda` (646 file-LOC / 417
-- strict-code-LOC).  The DSL proof collapses the strip lemmas into
-- the iso bijection (γ.1's `fwd-bwd`) and the per-iteration roundtrip
-- into the universal `manyHelper-roundtrip-list` (Format.agda).
--
-- Post-ε.3, `Properties/Topology/Receivers.agda` is a slim bridge
-- (~70 strict-code-LOC) that derives a flat `parseReceiverList-
-- roundtrip` from this DSL theorem; the 3d.3 dispatcher's
-- receiver-list step uses the bridge directly.  See ε.3 commit notes
-- for the cycle resolution that enabled the migration.
module Aletheia.DBC.TextParser.Format.Receivers.Roundtrip where

open import Data.Bool using (Bool; true; false; _∨_)
open import Data.Char using (Char; _≈ᵇ_)
open import Data.List using (List; []; _∷_) renaming (_++_ to _++ₗ_)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (s≤s; z≤n)
open import Data.Product using (_,_)
open import Data.Unit using (tt)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl)

open import Aletheia.Parser.Combinators
  using (mkResult; advancePositions)
open import Aletheia.DBC.Identifier using (Identifier; isIdentCont)
open import Aletheia.DBC.CanonicalReceivers
  using (CanonicalReceivers; mkCanonical)

open import Aletheia.DBC.TextParser.DecRatParse.Properties
  using (SuffixStops; []-stop; ∷-stop)
open import Aletheia.DBC.TextParser.Format
  using (ident; withPrefix;
         emit; parse; EmitsOK; EmitsOKMany;
         []-fails; ∷-cons; roundtrip)
open import Aletheia.DBC.TextParser.Format.Receivers
  using (canonicalReceiversFmt)

-- ============================================================================
-- isReceiverCont — receivers character predicate
-- ============================================================================

-- Combined inner-many stop condition (`isIdentCont` for
-- parseIdentifier's inner satisfy-loop) and outer-many stop condition
-- (`,` separator).  The single SuffixStops precondition discharges
-- both.  Re-exported by `Properties/Topology/Receivers` (the post-ε.3
-- slim bridge) for backwards-compatible facade exports.
isReceiverCont : Char → Bool
isReceiverCont c = isIdentCont c ∨ (c ≈ᵇ ',')

-- ============================================================================
-- DISJUNCTION ELIMINATION HELPERS
-- ============================================================================

private
  -- `(b₁ ∨ b₂) ≡ false` ⇒ `b₁ ≡ false ∧ b₂ ≡ false`.  By case on the
  -- implicit Bools.  Used to peel `isReceiverCont c ≡ false` into the
  -- two pieces needed: `isIdentCont c ≡ false` (for the inner-ident's
  -- SuffixStops) and `c ≈ᵇ ',' ≡ false` (for the comma-prefix's
  -- termination certificate).
  ∨-elim-isIdentCont : ∀ (c : Char)
    → isReceiverCont c ≡ false → isIdentCont c ≡ false
  ∨-elim-isIdentCont c eq with isIdentCont c | c ≈ᵇ ','
  ... | false | _ = refl
  ... | true  | _ = case eq of λ ()

  ∨-elim-comma : ∀ (c : Char)
    → isReceiverCont c ≡ false → (c ≈ᵇ ',') ≡ false
  ∨-elim-comma c eq with isIdentCont c | c ≈ᵇ ','
  ... | false | false = refl
  ... | false | true  = case eq of λ ()
  ... | true  | _     = case eq of λ ()

  -- SuffixStops isReceiverCont ⇒ SuffixStops isIdentCont.  Mirrors
  -- `Properties/Topology/Receivers.isReceiverCont-stop→isIdentCont-stop`;
  -- inlined for standalone-ness.
  isReceiverCont→isIdentCont : ∀ (suffix : List Char)
    → SuffixStops isReceiverCont suffix → SuffixStops isIdentCont suffix
  isReceiverCont→isIdentCont []      _          = []-stop
  isReceiverCont→isIdentCont (c ∷ _) (∷-stop h) =
    ∷-stop (∨-elim-isIdentCont c h)

-- ============================================================================
-- TERMINATION CERTIFICATE — `parse (withPrefix "," ident)` rejects
-- a non-comma-headed suffix
-- ============================================================================

  -- The inner-many's `[]-fails` constructor needs `parse (withPrefix
  -- "," ident) pos suffix ≡ nothing` for the trailing input.  After
  -- all comma-prefixed entries are consumed, the residual is the
  -- caller's `suffix`, whose head is non-comma by `SuffixStops
  -- isReceiverCont`.  `rewrite` substitutes `c ≈ᵇ ','` for `false`,
  -- letting `satisfy`'s with-pattern reduce to `nothing`.
  parse-withPrefix-comma-fails : ∀ pos suffix
    → SuffixStops isReceiverCont suffix
    → parse (withPrefix (',' ∷ []) ident) pos suffix ≡ nothing
  parse-withPrefix-comma-fails pos []      _          = refl
  parse-withPrefix-comma-fails pos (c ∷ _) (∷-stop ss)
    rewrite ∨-elim-comma c ss = refl

-- ============================================================================
-- WELL-FORMEDNESS BUILDER — EmitsOKMany (withPrefix "," ident) over the tail
-- ============================================================================

  -- Inductive on `t` (the comma-prefixed tail of the receivers list).
  -- Each iteration carries:
  --   * `wf-s` : EmitsOK (withPrefix "," ident) s (next-residual-suffix)
  --   * `ne-s` : 0 < length (emit (withPrefix "," ident) s) = 0 < suc _
  --   * recurse on the rest of `t`.
  -- The two non-empty branches differ only on what the next residual
  -- after `s` is: empty `rest` reduces to the caller's `suffix`,
  -- non-empty to the next entry's leading `,`.  Splitting on `rest`
  -- lets Agda reduce the head definitionally for `∷-stop refl`.
  build-tail-EmitsOKMany : ∀ (t : List Identifier) (suffix : List Char)
    → SuffixStops isReceiverCont suffix
    → EmitsOKMany (withPrefix (',' ∷ []) ident) t suffix
  build-tail-EmitsOKMany [] suffix ss =
    []-fails (λ pos → parse-withPrefix-comma-fails pos suffix ss)
  build-tail-EmitsOKMany (s ∷ []) suffix ss =
    ∷-cons (tt , isReceiverCont→isIdentCont suffix ss)
           (s≤s z≤n)
           (build-tail-EmitsOKMany [] suffix ss)
  build-tail-EmitsOKMany (s ∷ s' ∷ rest) suffix ss =
    ∷-cons (tt , ∷-stop refl)
           (s≤s z≤n)
           (build-tail-EmitsOKMany (s' ∷ rest) suffix ss)

-- ============================================================================
-- WELL-FORMEDNESS BUILDER — top-level EmitsOK canonicalReceiversFmt
-- ============================================================================

-- `canonicalReceiversFmt = iso _ ψ _ (pair ident (many (withPrefix
-- "," ident)))`.  EmitsOK on iso passes through ψ (= bwd) which
-- produces three shapes per `cr.list`:
--   * `[]`           → `(vectorXXX-id , [])`
--   * `(r ∷ [])`     → `(r , [])`
--   * `(r ∷ s ∷ rest)` → `(r , s ∷ rest)`
-- All three reduce the ident-step's residual head to: caller's
-- suffix (cases 1+2) or `,` (case 3).  Cases 1+2 borrow the
-- caller's SuffixStops; case 3 closes via `∷-stop refl` because the
-- head is the literal comma.
--
-- Public so downstream chunks (e.g. `tailFmt` in `Format.SignalLine`)
-- can compose it inside larger `EmitsOK` certificates.
build-emits-ok : ∀ (cr : CanonicalReceivers) (suffix : List Char)
  → SuffixStops isReceiverCont suffix
  → EmitsOK canonicalReceiversFmt cr suffix
build-emits-ok (mkCanonical [] _) suffix ss =
  isReceiverCont→isIdentCont suffix ss ,
  build-tail-EmitsOKMany [] suffix ss
build-emits-ok (mkCanonical (r ∷ []) _) suffix ss =
  isReceiverCont→isIdentCont suffix ss ,
  build-tail-EmitsOKMany [] suffix ss
build-emits-ok (mkCanonical (r ∷ s ∷ rest) _) suffix ss =
  ∷-stop refl ,
  build-tail-EmitsOKMany (s ∷ rest) suffix ss

-- ============================================================================
-- THE GATE: DSL receivers roundtrip
-- ============================================================================

-- DSL-side universal property for receivers parsing.  Body is one
-- `roundtrip` call backed by `build-emits-ok` from the SuffixStops
-- precondition.  Total file LOC for the proof is the gate measurement
-- vs `Properties/Topology/Receivers` (646 LOC).
canonicalReceivers-roundtrip : ∀ pos (cr : CanonicalReceivers)
                                  (suffix : List Char)
  → SuffixStops isReceiverCont suffix
  → parse canonicalReceiversFmt pos
      (emit canonicalReceiversFmt cr ++ₗ suffix)
    ≡ just (mkResult cr
             (advancePositions pos (emit canonicalReceiversFmt cr))
             suffix)
canonicalReceivers-roundtrip pos cr suffix ss =
  roundtrip canonicalReceiversFmt pos cr suffix
    (build-emits-ok cr suffix ss)
