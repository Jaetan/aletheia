-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Mux-presence and master-coherence deciders — the SSOT for the
-- `MultiValueMuxSelector` and `MuxMasterIncoherent` diagnostics.
--
-- Two runtime surfaces consume these deciders:
--   • the text-round-trip WF checker (`Aletheia.DBC.TextParser.WellFormedCheck`,
--     which re-exports this module publicly — the `wfps` / `mc` fields of
--     `WellFormedTextDBCAgg`), and
--   • the structural validator's warning-class mirrors
--     (`Aletheia.DBC.Validator.Checks`, the multi-value-mux-selector and
--     mux-master-incoherent checks), so `validateDBC` and the DBC-loading
--     routes name these round-trip-fatal shapes without a second
--     implementation.
--
-- Extracted as a Foundations submodule (the house cycle-break/closure
-- pattern) so the validator's import closure stays free of the text-parser
-- closure that `WellFormedCheck` itself carries: this module reaches only
-- `TextFormatter.Topology` (for `findMuxMaster`) and the shared
-- Types/Identifier/Combinators substrate — see the heap note in
-- `Aletheia.Protocol.Handlers.LoadDBC`.
--
-- Cold-path (per-DBC ingest / format, never per-frame), so `Dec` allocation
-- is acceptable here; the hot-path performance rule applies to streaming only.
module Aletheia.DBC.TextParser.WellFormedCheck.Foundations where

open import Data.Char using (Char) renaming (_≟_ to _≟ᶜ_)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (find; lose)
open import Data.List.NonEmpty using (List⁺) renaming (_∷_ to _∷⁺_)
import Data.List.Properties as ListProps
open import Data.List.Relation.Unary.All as All using (all?)
open import Data.List.Relation.Unary.Any using (any?)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open import Data.String using (String) renaming (_++_ to _++ₛ_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import Relation.Nullary.Decidable using (Dec; yes; no; _×-dec_)

open import Aletheia.DBC.Identifier using (Identifier; nameStr)
open import Aletheia.DBC.Formatter.WellFormedText.Foundations using (MasterCoherent; mc-no-mux; mc-mux)
open import Aletheia.DBC.TextFormatter.Topology using (findMuxMaster)
open import Aletheia.DBC.Types using
  ( ValidationIssue; mkIssue; IsWarning
  ; DBCSignal; SignalPresence; Always; When
  ; MultiValueMuxSelector; MuxMasterIncoherent )
open import Aletheia.DBC.Validity.Combinators using (requireDec)

-- ── single-value presence (WF field `wfps`) ──────────────────────────────────
--
-- EXPOSED SCRUTINEE: `pGo` takes the `SignalPresence` as an explicit argument
-- and pattern-matches structurally — deliberately NO `with` here.  The checker
-- is then a plain function of the scrutinee, so the soundness proof can
-- `with … in eq` the scrutinee EXTERNALLY and this application reduces cleanly
-- (past `with`-reduction failures came from `with`-abstracting internally).

pGo : SignalPresence → String → List ValidationIssue
pGo Always                  _    = []
pGo (When _ (_ ∷⁺ []))      _    = []
pGo (When _ (_ ∷⁺ (_ ∷ _))) name =
  mkIssue IsWarning MultiValueMuxSelector
    ("signal '" ++ₛ name
     ++ₛ "': multi-value mux selector — text form emits only the first selector value")
  ∷ []

presenceIssue : DBCSignal → List ValidationIssue
presenceIssue s = pGo (DBCSignal.presence s) (nameStr (DBCSignal.name s))

-- ── master coherence (WF field `mc` = MasterCoherent), decided directly ─────
--
-- `MasterCoherent` (Formatter/WellFormedText/Foundations.agda) = single `Always` master, and
-- every `When` selector names it.  Decided by stock `Dec`: `any? (masterOk? n)`
-- exhibits the master (with the `∈` witness `mc-mux` needs, via `find`) and
-- `all? (whenOk? n)` lands the slaves `All` field verbatim, so `requireDec-sound`
-- turns "no issue" into the WF field with no Bool-reflection bridge.  `mcGo?`
-- takes the `findMuxMaster` result as an argument together with its equation
-- (`masterCoherent?` instantiates `refl`), keeping the case-split `with`-free
-- on the scrutinee.

isAlways? : (p : SignalPresence) → Dec (p ≡ Always)
isAlways? Always     = yes refl
isAlways? (When _ _) = no λ ()

-- The master conjunct of `mc-mux`: the signal carries the master's name and is
-- `Always`-present — exactly the constructor's name/presence witness pair.
MasterOk : List Char → DBCSignal → Set
MasterOk n s = (Identifier.name (DBCSignal.name s) ≡ n) × (DBCSignal.presence s ≡ Always)

masterOk? : (n : List Char) (s : DBCSignal) → Dec (MasterOk n s)
masterOk? n s =
  ListProps.≡-dec _≟ᶜ_ (Identifier.name (DBCSignal.name s)) n
    ×-dec isAlways? (DBCSignal.presence s)

-- The slave conjunct of `mc-mux`, stated in the SAME ∀-shape as the
-- constructor's `All` field, so `all? (whenOk? n) sigs` produces that field
-- with no per-element conversion.
WhenNames : List Char → SignalPresence → Set
WhenNames n p = ∀ (m : Identifier) (vs : List⁺ ℕ) → p ≡ When m vs → Identifier.name m ≡ n

whenNames? : (n : List Char) (p : SignalPresence) → Dec (WhenNames n p)
whenNames? n Always      = yes λ _ _ ()
whenNames? n (When m vs) with ListProps.≡-dec _≟ᶜ_ (Identifier.name m) n
... | yes eq = yes λ { _ _ refl → eq }
... | no ¬eq = no λ f → ¬eq (f m vs refl)

whenOk? : (n : List Char) (s : DBCSignal) → Dec (WhenNames n (DBCSignal.presence s))
whenOk? n s = whenNames? n (DBCSignal.presence s)

private
  just≢nothing : ∀ {A : Set} {x : A} → just x ≡ nothing → ⊥
  just≢nothing ()

mcGo? : (mm : Maybe (List Char)) (sigs : List DBCSignal)
  → findMuxMaster sigs ≡ mm → Dec (MasterCoherent sigs)
mcGo? nothing  sigs eq = yes (mc-no-mux eq)
mcGo? (just n) sigs eq
  with any? (masterOk? n) sigs ×-dec all? (whenOk? n) sigs
... | yes (anyOk , allOk) =
  let (ms , ms∈sigs , nameEq , presEq) = find anyOk
  in yes (mc-mux n eq ms ms∈sigs nameEq presEq allOk)
... | no ¬both = no λ where
  (mc-no-mux eqN) → just≢nothing (trans (sym eq) eqN)
  (mc-mux n′ eq′ ms ms∈sigs nameEq presEq slaves) →
    let n′≡n = just-injective (trans (sym eq′) eq)
    in ¬both ( lose ms∈sigs (trans nameEq n′≡n , presEq)
             , All.map (λ {s} f m vs weq → trans (f m vs weq) n′≡n) slaves )

masterCoherent? : (sigs : List DBCSignal) → Dec (MasterCoherent sigs)
masterCoherent? sigs = mcGo? (findMuxMaster sigs) sigs refl

mcIssue : List DBCSignal → List ValidationIssue
mcIssue sigs =
  requireDec (masterCoherent? sigs)
    (mkIssue IsWarning MuxMasterIncoherent
      ("message multiplexing is incoherent (no single Always master, or a "
       ++ₛ "selector names a different master)"))
