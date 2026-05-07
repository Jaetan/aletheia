{-# OPTIONS --safe --without-K #-}

-- Track E.6 — VAL_ refinement: distribute parsed `RawValueDesc` payloads
-- back into the per-signal `DBCSignal.valueDescriptions` field.
--
-- Mirrors the `refineAttributes` pattern (in `TextParser.Attributes`) that
-- closes the BA_/BA_DEF_DEF_/BA_REL_ refinement: a flat `List RawX`
-- collected by `partitionTopStmts` is folded back into the structured
-- `DBC` record via a function that runs at DBC config time.
--
-- Three runtime entry points:
--
--   * `lookup-vd : CANId → Identifier → List RawValueDesc → Maybe RawValueDesc`
--     Linear scan; returns the first rvd whose `(canId, signalName)` pair
--     matches.  Under WF (msg-id unique, within-msg signal-name unique)
--     `collectFromMessages` produces at most one rvd per signal, so the
--     "first match" is the only match.
--
--   * `attachValueDescs : List RawValueDesc → List DBCMessage → List DBCMessage`
--     Walks the messages once, mapping `attachToSignal` over each
--     message's signals.  Total — silent drop on unmatched rvds (the
--     validator's CHECK 23 `UnknownValueDescriptionTarget` catches
--     unresolved rvds at validation time, not refinement time, mirroring
--     `RawDBCComment` and the rest of the refine-permissive / validate-
--     strict split).
--
--   * `collectFromMessages : List DBCMessage → List RawValueDesc`
--     Inverse of `attachValueDescs`.  Walks each message's signals, and
--     emits one `mkRawValueDesc msg.id sig.name sig.valueDescriptions`
--     per signal whose `valueDescriptions` is non-empty.  Empty-vds
--     signals contribute nothing — this matches the formatter's behavior
--     at E.7 (only emit `VAL_` lines for signals with value descriptions).
--
-- The proof side (`Properties.Aggregator.Refine.ValueDescriptions`) shows
-- `attachValueDescs (collectFromMessages msgs) msgs ≡ msgs` under WF.
-- The vacuous case `attachValueDescs [] msgs ≡ msgs` is the form used by
-- the universal aggregator at E.6 closure (`partitionTopStmts-bridge`
-- still produces `rawValueDescs = []` until E.7 flips `toTopStmtsTyped`
-- to 7 chunks via `collectFromMessages`).
--
-- API design discipline:
--   * `lookup-vd` and `attachWithMaybe` use Maybe-elim direct pattern
--     matching (per `feedback_expose_scrutinee_for_external_rewrite` +
--     `feedback_with_abstraction_traps`); the "set vds when matching"
--     branch destructures `mkRawValueDesc` at outer level
--     (per `feedback_k_elim_constructor_records`).
--   * Functions are total — no `Maybe` wrap.  CHECK 23 catches the
--     "missing target" case at validation, not here.
module Aletheia.DBC.TextParser.ValueDescriptions where

open import Data.List using (List; []; _∷_; map)
open import Data.Bool.ListAction using (any)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (Bool; true; false; if_then_else_; _∧_; _∨_)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_)
open import Data.Char using (Char)
open import Relation.Nullary using (⌊_⌋)

open import Aletheia.CAN.Frame using (CANId)
open import Aletheia.CAN.DBCHelpers using (_≟-CANId_)
open import Aletheia.DBC.Identifier using (Identifier; _≟ᴵ_)
open import Aletheia.DBC.Types using (DBCSignal; DBCMessage; RawValueDesc; mkRawValueDesc)

-- ============================================================================
-- LOOKUP — `(canId, signalName)` pair lookup in a `List RawValueDesc`
-- ============================================================================
--
-- Constructor pattern on `mkRawValueDesc` keeps the function reducing
-- past with-abstraction in proof bodies.  The Bool predicate routes
-- through stdlib `_∧_`, which reduces by primitive case analysis once
-- the two `⌊ ⌋` decidables resolve.

private
  matchesVD : CANId → Identifier → RawValueDesc → Bool
  matchesVD cid name (mkRawValueDesc rcid rname _) =
    ⌊ cid ≟-CANId rcid ⌋ ∧ ⌊ name ≟ᴵ rname ⌋

lookup-vd : CANId → Identifier → List RawValueDesc → Maybe RawValueDesc
lookup-vd _   _    []         = nothing
lookup-vd cid name (rvd ∷ rs) =
  if matchesVD cid name rvd
    then just rvd
    else lookup-vd cid name rs

-- ============================================================================
-- ATTACH — distribute a `List RawValueDesc` into nested `DBCMessage` signals
-- ============================================================================
--
-- `attachWithMaybe` is the Maybe-elim helper used inside `attachToSignal`.
-- Top-level (not where-bound) so proof-side `cong (attachWithMaybe s) eq`
-- finds the same identity (per `feedback_expose_scrutinee_for_external_
-- rewrite`).

attachWithMaybe : DBCSignal → Maybe RawValueDesc → DBCSignal
attachWithMaybe s nothing                          = s
attachWithMaybe s (just (mkRawValueDesc _ _ entries)) =
  record s { valueDescriptions = entries }

attachToSignal : List RawValueDesc → CANId → DBCSignal → DBCSignal
attachToSignal rvds canId s =
  attachWithMaybe s (lookup-vd canId (DBCSignal.name s) rvds)

attachToMessage : List RawValueDesc → DBCMessage → DBCMessage
attachToMessage rvds m =
  record m { signals = map (attachToSignal rvds (DBCMessage.id m))
                          (DBCMessage.signals m) }

attachValueDescs : List RawValueDesc → List DBCMessage → List DBCMessage
attachValueDescs rvds = map (attachToMessage rvds)

-- ============================================================================
-- COLLECT — flatten signals with non-empty `valueDescriptions` to `RawValueDesc`s
-- ============================================================================
--
-- `collectFromSignals` skips signals whose `valueDescriptions` is `[]`,
-- matching E.7's formatter (which only emits `VAL_` for non-empty
-- value-description lists).
--
-- The `prependVdsRvd` helper case-splits on the vds list explicitly (not
-- inline `with` inside `collectFromSignals`) so external proofs can
-- rewrite via `cong (prependVdsRvd cid name) (vds-eq : s.vds ≡ ...)`
-- without triggering the `with`-abstraction trap (per
-- `feedback_expose_scrutinee_for_external_rewrite.md` +
-- `feedback_with_abstraction_traps.md`).

prependVdsRvd : CANId → Identifier → List (ℕ × List Char)
              → List RawValueDesc → List RawValueDesc
prependVdsRvd _   _    []        rest = rest
prependVdsRvd cid name (x ∷ vds) rest = mkRawValueDesc cid name (x ∷ vds) ∷ rest

collectFromSignals : CANId → List DBCSignal → List RawValueDesc
collectFromSignals _   []       = []
collectFromSignals cid (s ∷ ss) =
  prependVdsRvd cid (DBCSignal.name s) (DBCSignal.valueDescriptions s)
                (collectFromSignals cid ss)

collectFromMessage : DBCMessage → List RawValueDesc
collectFromMessage m =
  collectFromSignals (DBCMessage.id m) (DBCMessage.signals m)

collectFromMessages : List DBCMessage → List RawValueDesc
collectFromMessages []       = []
collectFromMessages (m ∷ ms) = collectFromMessage m ++ₗ collectFromMessages ms
  where open import Data.List using () renaming (_++_ to _++ₗ_)


-- ============================================================================
-- RESOLVES — decidable Bool check against a `List DBCMessage`
-- ============================================================================
--
-- True iff some message `msg ∈ msgs` has `DBCMessage.id msg ≡ rvd.canId`,
-- and some signal `sig ∈ DBCMessage.signals msg` has `DBCSignal.name sig ≡
-- rvd.signalName`.  `unresolvedRVDs` (below) and `Formatter.WellFormedText.
-- ValueDescResolves.resolvesᵇ` (the validator-side wrapper over `DBC`)
-- both consume this primitive.
--
-- `matchesMsgᵇ` and `matchesSigᵇ` are top-level (not where-bound) so the
-- proof side in `Properties.Aggregator.Refine.ValueDescriptions` can name
-- them and reason about reduction directly per
-- `feedback_with_abstraction_traps.md` and
-- `feedback_expose_scrutinee_for_external_rewrite.md`.  `resolvesᵇ-msgs`
-- is a direct list recursion (not `any`-based) so the cons clause
-- reduces to `matchesMsgᵇ rvd m ∨ resolvesᵇ-msgs rvd ms` definitionally.

matchesSigᵇ : RawValueDesc → DBCSignal → Bool
matchesSigᵇ rvd s = ⌊ RawValueDesc.signalName rvd ≟ᴵ DBCSignal.name s ⌋

matchesMsgᵇ : RawValueDesc → DBCMessage → Bool
matchesMsgᵇ rvd msg =
  ⌊ RawValueDesc.canId rvd ≟-CANId DBCMessage.id msg ⌋
    ∧ any (matchesSigᵇ rvd) (DBCMessage.signals msg)

resolvesᵇ-msgs : RawValueDesc → List DBCMessage → Bool
resolvesᵇ-msgs _   []         = false
resolvesᵇ-msgs rvd (m ∷ ms)   = matchesMsgᵇ rvd m ∨ resolvesᵇ-msgs rvd ms


-- ============================================================================
-- PARTITION — RVDs that did NOT resolve against a `List DBCMessage`
-- ============================================================================
--
-- Walk the input RVD list once.  A resolved RVD is dropped (the matching
-- entry has already been distributed onto its signal by `attachValueDescs`);
-- an unresolved RVD is preserved.  The two functions together partition
-- the input: `attachValueDescs` consumes the resolved subset, `unresolvedRVDs`
-- consumes the rest.  At `buildDBC` time, the result lands on `DBC.unresolved
-- ValueDescs`; the validator's CHECK 23 walks that field.
--
-- `unresolvedRVDs (collectFromMessages msgs) msgs ≡ []` under WF (see
-- `Properties.Aggregator.Refine.ValueDescriptions.unresolvedRVDs-on-collected`):
-- entries collected from `msgs` necessarily resolve back to `msgs`.

unresolvedRVDs : List RawValueDesc → List DBCMessage → List RawValueDesc
unresolvedRVDs []         _    = []
unresolvedRVDs (rvd ∷ rs) msgs =
  if resolvesᵇ-msgs rvd msgs
    then unresolvedRVDs rs msgs
    else rvd ∷ unresolvedRVDs rs msgs
