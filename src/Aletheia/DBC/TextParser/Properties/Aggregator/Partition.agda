-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- `partitionTopStmts` categorical preservation.
--
-- Theorem (7-chunk toTopStmtsTyped):
--   partitionTopStmts (map (liftTopStmt defs) (toTopStmtsTyped d))
--     ≡ mkCollectedTop (DBC.messages        d)
--                       (DBC.valueTables     d)
--                       (DBC.environmentVars d)
--                       (DBC.comments        d)
--                       (map (rawOf defs) (DBC.attributes d))
--                       (DBC.signalGroups    d)
--                       (collectFromMessages (DBC.messages d))
--
-- Proof strategy: 7 per-section accumulator-style lemmas + 6 `foldr-++`
-- compositions (one per `++` boundary in `toTopStmtsTyped`).  Each
-- per-section lemma updates exactly one field of the accumulator,
-- leaving the other 6 untouched.  Other drop variants (`TSBOTxBu` /
-- `TSSigValType` / `TSSigMulVal`) never occur in `liftTopStmt`'s image
-- so are not in scope.
module Aletheia.DBC.TextParser.Properties.Aggregator.Partition where

open import Data.Char  using ()
open import Data.List  using (List; []; _∷_; foldr; map)
  renaming (_++_ to _++ₗ_)
open import Data.List.Properties using (foldr-++; map-++)
  renaming (++-identityʳ to ++ₗ-identityʳ)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; cong)

open import Aletheia.DBC.Types using
  ( DBC; DBCMessage; ValueTable; EnvironmentVar; DBCComment; SignalGroup
  ; AttrDef; DBCAttribute; clearBothMsg
  )

open import Aletheia.DBC.TextParser.Attributes using
  ()
open import Aletheia.DBC.TextParser.ValueTables using
  (RawValueDesc)
open import Aletheia.DBC.TextParser.ValueDescriptions using
  (collectFromMessages)
open import Aletheia.DBC.TextParser.Senders using
  (RawMsgSenders; collectSenders)

open import Aletheia.DBC.TextParser.TopLevel using
  ( TopStmt; TSValueTable; TSMessage; TSEnvVar; TSComment
  ; TSAttribute; TSSignalGroup; TSValueDesc; TSBOTxBu
  ; CollectedTop; mkCollectedTop; emptyCollected; consTop
  ; partitionTopStmts
  )

open import Aletheia.DBC.TextParser.Properties.Aggregator.Foundations using
  ( TVT; TM; TEV; TCM; TAT; TSG; TVD; TBO
  ; liftTopStmt; rawOf
  ; toTopStmtsTyped
  )

-- ============================================================================
-- PER-SECTION ACCUMULATOR-STYLE BRIDGES
-- ============================================================================
--
-- For each section TX, processing `map (liftTopStmt defs) (map TX xs)`
-- through `foldr consTop acc` updates exactly one field of `acc` —
-- prepending the corresponding `xs` (or `map (rawOf defs) attrs` for
-- TAT) onto that field's existing value.  Other fields pass through.

partition-onto-acc-TVT :
    ∀ (defs : List AttrDef) (vts : List ValueTable) (acc : CollectedTop)
  → foldr consTop acc (map (liftTopStmt defs) (map TVT vts))
    ≡ record acc { valueTables = vts ++ₗ CollectedTop.valueTables acc }
partition-onto-acc-TVT defs []         acc = refl
partition-onto-acc-TVT defs (vt ∷ vts) acc =
  cong (consTop (TSValueTable vt)) (partition-onto-acc-TVT defs vts acc)

-- liftTopStmt (TM m) = TSMessage (clearBothMsg m), so the
-- partitioned messages field carries `map clearBothMsg msgs`.  The
-- Universal layer threads `attachValueDescs ∘ collectFromMessages ≡ id`
-- post-buildDBC to recover the original messages.
partition-onto-acc-TM :
    ∀ (defs : List AttrDef) (msgs : List DBCMessage) (acc : CollectedTop)
  → foldr consTop acc (map (liftTopStmt defs) (map TM msgs))
    ≡ record acc { messages = map clearBothMsg msgs ++ₗ CollectedTop.messages acc }
partition-onto-acc-TM defs []         acc = refl
partition-onto-acc-TM defs (m  ∷ ms)  acc =
  cong (consTop (TSMessage (clearBothMsg m))) (partition-onto-acc-TM defs ms acc)

partition-onto-acc-TEV :
    ∀ (defs : List AttrDef) (evs : List EnvironmentVar) (acc : CollectedTop)
  → foldr consTop acc (map (liftTopStmt defs) (map TEV evs))
    ≡ record acc { environmentVars = evs ++ₗ CollectedTop.environmentVars acc }
partition-onto-acc-TEV defs []         acc = refl
partition-onto-acc-TEV defs (ev ∷ evs) acc =
  cong (consTop (TSEnvVar ev)) (partition-onto-acc-TEV defs evs acc)

partition-onto-acc-TCM :
    ∀ (defs : List AttrDef) (cms : List DBCComment) (acc : CollectedTop)
  → foldr consTop acc (map (liftTopStmt defs) (map TCM cms))
    ≡ record acc { comments = cms ++ₗ CollectedTop.comments acc }
partition-onto-acc-TCM defs []         acc = refl
partition-onto-acc-TCM defs (cm ∷ cms) acc =
  cong (consTop (TSComment cm)) (partition-onto-acc-TCM defs cms acc)

partition-onto-acc-TAT :
    ∀ (defs : List AttrDef) (attrs : List DBCAttribute) (acc : CollectedTop)
  → foldr consTop acc (map (liftTopStmt defs) (map TAT attrs))
    ≡ record acc { rawAttributes =
                     map (rawOf defs) attrs ++ₗ CollectedTop.rawAttributes acc }
partition-onto-acc-TAT defs []        acc = refl
partition-onto-acc-TAT defs (a ∷ as)  acc =
  cong (consTop (TSAttribute (rawOf defs a)))
       (partition-onto-acc-TAT defs as acc)

partition-onto-acc-TSG :
    ∀ (defs : List AttrDef) (sgs : List SignalGroup) (acc : CollectedTop)
  → foldr consTop acc (map (liftTopStmt defs) (map TSG sgs))
    ≡ record acc { signalGroups = sgs ++ₗ CollectedTop.signalGroups acc }
partition-onto-acc-TSG defs []         acc = refl
partition-onto-acc-TSG defs (sg ∷ sgs) acc =
  cong (consTop (TSSignalGroup sg)) (partition-onto-acc-TSG defs sgs acc)

-- TVD per-section lemma.  Mirrors the 6 above; updates
-- the `rawValueDescs` field by prepending `rvds`.  It wires this into
-- `partitionTopStmts-bridge` via `collectFromMessages (DBC.messages d)`.
partition-onto-acc-TVD :
    ∀ (defs : List AttrDef) (rvds : List RawValueDesc) (acc : CollectedTop)
  → foldr consTop acc (map (liftTopStmt defs) (map TVD rvds))
    ≡ record acc { rawValueDescs = rvds ++ₗ CollectedTop.rawValueDescs acc }
partition-onto-acc-TVD defs []           acc = refl
partition-onto-acc-TVD defs (rvd ∷ rvds) acc =
  cong (consTop (TSValueDesc rvd)) (partition-onto-acc-TVD defs rvds acc)

-- TBO per-section lemma.  Mirrors the 7 above; updates the
-- `rawMsgSenders` field by prepending `rmss`.  Wired into
-- `partitionTopStmts-bridge` via `collectSenders (DBC.messages d)`.
partition-onto-acc-TBO :
    ∀ (defs : List AttrDef) (rmss : List RawMsgSenders) (acc : CollectedTop)
  → foldr consTop acc (map (liftTopStmt defs) (map TBO rmss))
    ≡ record acc { rawMsgSenders = rmss ++ₗ CollectedTop.rawMsgSenders acc }
partition-onto-acc-TBO defs []           acc = refl
partition-onto-acc-TBO defs (rms ∷ rmss) acc =
  cong (consTop (TSBOTxBu rms)) (partition-onto-acc-TBO defs rmss acc)

-- ============================================================================
-- BRIDGE — `partitionTopStmts ≡ foldr consTop emptyCollected`
-- ============================================================================
--
-- `partitionTopStmts` is definitionally `foldr consTop emptyCollected`
-- (see TopLevel.agda).  We work with the foldr form so `foldr-++` from
-- stdlib applies directly.

partitionTopStmts-foldr :
    ∀ (xs : List TopStmt)
  → partitionTopStmts xs ≡ foldr consTop emptyCollected xs
partitionTopStmts-foldr []       = refl
partitionTopStmts-foldr (x ∷ xs) =
  cong (consTop x) (partitionTopStmts-foldr xs)

-- ============================================================================
-- TOP-LEVEL THEOREM — categorical preservation
-- ============================================================================

-- `messages` field carries `map clearBothMsg d.messages`, NOT
-- `d.messages` — `liftTopStmt (TM m) = TSMessage (clearBothMsg m)` so
-- partition extracts the cleared form.  The Universal layer threads
-- `attachValueDescs (collectFromMessages d.messages) (map clearBothMsg
-- d.messages) ≡ d.messages` at buildDBC time to
-- recover the originals.  The TVD chunk still uses the original
-- `DBC.messages d` (before clearing) because the typed shadow's TVD
-- subterm was constructed at compile time from the original DBC.
partitionTopStmts-bridge :
    ∀ (defs : List AttrDef) (d : DBC)
  → partitionTopStmts (map (liftTopStmt defs) (toTopStmtsTyped d))
    ≡ mkCollectedTop
        (map clearBothMsg (DBC.messages d))
        (DBC.valueTables     d)
        (DBC.environmentVars d)
        (DBC.comments        d)
        (map (rawOf defs) (DBC.attributes d))
        (DBC.signalGroups    d)
        (collectFromMessages (DBC.messages d))
        (collectSenders      (DBC.messages d))
        []
partitionTopStmts-bridge defs d =
  trans (partitionTopStmts-foldr (map (liftTopStmt defs) (toTopStmtsTyped d))) compose
  where
    vts   = DBC.valueTables     d
    msgs  = DBC.messages        d
    evs   = DBC.environmentVars d
    cms   = DBC.comments        d
    attrs = DBC.attributes      d
    sgs   = DBC.signalGroups    d
    rvds  = collectFromMessages msgs
    rmss  = collectSenders      msgs

    -- The 8 typed-shadow chunks (lifted to TopStmt via liftTopStmt defs).
    chunkVT  = map (liftTopStmt defs) (map TVT vts)
    chunkM   = map (liftTopStmt defs) (map TM  msgs)
    chunkTBO = map (liftTopStmt defs) (map TBO rmss)
    chunkTVD = map (liftTopStmt defs) (map TVD rvds)
    chunkEV  = map (liftTopStmt defs) (map TEV evs)
    chunkCM  = map (liftTopStmt defs) (map TCM cms)
    chunkAT  = map (liftTopStmt defs) (map TAT attrs)
    chunkSG  = map (liftTopStmt defs) (map TSG sgs)

    -- After mapping liftTopStmt over toTopStmtsTyped d, the 8-section
    -- structure is preserved by `map-++` (7 applications).
    map-distrib :
        map (liftTopStmt defs) (toTopStmtsTyped d)
      ≡ chunkVT ++ₗ chunkM ++ₗ chunkTBO ++ₗ chunkTVD ++ₗ chunkEV ++ₗ chunkCM ++ₗ chunkAT ++ₗ chunkSG
    map-distrib =
      trans
        (map-++ (liftTopStmt defs) (map TVT vts) _)
        (cong (chunkVT ++ₗ_)
          (trans
            (map-++ (liftTopStmt defs) (map TM msgs) _)
            (cong (chunkM ++ₗ_)
              (trans
                (map-++ (liftTopStmt defs) (map TBO rmss) _)
                (cong (chunkTBO ++ₗ_)
                  (trans
                    (map-++ (liftTopStmt defs) (map TVD rvds) _)
                    (cong (chunkTVD ++ₗ_)
                      (trans
                        (map-++ (liftTopStmt defs) (map TEV evs) _)
                        (cong (chunkEV ++ₗ_)
                          (trans
                            (map-++ (liftTopStmt defs) (map TCM cms) _)
                            (cong (chunkCM ++ₗ_)
                              (map-++ (liftTopStmt defs) (map TAT attrs) _))))))))))))

    -- Process the 7 chunks right-to-left via 6 applications of foldr-++,
    -- each followed by the corresponding per-section accumulator lemma.

    -- Innermost: foldr over chunkSG starting from emptyCollected.
    acc-SG : CollectedTop
    acc-SG = record emptyCollected
               { signalGroups = sgs ++ₗ CollectedTop.signalGroups emptyCollected }

    foldr-SG-eq : foldr consTop emptyCollected chunkSG ≡ acc-SG
    foldr-SG-eq = partition-onto-acc-TSG defs sgs emptyCollected

    -- Next: foldr over chunkAT starting from acc-SG.
    acc-AT : CollectedTop
    acc-AT = record acc-SG
               { rawAttributes = map (rawOf defs) attrs ++ₗ CollectedTop.rawAttributes acc-SG }

    foldr-AT-eq :
        foldr consTop (foldr consTop emptyCollected chunkSG) chunkAT
      ≡ acc-AT
    foldr-AT-eq =
      trans (cong (λ z → foldr consTop z chunkAT) foldr-SG-eq)
            (partition-onto-acc-TAT defs attrs acc-SG)

    acc-CM : CollectedTop
    acc-CM = record acc-AT
               { comments = cms ++ₗ CollectedTop.comments acc-AT }

    foldr-CM-eq :
        foldr consTop
              (foldr consTop (foldr consTop emptyCollected chunkSG) chunkAT)
              chunkCM
      ≡ acc-CM
    foldr-CM-eq =
      trans (cong (λ z → foldr consTop z chunkCM) foldr-AT-eq)
            (partition-onto-acc-TCM defs cms acc-AT)

    acc-EV : CollectedTop
    acc-EV = record acc-CM
               { environmentVars = evs ++ₗ CollectedTop.environmentVars acc-CM }

    foldr-EV-eq :
        foldr consTop
              (foldr consTop
                     (foldr consTop (foldr consTop emptyCollected chunkSG) chunkAT)
                     chunkCM)
              chunkEV
      ≡ acc-EV
    foldr-EV-eq =
      trans (cong (λ z → foldr consTop z chunkEV) foldr-CM-eq)
            (partition-onto-acc-TEV defs evs acc-CM)

    -- TVD step between acc-EV and acc-M (TVD sits between TM and
    -- TEV in toTopStmtsTyped, so inside-out it sits between EV and M).
    acc-TVD : CollectedTop
    acc-TVD = record acc-EV
                { rawValueDescs = rvds ++ₗ CollectedTop.rawValueDescs acc-EV }

    foldr-TVD-eq :
        foldr consTop
              (foldr consTop
                     (foldr consTop
                            (foldr consTop (foldr consTop emptyCollected chunkSG) chunkAT)
                            chunkCM)
                     chunkEV)
              chunkTVD
      ≡ acc-TVD
    foldr-TVD-eq =
      trans (cong (λ z → foldr consTop z chunkTVD) foldr-EV-eq)
            (partition-onto-acc-TVD defs rvds acc-EV)

    -- TBO step between acc-TVD and acc-M (TBO sits between TM and TVD
    -- in toTopStmtsTyped, so inside-out it sits between TVD and M).
    acc-BO : CollectedTop
    acc-BO = record acc-TVD
               { rawMsgSenders = rmss ++ₗ CollectedTop.rawMsgSenders acc-TVD }

    foldr-BO-eq :
        foldr consTop
              (foldr consTop
                     (foldr consTop
                            (foldr consTop
                                   (foldr consTop (foldr consTop emptyCollected chunkSG) chunkAT)
                                   chunkCM)
                            chunkEV)
                     chunkTVD)
              chunkTBO
      ≡ acc-BO
    foldr-BO-eq =
      trans (cong (λ z → foldr consTop z chunkTBO) foldr-TVD-eq)
            (partition-onto-acc-TBO defs rmss acc-TVD)

    acc-M : CollectedTop
    acc-M = record acc-BO
              { messages = map clearBothMsg msgs ++ₗ CollectedTop.messages acc-BO }

    foldr-M-eq :
        foldr consTop
              (foldr consTop
                     (foldr consTop
                            (foldr consTop
                                   (foldr consTop
                                          (foldr consTop (foldr consTop emptyCollected chunkSG) chunkAT)
                                          chunkCM)
                                   chunkEV)
                            chunkTVD)
                     chunkTBO)
              chunkM
      ≡ acc-M
    foldr-M-eq =
      trans (cong (λ z → foldr consTop z chunkM) foldr-BO-eq)
            (partition-onto-acc-TM defs msgs acc-BO)

    acc-VT : CollectedTop
    acc-VT = record acc-M
               { valueTables = vts ++ₗ CollectedTop.valueTables acc-M }

    foldr-VT-eq :
        foldr consTop
              (foldr consTop
                     (foldr consTop
                            (foldr consTop
                                   (foldr consTop
                                          (foldr consTop
                                                 (foldr consTop (foldr consTop emptyCollected chunkSG) chunkAT)
                                                 chunkCM)
                                          chunkEV)
                                   chunkTVD)
                            chunkTBO)
                     chunkM)
              chunkVT
      ≡ acc-VT
    foldr-VT-eq =
      trans (cong (λ z → foldr consTop z chunkVT) foldr-M-eq)
            (partition-onto-acc-TVT defs vts acc-M)

    -- 7 applications of foldr-++ to walk through the 8 chunks.
    foldr-app-bridge :
        foldr consTop emptyCollected
              (chunkVT ++ₗ chunkM ++ₗ chunkTBO ++ₗ chunkTVD ++ₗ chunkEV ++ₗ chunkCM ++ₗ chunkAT ++ₗ chunkSG)
      ≡ foldr consTop
              (foldr consTop
                     (foldr consTop
                            (foldr consTop
                                   (foldr consTop
                                          (foldr consTop
                                                 (foldr consTop (foldr consTop emptyCollected chunkSG) chunkAT)
                                                 chunkCM)
                                          chunkEV)
                                   chunkTVD)
                            chunkTBO)
                     chunkM)
              chunkVT
    foldr-app-bridge =
      trans (foldr-++ consTop emptyCollected chunkVT _)
        (cong (λ z → foldr consTop z chunkVT)
          (trans (foldr-++ consTop emptyCollected chunkM _)
            (cong (λ z → foldr consTop z chunkM)
              (trans (foldr-++ consTop emptyCollected chunkTBO _)
                (cong (λ z → foldr consTop z chunkTBO)
                  (trans (foldr-++ consTop emptyCollected chunkTVD _)
                    (cong (λ z → foldr consTop z chunkTVD)
                      (trans (foldr-++ consTop emptyCollected chunkEV _)
                        (cong (λ z → foldr consTop z chunkEV)
                          (trans (foldr-++ consTop emptyCollected chunkCM _)
                            (cong (λ z → foldr consTop z chunkCM)
                              (foldr-++ consTop emptyCollected chunkAT _))))))))))))

    -- Per-field cong helper for cleaning up `xs ++ []` to `xs` in each
    -- bucket via `++ₗ-identityʳ`.  The `signalErrors` slot needs no
    -- cleanup — no typed-shadow chunk ever conses onto it, so it stays
    -- `[]` on both sides.
    cong-mkCollectedTop :
        ∀ {a a' b b' c c' dd dd' e e' f f' g g' h h'} →
        a ≡ a' → b ≡ b' → c ≡ c' → dd ≡ dd' → e ≡ e' → f ≡ f' → g ≡ g' → h ≡ h'
      → mkCollectedTop a b c dd e f g h [] ≡ mkCollectedTop a' b' c' dd' e' f' g' h' []
    cong-mkCollectedTop refl refl refl refl refl refl refl refl = refl

    final-eq :
        acc-VT
      ≡ mkCollectedTop (map clearBothMsg msgs) vts evs cms (map (rawOf defs) attrs) sgs rvds rmss []
    final-eq = cong-mkCollectedTop
                 (++ₗ-identityʳ (map clearBothMsg msgs))
                 (++ₗ-identityʳ vts)
                 (++ₗ-identityʳ evs)
                 (++ₗ-identityʳ cms)
                 (++ₗ-identityʳ (map (rawOf defs) attrs))
                 (++ₗ-identityʳ sgs)
                 (++ₗ-identityʳ rvds)
                 (++ₗ-identityʳ rmss)

    compose :
        foldr consTop emptyCollected
              (map (liftTopStmt defs) (toTopStmtsTyped d))
      ≡ mkCollectedTop (map clearBothMsg msgs) vts evs cms (map (rawOf defs) attrs) sgs rvds rmss []
    compose =
      trans (cong (foldr consTop emptyCollected) map-distrib)
        (trans foldr-app-bridge
          (trans foldr-VT-eq final-eq))
