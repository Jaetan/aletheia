{-# OPTIONS --safe --without-K #-}

-- B.3.d Layer 4c task C — `partitionTopStmts` categorical preservation.
--
-- Theorem:
--   partitionTopStmts (map (liftTopStmt defs) (toTopStmtsTyped d))
--     ≡ mkCollectedTop (DBC.messages        d)
--                       (DBC.valueTables     d)
--                       (DBC.environmentVars d)
--                       (DBC.comments        d)
--                       (map (rawOf defs) (DBC.attributes d))
--                       (DBC.signalGroups    d)
--
-- Proof strategy: 6 per-section accumulator-style lemmas + 5 `foldr-++`
-- compositions (one per `++` boundary in `toTopStmtsTyped`).  Each
-- per-section lemma updates exactly one field of the accumulator,
-- leaving the other 5 untouched.  Drop variants (`TSBOTxBu` / `TSValue-
-- Desc` / `TSSigValType` / `TSSigMulVal`) never occur in `liftTopStmt`'s
-- image so are not in scope.
module Aletheia.DBC.TextParser.Properties.Aggregator.Partition where

open import Data.Char  using (Char)
open import Data.List  using (List; []; _∷_; foldr; map)
  renaming (_++_ to _++ₗ_)
open import Data.List.Properties using (foldr-++; map-++)
  renaming (++-identityʳ to ++ₗ-identityʳ)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong)

open import Aletheia.DBC.Types using
  ( DBC; DBCMessage; ValueTable; EnvironmentVar; DBCComment; SignalGroup
  ; AttrDef; DBCAttribute
  )

open import Aletheia.DBC.TextParser.Attributes using
  (RawDBCAttribute)

open import Aletheia.DBC.TextParser.TopLevel using
  ( TopStmt; TSValueTable; TSMessage; TSEnvVar; TSComment
  ; TSAttribute; TSSignalGroup
  ; CollectedTop; mkCollectedTop; emptyCollected; consTop
  ; partitionTopStmts
  )

open import Aletheia.DBC.TextParser.Properties.Aggregator.Foundations using
  ( TopStmtTyped; TVT; TM; TEV; TCM; TAT; TSG
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

partition-onto-acc-TM :
    ∀ (defs : List AttrDef) (msgs : List DBCMessage) (acc : CollectedTop)
  → foldr consTop acc (map (liftTopStmt defs) (map TM msgs))
    ≡ record acc { messages = msgs ++ₗ CollectedTop.messages acc }
partition-onto-acc-TM defs []         acc = refl
partition-onto-acc-TM defs (m  ∷ ms)  acc =
  cong (consTop (TSMessage m)) (partition-onto-acc-TM defs ms acc)

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

partitionTopStmts-bridge :
    ∀ (defs : List AttrDef) (d : DBC)
  → partitionTopStmts (map (liftTopStmt defs) (toTopStmtsTyped d))
    ≡ mkCollectedTop
        (DBC.messages        d)
        (DBC.valueTables     d)
        (DBC.environmentVars d)
        (DBC.comments        d)
        (map (rawOf defs) (DBC.attributes d))
        (DBC.signalGroups    d)
partitionTopStmts-bridge defs d =
  trans (partitionTopStmts-foldr (map (liftTopStmt defs) (toTopStmtsTyped d))) compose
  where
    vts   = DBC.valueTables     d
    msgs  = DBC.messages        d
    evs   = DBC.environmentVars d
    cms   = DBC.comments        d
    attrs = DBC.attributes      d
    sgs   = DBC.signalGroups    d

    -- The 6 typed-shadow chunks (lifted to TopStmt via liftTopStmt defs).
    chunkVT = map (liftTopStmt defs) (map TVT vts)
    chunkM  = map (liftTopStmt defs) (map TM  msgs)
    chunkEV = map (liftTopStmt defs) (map TEV evs)
    chunkCM = map (liftTopStmt defs) (map TCM cms)
    chunkAT = map (liftTopStmt defs) (map TAT attrs)
    chunkSG = map (liftTopStmt defs) (map TSG sgs)

    -- After mapping liftTopStmt over toTopStmtsTyped d, the 6-section
    -- structure is preserved by `map-++` (5 applications).
    map-distrib :
        map (liftTopStmt defs) (toTopStmtsTyped d)
      ≡ chunkVT ++ₗ chunkM ++ₗ chunkEV ++ₗ chunkCM ++ₗ chunkAT ++ₗ chunkSG
    map-distrib =
      trans
        (map-++ (liftTopStmt defs) (map TVT vts) _)
        (cong (chunkVT ++ₗ_)
          (trans
            (map-++ (liftTopStmt defs) (map TM msgs) _)
            (cong (chunkM ++ₗ_)
              (trans
                (map-++ (liftTopStmt defs) (map TEV evs) _)
                (cong (chunkEV ++ₗ_)
                  (trans
                    (map-++ (liftTopStmt defs) (map TCM cms) _)
                    (cong (chunkCM ++ₗ_)
                      (map-++ (liftTopStmt defs) (map TAT attrs) _))))))))

    -- Process the 6 chunks right-to-left via 5 applications of foldr-++,
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

    acc-M : CollectedTop
    acc-M = record acc-EV
              { messages = msgs ++ₗ CollectedTop.messages acc-EV }

    foldr-M-eq :
        foldr consTop
              (foldr consTop
                     (foldr consTop
                            (foldr consTop (foldr consTop emptyCollected chunkSG) chunkAT)
                            chunkCM)
                     chunkEV)
              chunkM
      ≡ acc-M
    foldr-M-eq =
      trans (cong (λ z → foldr consTop z chunkM) foldr-EV-eq)
            (partition-onto-acc-TM defs msgs acc-EV)

    acc-VT : CollectedTop
    acc-VT = record acc-M
               { valueTables = vts ++ₗ CollectedTop.valueTables acc-M }

    foldr-VT-eq :
        foldr consTop
              (foldr consTop
                     (foldr consTop
                            (foldr consTop
                                   (foldr consTop (foldr consTop emptyCollected chunkSG) chunkAT)
                                   chunkCM)
                            chunkEV)
                     chunkM)
              chunkVT
      ≡ acc-VT
    foldr-VT-eq =
      trans (cong (λ z → foldr consTop z chunkVT) foldr-M-eq)
            (partition-onto-acc-TVT defs vts acc-M)

    -- 5 applications of foldr-++ to walk through the 6 chunks.
    foldr-app-bridge :
        foldr consTop emptyCollected
              (chunkVT ++ₗ chunkM ++ₗ chunkEV ++ₗ chunkCM ++ₗ chunkAT ++ₗ chunkSG)
      ≡ foldr consTop
              (foldr consTop
                     (foldr consTop
                            (foldr consTop
                                   (foldr consTop (foldr consTop emptyCollected chunkSG) chunkAT)
                                   chunkCM)
                            chunkEV)
                     chunkM)
              chunkVT
    foldr-app-bridge =
      trans (foldr-++ consTop emptyCollected chunkVT _)
        (cong (λ z → foldr consTop z chunkVT)
          (trans (foldr-++ consTop emptyCollected chunkM _)
            (cong (λ z → foldr consTop z chunkM)
              (trans (foldr-++ consTop emptyCollected chunkEV _)
                (cong (λ z → foldr consTop z chunkEV)
                  (trans (foldr-++ consTop emptyCollected chunkCM _)
                    (cong (λ z → foldr consTop z chunkCM)
                      (foldr-++ consTop emptyCollected chunkAT _))))))))

    -- 6-arity cong helper for cleaning up `xs ++ []` to `xs` in each
    -- field via `++ₗ-identityʳ`.  Each `acc-X` definition prepends a
    -- list onto the matching field of its base accumulator, but the
    -- base field is `[]` (definitionally, by chain reduction through
    -- the record updates), so each cumulative field has shape
    -- `xs ++ []`.  `++-identityʳ` cleans up.
    cong-mkCollectedTop :
        ∀ {a a' b b' c c' d d' e e' f f'} →
        a ≡ a' → b ≡ b' → c ≡ c' → d ≡ d' → e ≡ e' → f ≡ f'
      → mkCollectedTop a b c d e f ≡ mkCollectedTop a' b' c' d' e' f'
    cong-mkCollectedTop refl refl refl refl refl refl = refl

    final-eq :
        acc-VT
      ≡ mkCollectedTop msgs vts evs cms (map (rawOf defs) attrs) sgs
    final-eq = cong-mkCollectedTop
                 (++ₗ-identityʳ msgs)
                 (++ₗ-identityʳ vts)
                 (++ₗ-identityʳ evs)
                 (++ₗ-identityʳ cms)
                 (++ₗ-identityʳ (map (rawOf defs) attrs))
                 (++ₗ-identityʳ sgs)

    compose :
        foldr consTop emptyCollected
              (map (liftTopStmt defs) (toTopStmtsTyped d))
      ≡ mkCollectedTop msgs vts evs cms (map (rawOf defs) attrs) sgs
    compose =
      trans (cong (foldr consTop emptyCollected) map-distrib)
        (trans foldr-app-bridge
          (trans foldr-VT-eq final-eq))
