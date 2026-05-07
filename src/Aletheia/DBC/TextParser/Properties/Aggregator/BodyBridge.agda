{-# OPTIONS --safe --without-K #-}

-- B.3.d Layer 4c — Body bridge: `formatChars-body d` (the 7-section
-- concatenation in `formatChars` order, post-E.7) equals
-- `foldr (emitTopStmt-chars defs) [] (toTopStmtsTyped d)` where
-- `defs = collectDefs (DBC.attributes d)`.
--
-- Proof structure:
--   1. `foldr-emit-app` — `foldr (λ x acc → f x ++ acc) [] (xs ++ ys)
--      ≡ foldr ... [] xs ++ foldr ... [] ys`.  Standard distributivity.
--   2. `foldr-emit-map` — `foldr (λ t acc → emitTopStmt-chars defs t
--      ++ acc) [] (map TX xs) ≡ emitX-chars xs` for each typed-shadow
--      constructor `TX`.  7 instances, each closes by structural
--      induction + the `emitTopStmt-chars` constructor case.
--   3. Compose 1 + 2 over the 7-section concat to get
--      `formatChars-body d ≡ foldr ... [] (toTopStmtsTyped d)`.
module Aletheia.DBC.TextParser.Properties.Aggregator.BodyBridge where

open import Data.Char  using (Char)
open import Data.List  using (List; []; _∷_; foldr; map)
  renaming (_++_ to _++ₗ_)
open import Data.List.Properties using ()
  renaming (++-assoc to ++ₗ-assoc; ++-identityʳ to ++ₗ-identityʳ)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong)

open import Aletheia.DBC.Types using
  ( DBC; DBCMessage; ValueTable; EnvironmentVar; DBCComment; SignalGroup
  ; AttrDef; DBCAttribute
  )

open import Aletheia.DBC.TextParser.ValueTables using (RawValueDesc)
open import Aletheia.DBC.TextParser.ValueDescriptions using (collectFromMessages)

open import Aletheia.DBC.TextFormatter.ValueTables  using
  ( emitValueTable-chars; emitValueTables-chars
  ; emitValueDescription-chars; emitValueDescriptions-chars; emitValueDescriptions-rvds-chars
  )
open import Aletheia.DBC.TextFormatter.Topology    using (emitMessage-chars; emitMessages-chars)
open import Aletheia.DBC.TextFormatter.EnvVars      using (emitEnvVar-chars; emitEnvVars-chars)
open import Aletheia.DBC.TextFormatter.Comments     using (emitComment-chars; emitComments-chars)
open import Aletheia.DBC.TextFormatter.SignalGroups using (emitSignalGroup-chars; emitSignalGroups-chars)
open import Aletheia.DBC.TextFormatter.Attributes   using (emitAttribute-chars; emitAttributes-chars; collectDefs)

open import Aletheia.DBC.TextParser.Properties.Aggregator.Foundations using
  ( TopStmtTyped; TVT; TM; TVD; TEV; TCM; TAT; TSG
  ; emitTopStmt-chars
  ; toTopStmtsTyped
  )

-- ============================================================================
-- GENERIC FOLDR HELPERS
-- ============================================================================

-- `foldr (λ x acc → f x ++ acc) [] (xs ++ ys)` distributes over `++ₗ`.
-- Standard structural induction on `xs`.
private
  foldr-emit-app :
      ∀ {A : Set} (f : A → List Char) (xs ys : List A)
    → foldr (λ a acc → f a ++ₗ acc) [] (xs ++ₗ ys)
      ≡ foldr (λ a acc → f a ++ₗ acc) [] xs
        ++ₗ foldr (λ a acc → f a ++ₗ acc) [] ys
  foldr-emit-app f []       ys = refl
  foldr-emit-app f (x ∷ xs) ys =
    trans
      (cong (λ tail → f x ++ₗ tail) (foldr-emit-app f xs ys))
      (sym (++ₗ-assoc (f x) _ _))

-- `foldr (λ t acc → emitTopStmt-chars defs t ++ acc) [] (map g xs) ≡
--  foldr (λ a acc → g' a ++ acc) [] xs` whenever `emitTopStmt-chars defs
-- ∘ g ≡ g'`.  Reusable for each per-section constructor instance.
private
  foldr-emit-map-iso :
      ∀ {A : Set} (defs : List AttrDef)
        (g : A → TopStmtTyped) (g' : A → List Char) (xs : List A)
    → (∀ (a : A) → emitTopStmt-chars defs (g a) ≡ g' a)
    → foldr (λ t acc → emitTopStmt-chars defs t ++ₗ acc) [] (map g xs)
      ≡ foldr (λ a acc → g' a ++ₗ acc) [] xs
  foldr-emit-map-iso _    _ _  []       _   = refl
  foldr-emit-map-iso defs g g' (x ∷ xs) eq  =
    trans
      (cong (λ b → b ++ₗ foldr (λ t acc → emitTopStmt-chars defs t ++ₗ acc) [] (map g xs))
            (eq x))
      (cong (λ tail → g' x ++ₗ tail)
            (foldr-emit-map-iso defs g g' xs eq))

-- ============================================================================
-- PER-SECTION BRIDGES — `foldr E [] (map TX xs) ≡ emitX-chars xs`
-- ============================================================================
--
-- For each non-attribute section, the bridge is direct: `emitTopStmt-
-- chars defs (TX x)` reduces to `emitX-chars x` by definition.

emit-map-TVT-eq :
    ∀ defs (vts : List ValueTable)
  → foldr (λ t acc → emitTopStmt-chars defs t ++ₗ acc) [] (map TVT vts)
    ≡ emitValueTables-chars vts
emit-map-TVT-eq defs vts =
  foldr-emit-map-iso defs TVT emitValueTable-chars vts (λ _ → refl)

emit-map-TM-eq :
    ∀ defs (msgs : List DBCMessage)
  → foldr (λ t acc → emitTopStmt-chars defs t ++ₗ acc) [] (map TM msgs)
    ≡ emitMessages-chars msgs
emit-map-TM-eq defs msgs =
  foldr-emit-map-iso defs TM emitMessage-chars msgs (λ _ → refl)

-- E.7: TVD per-section bridge.  Bridges the rvd list (the post-
-- `collectFromMessages` form) directly; the wrapper
-- `emitValueDescriptions-chars msgs = emitValueDescriptions-rvds-chars
-- (collectFromMessages msgs)` collapses by `refl` at the call site.
emit-map-TVD-eq :
    ∀ defs (rvds : List RawValueDesc)
  → foldr (λ t acc → emitTopStmt-chars defs t ++ₗ acc) [] (map TVD rvds)
    ≡ emitValueDescriptions-rvds-chars rvds
emit-map-TVD-eq defs rvds =
  foldr-emit-map-iso defs TVD emitValueDescription-chars rvds (λ _ → refl)

emit-map-TEV-eq :
    ∀ defs (evs : List EnvironmentVar)
  → foldr (λ t acc → emitTopStmt-chars defs t ++ₗ acc) [] (map TEV evs)
    ≡ emitEnvVars-chars evs
emit-map-TEV-eq defs evs =
  foldr-emit-map-iso defs TEV emitEnvVar-chars evs (λ _ → refl)

emit-map-TCM-eq :
    ∀ defs (cms : List DBCComment)
  → foldr (λ t acc → emitTopStmt-chars defs t ++ₗ acc) [] (map TCM cms)
    ≡ emitComments-chars cms
emit-map-TCM-eq defs cms =
  foldr-emit-map-iso defs TCM emitComment-chars cms (λ _ → refl)

-- For attributes, `emitTopStmt-chars defs (TAT a) = emitAttribute-chars
-- defs a` and `emitAttributes-chars attrs = foldr (...emitAttribute-
-- chars defs...) [] attrs` where `defs = collectDefs attrs`.  When the
-- ambient `defs` matches `collectDefs attrs` (top-level invariant), the
-- bridge holds.
emit-map-TAT-eq :
    ∀ defs (attrs : List DBCAttribute)
  → defs ≡ collectDefs attrs
  → foldr (λ t acc → emitTopStmt-chars defs t ++ₗ acc) [] (map TAT attrs)
    ≡ emitAttributes-chars attrs
emit-map-TAT-eq defs attrs defs-eq =
  trans
    (foldr-emit-map-iso defs TAT (λ a → emitAttribute-chars defs a)
                        attrs (λ _ → refl))
    body
  where
    body :
      foldr (λ a acc → emitAttribute-chars defs a ++ₗ acc) [] attrs
      ≡ emitAttributes-chars attrs
    body =
      cong (λ ds → foldr (λ a acc → emitAttribute-chars ds a ++ₗ acc) [] attrs)
           defs-eq

emit-map-TSG-eq :
    ∀ defs (sgs : List SignalGroup)
  → foldr (λ t acc → emitTopStmt-chars defs t ++ₗ acc) [] (map TSG sgs)
    ≡ emitSignalGroups-chars sgs
emit-map-TSG-eq defs sgs =
  foldr-emit-map-iso defs TSG emitSignalGroup-chars sgs (λ _ → refl)

-- ============================================================================
-- BODY BRIDGE — full 7-section composition
-- ============================================================================
--
-- `formatChars-body d` (the part of `formatChars d` after BU_) equals
-- `foldr (emitTopStmt-chars (collectDefs (DBC.attributes d))) [] (to-
-- TopStmtsTyped d)`.  Composes the 7 per-section bridges via the
-- `foldr-emit-app` distributivity helper.

formatChars-body : DBC → List Char
formatChars-body d =
  emitValueTables-chars       (DBC.valueTables     d) ++ₗ
  emitMessages-chars          (DBC.messages        d) ++ₗ
  emitValueDescriptions-chars (DBC.messages        d) ++ₗ
  emitEnvVars-chars           (DBC.environmentVars d) ++ₗ
  emitComments-chars          (DBC.comments        d) ++ₗ
  emitAttributes-chars        (DBC.attributes      d) ++ₗ
  emitSignalGroups-chars      (DBC.signalGroups    d)

-- The whole-body bridge.  Decomposes via 6 applications of `foldr-
-- emit-app` (one per `++` boundary in `toTopStmtsTyped`), then 7
-- applications of the per-section `emit-map-T*-eq` bridges to convert
-- each `foldr (...) (map T* xs)` chunk to its `emitX-chars xs` form.
formatChars-body-bridge :
    ∀ (d : DBC)
  → foldr (λ t acc → emitTopStmt-chars (collectDefs (DBC.attributes d)) t ++ₗ acc) []
          (toTopStmtsTyped d)
    ≡ formatChars-body d
formatChars-body-bridge d = step7
  where
    vts   = DBC.valueTables     d
    msgs  = DBC.messages        d
    rvds  = collectFromMessages msgs
    evs   = DBC.environmentVars d
    cms   = DBC.comments        d
    attrs = DBC.attributes      d
    sgs   = DBC.signalGroups    d
    defs  = collectDefs attrs

    step1 :
        foldr (λ t acc → emitTopStmt-chars defs t ++ₗ acc) []
              (toTopStmtsTyped d)
      ≡ foldr (λ t acc → emitTopStmt-chars defs t ++ₗ acc) [] (map TVT vts)
        ++ₗ foldr (λ t acc → emitTopStmt-chars defs t ++ₗ acc) []
              (map TM msgs ++ₗ map TVD rvds ++ₗ map TEV evs ++ₗ map TCM cms ++ₗ map TAT attrs ++ₗ map TSG sgs)
    step1 =
      foldr-emit-app (λ t → emitTopStmt-chars defs t)
                     (map TVT vts)
                     (map TM msgs ++ₗ map TVD rvds ++ₗ map TEV evs ++ₗ map TCM cms ++ₗ map TAT attrs ++ₗ map TSG sgs)

    step2 :
        foldr (λ t acc → emitTopStmt-chars defs t ++ₗ acc) []
              (map TM msgs ++ₗ map TVD rvds ++ₗ map TEV evs ++ₗ map TCM cms ++ₗ map TAT attrs ++ₗ map TSG sgs)
      ≡ foldr (λ t acc → emitTopStmt-chars defs t ++ₗ acc) [] (map TM msgs)
        ++ₗ foldr (λ t acc → emitTopStmt-chars defs t ++ₗ acc) []
              (map TVD rvds ++ₗ map TEV evs ++ₗ map TCM cms ++ₗ map TAT attrs ++ₗ map TSG sgs)
    step2 =
      foldr-emit-app (λ t → emitTopStmt-chars defs t)
                     (map TM msgs)
                     (map TVD rvds ++ₗ map TEV evs ++ₗ map TCM cms ++ₗ map TAT attrs ++ₗ map TSG sgs)

    step3 :
        foldr (λ t acc → emitTopStmt-chars defs t ++ₗ acc) []
              (map TVD rvds ++ₗ map TEV evs ++ₗ map TCM cms ++ₗ map TAT attrs ++ₗ map TSG sgs)
      ≡ foldr (λ t acc → emitTopStmt-chars defs t ++ₗ acc) [] (map TVD rvds)
        ++ₗ foldr (λ t acc → emitTopStmt-chars defs t ++ₗ acc) []
              (map TEV evs ++ₗ map TCM cms ++ₗ map TAT attrs ++ₗ map TSG sgs)
    step3 =
      foldr-emit-app (λ t → emitTopStmt-chars defs t)
                     (map TVD rvds)
                     (map TEV evs ++ₗ map TCM cms ++ₗ map TAT attrs ++ₗ map TSG sgs)

    step4 :
        foldr (λ t acc → emitTopStmt-chars defs t ++ₗ acc) []
              (map TEV evs ++ₗ map TCM cms ++ₗ map TAT attrs ++ₗ map TSG sgs)
      ≡ foldr (λ t acc → emitTopStmt-chars defs t ++ₗ acc) [] (map TEV evs)
        ++ₗ foldr (λ t acc → emitTopStmt-chars defs t ++ₗ acc) []
              (map TCM cms ++ₗ map TAT attrs ++ₗ map TSG sgs)
    step4 =
      foldr-emit-app (λ t → emitTopStmt-chars defs t)
                     (map TEV evs)
                     (map TCM cms ++ₗ map TAT attrs ++ₗ map TSG sgs)

    step5 :
        foldr (λ t acc → emitTopStmt-chars defs t ++ₗ acc) []
              (map TCM cms ++ₗ map TAT attrs ++ₗ map TSG sgs)
      ≡ foldr (λ t acc → emitTopStmt-chars defs t ++ₗ acc) [] (map TCM cms)
        ++ₗ foldr (λ t acc → emitTopStmt-chars defs t ++ₗ acc) []
              (map TAT attrs ++ₗ map TSG sgs)
    step5 =
      foldr-emit-app (λ t → emitTopStmt-chars defs t)
                     (map TCM cms)
                     (map TAT attrs ++ₗ map TSG sgs)

    step6 :
        foldr (λ t acc → emitTopStmt-chars defs t ++ₗ acc) []
              (map TAT attrs ++ₗ map TSG sgs)
      ≡ foldr (λ t acc → emitTopStmt-chars defs t ++ₗ acc) [] (map TAT attrs)
        ++ₗ foldr (λ t acc → emitTopStmt-chars defs t ++ₗ acc) [] (map TSG sgs)
    step6 =
      foldr-emit-app (λ t → emitTopStmt-chars defs t)
                     (map TAT attrs)
                     (map TSG sgs)

    -- Abbreviations for the 7 chunks (typed-shadow folds).
    chunkVT  = foldr (λ t acc → emitTopStmt-chars defs t ++ₗ acc) [] (map TVT vts)
    chunkM   = foldr (λ t acc → emitTopStmt-chars defs t ++ₗ acc) [] (map TM msgs)
    chunkTVD = foldr (λ t acc → emitTopStmt-chars defs t ++ₗ acc) [] (map TVD rvds)
    chunkEV  = foldr (λ t acc → emitTopStmt-chars defs t ++ₗ acc) [] (map TEV evs)
    chunkCM  = foldr (λ t acc → emitTopStmt-chars defs t ++ₗ acc) [] (map TCM cms)
    chunkAT  = foldr (λ t acc → emitTopStmt-chars defs t ++ₗ acc) [] (map TAT attrs)
    chunkSG  = foldr (λ t acc → emitTopStmt-chars defs t ++ₗ acc) [] (map TSG sgs)

    -- After 6 applications of foldr-emit-app, the LHS reshapes into a
    -- right-associated 7-chunk concatenation.
    distrib :
        foldr (λ t acc → emitTopStmt-chars defs t ++ₗ acc) []
              (toTopStmtsTyped d)
      ≡ chunkVT ++ₗ chunkM ++ₗ chunkTVD ++ₗ chunkEV ++ₗ chunkCM ++ₗ chunkAT ++ₗ chunkSG
    distrib =
      trans step1
        (cong (λ r → chunkVT ++ₗ r)
          (trans step2
            (cong (λ r → chunkM ++ₗ r)
              (trans step3
                (cong (λ r → chunkTVD ++ₗ r)
                  (trans step4
                    (cong (λ r → chunkEV ++ₗ r)
                      (trans step5
                        (cong (λ r → chunkCM ++ₗ r) step6)))))))))

    -- Convert each chunk to its `emitX-chars` form via the per-section
    -- bridges (left-to-right).
    convert :
        chunkVT ++ₗ chunkM ++ₗ chunkTVD ++ₗ chunkEV ++ₗ chunkCM ++ₗ chunkAT ++ₗ chunkSG
      ≡ formatChars-body d
    convert =
      trans
        (cong (λ x → x ++ₗ chunkM ++ₗ chunkTVD ++ₗ chunkEV ++ₗ chunkCM ++ₗ chunkAT ++ₗ chunkSG)
              (emit-map-TVT-eq defs vts))
        (cong (λ x → emitValueTables-chars vts ++ₗ x)
          (trans
            (cong (λ x → x ++ₗ chunkTVD ++ₗ chunkEV ++ₗ chunkCM ++ₗ chunkAT ++ₗ chunkSG)
                  (emit-map-TM-eq defs msgs))
            (cong (λ x → emitMessages-chars msgs ++ₗ x)
              (trans
                (cong (λ x → x ++ₗ chunkEV ++ₗ chunkCM ++ₗ chunkAT ++ₗ chunkSG)
                      (emit-map-TVD-eq defs rvds))
                (cong (λ x → emitValueDescriptions-rvds-chars rvds ++ₗ x)
                  (trans
                    (cong (λ x → x ++ₗ chunkCM ++ₗ chunkAT ++ₗ chunkSG)
                          (emit-map-TEV-eq defs evs))
                    (cong (λ x → emitEnvVars-chars evs ++ₗ x)
                      (trans
                        (cong (λ x → x ++ₗ chunkAT ++ₗ chunkSG)
                              (emit-map-TCM-eq defs cms))
                        (cong (λ x → emitComments-chars cms ++ₗ x)
                          (trans
                            (cong (λ x → x ++ₗ chunkSG)
                                  (emit-map-TAT-eq defs attrs refl))
                            (cong (λ x → emitAttributes-chars attrs ++ₗ x)
                                  (emit-map-TSG-eq defs sgs))))))))))))

    step7 :
        foldr (λ t acc → emitTopStmt-chars defs t ++ₗ acc) []
              (toTopStmtsTyped d)
      ≡ formatChars-body d
    step7 = trans distrib convert
