{-# OPTIONS --safe --without-K #-}

-- B.3.d Layer 4c task E — Universal aggregator + finalizeParse closure.
--
-- The universal target:
--
--     ∀ d → WellFormedDBC d → parseText (formatText d) ≡ inj₂ d
--
-- Composes:
--   1. `parseText`-via-`parseTextChars` bridge, using
--      `Substrate.Unsafe.toList∘fromList` (the only `--unsafe` site in
--      the project, allowlisted by name in `Shakefile.hs`).
--   2. `parseDBCText` 5-step bind-chain composition through the slim
--      preamble lemmas (Version / Namespace / BitTiming / BU) + the
--      list-level `parseTopStmts-roundtrip` (Layer 4b's `many-η-with-
--      lift` instantiation, this commit's task B).
--   3. `finalizeParse` closure: `partitionTopStmts` (task C) +
--      `refineAttributes` inverse (task D) + buildDBC reconstruction.
module Aletheia.DBC.TextParser.Properties.Aggregator.Universal where

open import Data.Char  using (Char)
open import Data.List  using (List; []; _∷_; foldr; map)
  renaming (_++_ to _++ₗ_)
open import Data.List.Properties using ()
  renaming (++-assoc to ++ₗ-assoc; ++-identityʳ to ++ₗ-identityʳ)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.List.Relation.Unary.AllPairs using (AllPairs)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.String using (String)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)

open import Aletheia.Parser.Combinators using
  ( Parser; Position; ParseResult; mkResult
  ; advancePositions; many; pure; _>>=_
  ; runParserPartial; initialPosition; value; position; remaining)

open import Aletheia.DBC.Types using
  ( DBC; DBCMessage; DBCSignal; ValueTable; EnvironmentVar; DBCComment; SignalGroup
  ; Node
  ; AttrDef; DBCAttribute
  )

open import Aletheia.DBC.TextParser using
  ( parseText; parseTextChars; finalizeParse; buildDBC
  ; DBCTextParseError)

open import Aletheia.DBC.TextFormatter using (formatText)
open import Aletheia.DBC.TextFormatter.TopLevel using (formatChars)

open import Aletheia.DBC.TextParser.TopLevel using
  ( TopStmt; CollectedTop; mkCollectedTop; partitionTopStmts
  ; parseDBCText; parseTopStmt
  )
open import Aletheia.DBC.TextParser.Preamble using
  (parseVersion; parseNamespace; parseBitTiming)
open import Aletheia.DBC.TextParser.Topology using
  (parseBU)
open import Aletheia.DBC.TextParser.Attributes using
  (refineAttributes)

-- Per-section preconditions.
open import Aletheia.DBC.TextParser.Properties.ValueTables using
  (ValueTableNameStop)
open import Aletheia.DBC.TextParser.Properties.Topology using
  (MessageWF; NodeNameStop)
open import Aletheia.DBC.TextParser.Properties.EnvVars using
  (EnvVarNameStop)
open import Aletheia.DBC.TextParser.Properties.Comments using
  (CommentTargetStop)
open import Aletheia.DBC.TextParser.Properties.SignalGroups using
  (SignalGroupWF)

-- Per-section slim roundtrips (Layer 3 / 4a / 4b).
open import Aletheia.DBC.TextParser.Properties.Preamble.Version using
  (parseVersion-roundtrip)
open import Aletheia.DBC.TextParser.Properties.Preamble.Namespace using
  (parseNamespace-roundtrip; isNSLineStart)
open import Aletheia.DBC.TextParser.Properties.Preamble.BitTiming using
  (parseBitTiming-roundtrip)
open import Aletheia.DBC.TextParser.Properties.Topology.Nodes using
  (parseBU-roundtrip)

-- Newline / SuffixStops infrastructure.
open import Aletheia.DBC.TextParser.DecRatParse.Properties using
  (SuffixStops; ∷-stop; bind-just-step)
open import Aletheia.DBC.TextParser.Properties.Preamble.Newline using
  (isNewlineStart)

-- Layer 4c building blocks (this commit's tasks B/C/D).
open import Aletheia.DBC.TextParser.Properties.Aggregator.Foundations using
  ( TopStmtTyped; toTopStmtsTyped
  ; emitTopStmt-chars; liftTopStmt
  ; WFAttribute; rawOf
  )
open import Aletheia.DBC.TextParser.Properties.Aggregator.Dispatcher using
  (TopStmtTypedWF; wfTVT; wfTM; wfTEV; wfTCM; wfTAT; wfTSG; wfTVD)
open import Aletheia.DBC.TextParser.Properties.Aggregator.ManyTopStmts using
  (parseTopStmts-roundtrip)
open import Aletheia.DBC.TextParser.Properties.Aggregator.Partition using
  (partitionTopStmts-bridge)
open import Aletheia.DBC.TextParser.Properties.Aggregator.Refine using
  (refineAttributes-on-rawOf)
open import Aletheia.DBC.TextParser.Properties.Aggregator.Refine.ValueDescriptions using
  (map-attachToMessage-on-clearVdsMsgs-collected;
   collectFromMessages-stops;
   unresolvedRVDs-on-clearVdsMsgs-collectFromMessages)
open import Aletheia.DBC.TextParser.ValueDescriptions using
  (collectFromMessages)
open import Aletheia.DBC.TextParser.Properties.Aggregator.BodyBridge using
  (formatChars-body; formatChars-body-bridge)
open import Aletheia.DBC.TextFormatter.Attributes using
  (collectDefs)

-- Section emitters needed for input-shape bridging.
open import Aletheia.DBC.TextFormatter.Preamble using
  (emitVersion-chars; emitNamespace-chars; emitBitTiming-chars)
open import Aletheia.DBC.TextFormatter.Topology using
  (emitBU-chars)

-- ============================================================================
-- WELL-FORMEDNESS RECORD
-- ============================================================================
--
-- Bundles every per-section precondition the universal roundtrip needs.
-- Each field is the same predicate the Layer 3 / 4 slim takes for its
-- corresponding section.

record WellFormedDBC (d : DBC) : Set where
  field
    node-stops : All NodeNameStop                                   (DBC.nodes           d)
    vt-stops   : All ValueTableNameStop                             (DBC.valueTables     d)
    msg-wfs    : All MessageWF                                      (DBC.messages        d)
    ev-stops   : All EnvVarNameStop                                 (DBC.environmentVars d)
    cm-stops   : All CommentTargetStop                              (DBC.comments        d)
    attr-wfs   : All (WFAttribute (collectDefs (DBC.attributes d))) (DBC.attributes      d)
    sg-wfs     : All SignalGroupWF                                  (DBC.signalGroups    d)
    -- E.6: cross-message CAN-ID uniqueness.  Required by
    -- `attachValueDescs ∘ collectFromMessages ≡ id` (the inverse-bridge
    -- in `Properties.Aggregator.Refine.ValueDescriptions`): two distinct
    -- messages with the same CAN ID would have their per-signal VAL_
    -- entries collapse onto whichever message `lookup-vd` finds first,
    -- breaking the round-trip.  Validator's CHECK 18 (`DuplicateMessageId`)
    -- enforces this at DBC-load time.
    msg-ids-unique : AllPairs _≢_ (map DBCMessage.id (DBC.messages d))
    -- E.8 (Plan B, 2026-05-07): `formatText` does not emit lines for
    -- `DBC.unresolvedValueDescs` entries (no canonical text representation
    -- — they could be re-emitted as VAL_ lines but those would be silently
    -- re-collected as unresolved on parse-back, leaving the round-trip
    -- closed but lossy).  The text round-trip therefore closes only for
    -- DBCs whose unresolved list is already `[]`; this includes every
    -- DBC built from `parseText` (because `unresolvedRVDs ∘ collectFrom
    -- Messages ≡ []` under any `msgs`) and every DBC built from JSON
    -- (the JSON path always defaults the field to `[]`).  CHECK 23
    -- `UnknownValueDescriptionTarget` warns at validation time when
    -- this field is non-empty (E.11).
    unresolved-empty : DBC.unresolvedValueDescs d ≡ []

-- ============================================================================
-- BRIDGE — derive `All TopStmtTypedWF` from `WellFormedDBC`
-- ============================================================================
--
-- `toTopStmtsTyped d` is a 7-section `++` chain (`map TX xs` per section).
-- `All P` distributes over `++` and `map`, so we can lift each section's
-- slim precondition through its `TX` constructor.  At E.7 the TVD chunk's
-- arm is discharged vacuously: `MessageWF.vds-empty` (an E.1 interim
-- clause) lets us prove `collectFromMessages msgs ≡ []`, so `map TVD
-- (collectFromMessages msgs) ≡ []` and the `All` becomes `[]`.  E.9
-- relaxes this and replaces the vacuous arm with a derivation of
-- `All RawValueDescStop` from signal-name validity.

private
  -- All P (map f xs) iff All (P ∘ f) xs.  Standard.
  all-map :
      ∀ {A B : Set} {P : B → Set} (f : A → B) (xs : List A)
    → All (λ a → P (f a)) xs
    → All P (map f xs)
  all-map _ []        []        = []
  all-map f (x ∷ xs) (px ∷ pxs) = px ∷ all-map f xs pxs

  all-++ :
      ∀ {A : Set} {P : A → Set} (xs ys : List A)
    → All P xs → All P ys → All P (xs ++ₗ ys)
  all-++ []       _ []        ays = ays
  all-++ (x ∷ xs) ys (px ∷ axs) ays = px ∷ all-++ xs ys axs ays

toTopStmtsTyped-WF :
    ∀ (d : DBC) → WellFormedDBC d
  → All (TopStmtTypedWF (collectDefs (DBC.attributes d))) (toTopStmtsTyped d)
toTopStmtsTyped-WF d wf =
  all-++ _ _ (all-map TVT (DBC.valueTables d)
               (lift-stops TVT (TopStmtTypedWF defs) (DBC.valueTables d)
                           (WellFormedDBC.vt-stops wf) wfTVT))
            (all-++ _ _ (all-map TM (DBC.messages d)
                          (lift-stops TM (TopStmtTypedWF defs) (DBC.messages d)
                                      (WellFormedDBC.msg-wfs wf) wfTM))
                       (all-++ _ _ tvd-WF
                                  (all-++ _ _ (all-map TEV (DBC.environmentVars d)
                                                (lift-stops TEV (TopStmtTypedWF defs) (DBC.environmentVars d)
                                                            (WellFormedDBC.ev-stops wf) wfTEV))
                                             (all-++ _ _ (all-map TCM (DBC.comments d)
                                                           (lift-stops TCM (TopStmtTypedWF defs) (DBC.comments d)
                                                                       (WellFormedDBC.cm-stops wf) wfTCM))
                                                        (all-++ _ _ (all-map TAT (DBC.attributes d)
                                                                      (lift-stops TAT (TopStmtTypedWF defs) (DBC.attributes d)
                                                                                  (WellFormedDBC.attr-wfs wf) wfTAT))
                                                                   (all-map TSG (DBC.signalGroups d)
                                                                     (lift-stops TSG (TopStmtTypedWF defs) (DBC.signalGroups d)
                                                                                 (WellFormedDBC.sg-wfs wf) wfTSG)))))))
  where
    open import Aletheia.DBC.TextParser.Properties.Aggregator.Foundations using
      (TVT; TM; TVD; TEV; TCM; TAT; TSG)

    defs = collectDefs (DBC.attributes d)

    -- Convert `All Stop xs` to `All (P ∘ TX) xs` via the wfTX
    -- constructor (which carries the per-element witness).
    lift-stops :
        ∀ {A : Set} {Stop : A → Set}
          (TX : A → TopStmtTyped)
          (Wf : TopStmtTyped → Set)
      → (xs : List A)
      → All Stop xs
      → (∀ x → Stop x → Wf (TX x))
      → All (λ x → Wf (TX x)) xs
    lift-stops _ _ []        []          _ = []
    lift-stops TX Wf (x ∷ xs) (sx ∷ srest) f =
      f x sx ∷ lift-stops TX Wf xs srest f

    -- E.9a: non-vacuous TVD arm.  `collectFromMessages-stops` derives
    -- `All RawValueDescStop (collectFromMessages msgs)` from the
    -- structural shape of `collectFromSignals` (every rvd's signalName
    -- comes from some `s.name : Identifier`, whose `valid` witness
    -- decomposes to a head non-isHSpace).  No `vds-empty` precondition
    -- needed.  `lift-stops` then routes through `wfTVD`.
    tvd-WF : All (TopStmtTypedWF defs) (map TVD (collectFromMessages (DBC.messages d)))
    tvd-WF =
      all-map TVD (collectFromMessages (DBC.messages d))
        (lift-stops TVD (TopStmtTypedWF defs)
                    (collectFromMessages (DBC.messages d))
                    (collectFromMessages-stops (DBC.messages d))
                    wfTVD)

-- ============================================================================
-- BRIDGE — `parseTopStmt pos [] ≡ nothing`  (terminator obligation for `many`)
-- ============================================================================

parseTopStmt-on-empty :
    ∀ (pos : Position) → parseTopStmt pos [] ≡ nothing
parseTopStmt-on-empty _ = refl

-- ============================================================================
-- LIST-LEVEL TOPSTMT ROUNDTRIP — instantiated at empty outer-suffix
-- ============================================================================
--
-- Specialised to the form needed by the universal aggregator: the
-- `formatChars-body` shape (no outer suffix) lifted through the typed
-- shadow and `liftTopStmt`.

parseTopStmts-on-formatChars-body :
    ∀ (d : DBC) (pos : Position) → WellFormedDBC d
  → many parseTopStmt pos (formatChars-body d)
    ≡ just (mkResult
              (map (liftTopStmt (collectDefs (DBC.attributes d))) (toTopStmtsTyped d))
              (advancePositions pos (formatChars-body d))
              [])
parseTopStmts-on-formatChars-body d pos wf =
  trans (cong (λ inp → many parseTopStmt pos inp) input-shape)
        (trans body-eq tail-shape)
  where
    defs = collectDefs (DBC.attributes d)

    input-shape :
        formatChars-body d
      ≡ foldr (λ t acc → emitTopStmt-chars defs t ++ₗ acc) [] (toTopStmtsTyped d)
        ++ₗ []
    input-shape =
      trans
        (sym (++ₗ-identityʳ (formatChars-body d)))
        (cong (_++ₗ [])
              (sym (formatChars-body-bridge d)))

    body-eq :
        many parseTopStmt pos
          (foldr (λ t acc → emitTopStmt-chars defs t ++ₗ acc) [] (toTopStmtsTyped d) ++ₗ [])
      ≡ just (mkResult
                (map (liftTopStmt defs) (toTopStmtsTyped d))
                (advancePositions pos
                  (foldr (λ t acc → emitTopStmt-chars defs t ++ₗ acc) [] (toTopStmtsTyped d)))
                [])
    body-eq =
      parseTopStmts-roundtrip defs pos (toTopStmtsTyped d) []
        (toTopStmtsTyped-WF d wf)
        []-stop
        parseTopStmt-on-empty
      where
        open import Aletheia.DBC.TextParser.DecRatParse.Properties using ([]-stop)

    tail-shape :
        just (mkResult
                (map (liftTopStmt defs) (toTopStmtsTyped d))
                (advancePositions pos
                  (foldr (λ t acc → emitTopStmt-chars defs t ++ₗ acc) [] (toTopStmtsTyped d)))
                [])
      ≡ just (mkResult
                (map (liftTopStmt defs) (toTopStmtsTyped d))
                (advancePositions pos (formatChars-body d))
                [])
    tail-shape =
      cong (λ p → just (mkResult (map (liftTopStmt defs) (toTopStmtsTyped d)) p []))
           (cong (advancePositions pos) (formatChars-body-bridge d))

-- ============================================================================
-- HELPER — `formatChars-body d` always satisfies `SuffixStops isNewlineStart`
-- ============================================================================
--
-- Used to discharge `parseBU-roundtrip`'s `nl-stop` when the suffix
-- after `emitBU-chars (DBC.nodes d)` is exactly `formatChars-body d`.
-- Inducts on `toTopStmtsTyped d` via the body bridge.

formatChars-body-stops-isNewlineStart :
    ∀ (d : DBC) → SuffixStops isNewlineStart (formatChars-body d)
formatChars-body-stops-isNewlineStart d =
  subst (SuffixStops isNewlineStart)
        (formatChars-body-bridge d)
        (foldr-stops (toTopStmtsTyped d))
  where
    open import Aletheia.DBC.TextParser.Properties.Aggregator.Dispatcher using
      (emitTopStmt-chars-head-not-newline)
    open import Aletheia.DBC.TextParser.DecRatParse.Properties using ([]-stop)

    defs = collectDefs (DBC.attributes d)

    foldr-stops :
        ∀ (ts : List TopStmtTyped)
      → SuffixStops isNewlineStart
          (foldr (λ t acc → emitTopStmt-chars defs t ++ₗ acc) [] ts)
    foldr-stops []        = []-stop
    foldr-stops (t ∷ rest) =
      emitTopStmt-chars-head-not-newline
        defs t (foldr (λ t' acc → emitTopStmt-chars defs t' ++ₗ acc) [] rest)

-- ============================================================================
-- PARSE-DBC-TEXT — full 5-step bind chain composition
-- ============================================================================

parseDBCText-on-formatChars :
    ∀ (d : DBC)
  → WellFormedDBC d
  → parseDBCText initialPosition (formatChars d)
    ≡ just (mkResult
             ( DBC.version d
             , DBC.nodes   d
             , map (liftTopStmt (collectDefs (DBC.attributes d)))
                   (toTopStmtsTyped d)
             )
             (advancePositions initialPosition (formatChars d))
             [])
parseDBCText-on-formatChars d wf =
  trans bindVersion
    (trans bindNamespace
      (trans bindBitTiming
        (trans bindBU
          (trans bindMany
            pure-eq))))
  where
    open import Aletheia.DBC.TextParser.DecRatParse.Properties using ([]-stop)

    defs = collectDefs (DBC.attributes d)

    ver   = DBC.version         d
    nodes = DBC.nodes           d
    body  = formatChars-body    d
    stmts = map (liftTopStmt defs) (toTopStmtsTyped d)

    -- Suffix slices.
    sufVer = emitNamespace-chars ++ₗ emitBitTiming-chars ++ₗ emitBU-chars nodes ++ₗ body
    sufNS  = emitBitTiming-chars ++ₗ emitBU-chars nodes ++ₗ body
    sufBS  = emitBU-chars nodes ++ₗ body
    sufBU  = body

    -- Position trace at each step.
    posV  = advancePositions initialPosition (emitVersion-chars ver)
    posN  = advancePositions posV emitNamespace-chars
    posBS = advancePositions posN emitBitTiming-chars
    posBU = advancePositions posBS (emitBU-chars nodes)
    posBody = advancePositions posBU body

    -- Suffix-stop witnesses.  Every emit-* prefix starts with a non-
    -- newline letter, so `∷-stop refl` discharges each.
    sufVer-stop : SuffixStops isNewlineStart sufVer
    sufVer-stop = ∷-stop refl

    sufNS-stop : SuffixStops isNSLineStart sufNS
    sufNS-stop = ∷-stop refl

    sufBS-stop : SuffixStops isNewlineStart sufBS
    sufBS-stop = ∷-stop refl

    sufBU-stop : SuffixStops isNewlineStart sufBU
    sufBU-stop = formatChars-body-stops-isNewlineStart d

    -- Step witnesses.
    pVer-eq :
        parseVersion initialPosition (formatChars d)
      ≡ just (mkResult ver posV sufVer)
    pVer-eq = parseVersion-roundtrip initialPosition ver sufVer sufVer-stop

    pNS-eq :
        parseNamespace posV sufVer
      ≡ just (mkResult tt posN sufNS)
    pNS-eq = parseNamespace-roundtrip posV sufNS sufNS-stop

    pBS-eq :
        parseBitTiming posN sufNS
      ≡ just (mkResult tt posBS sufBS)
    pBS-eq = parseBitTiming-roundtrip posN sufBS sufBS-stop

    pBU-eq :
        parseBU posBS sufBS
      ≡ just (mkResult nodes posBU sufBU)
    pBU-eq =
      parseBU-roundtrip posBS nodes sufBU
        (WellFormedDBC.node-stops wf)
        sufBU-stop

    pMany-eq :
        many parseTopStmt posBU body
      ≡ just (mkResult stmts posBody [])
    pMany-eq = parseTopStmts-on-formatChars-body d posBU wf

    -- Bind chain — each step uses `bind-just-step`.
    bindVersion :
        parseDBCText initialPosition (formatChars d)
      ≡ ( parseNamespace >>= λ _ →
          parseBitTiming >>= λ _ →
          parseBU        >>= λ ns  →
          many parseTopStmt >>= λ ss →
          pure (ver , ns , ss) )
        posV sufVer
    bindVersion =
      bind-just-step parseVersion
        (λ v → parseNamespace >>= λ _ →
                parseBitTiming >>= λ _ →
                parseBU        >>= λ ns  →
                many parseTopStmt >>= λ ss →
                pure (v , ns , ss))
        initialPosition (formatChars d) ver posV sufVer pVer-eq

    bindNamespace :
        ( parseNamespace >>= λ _ →
          parseBitTiming >>= λ _ →
          parseBU        >>= λ ns  →
          many parseTopStmt >>= λ ss →
          pure (ver , ns , ss) )
        posV sufVer
      ≡ ( parseBitTiming >>= λ _ →
          parseBU        >>= λ ns  →
          many parseTopStmt >>= λ ss →
          pure (ver , ns , ss) )
        posN sufNS
    bindNamespace =
      bind-just-step parseNamespace
        (λ _ → parseBitTiming >>= λ _ →
                parseBU        >>= λ ns  →
                many parseTopStmt >>= λ ss →
                pure (ver , ns , ss))
        posV sufVer tt posN sufNS pNS-eq

    bindBitTiming :
        ( parseBitTiming >>= λ _ →
          parseBU        >>= λ ns  →
          many parseTopStmt >>= λ ss →
          pure (ver , ns , ss) )
        posN sufNS
      ≡ ( parseBU        >>= λ ns  →
          many parseTopStmt >>= λ ss →
          pure (ver , ns , ss) )
        posBS sufBS
    bindBitTiming =
      bind-just-step parseBitTiming
        (λ _ → parseBU        >>= λ ns  →
                many parseTopStmt >>= λ ss →
                pure (ver , ns , ss))
        posN sufNS tt posBS sufBS pBS-eq

    bindBU :
        ( parseBU        >>= λ ns  →
          many parseTopStmt >>= λ ss →
          pure (ver , ns , ss) )
        posBS sufBS
      ≡ ( many parseTopStmt >>= λ ss →
          pure (ver , nodes , ss) )
        posBU sufBU
    bindBU =
      bind-just-step parseBU
        (λ ns  → many parseTopStmt >>= λ ss →
                  pure (ver , ns , ss))
        posBS sufBS nodes posBU sufBU pBU-eq

    bindMany :
        ( many parseTopStmt >>= λ ss →
          pure (ver , nodes , ss) )
        posBU sufBU
      ≡ pure (ver , nodes , stmts) posBody []
    bindMany =
      bind-just-step (many parseTopStmt)
        (λ ss → pure (ver , nodes , ss))
        posBU body stmts posBody [] pMany-eq

    -- Final position witness: `posBody = advancePositions initialPosition (formatChars d)`.
    -- `formatChars d = emitVersion-chars ver ++ emitNamespace-chars ++ emitBitTiming-chars ++ emitBU-chars nodes ++ body`.
    -- 4 applications of `advancePositions-++` chain through the layers.
    pos-bridge :
        posBody
      ≡ advancePositions initialPosition (formatChars d)
    pos-bridge = sym
      (trans
        (advancePositions-++ initialPosition (emitVersion-chars ver)
                              (emitNamespace-chars ++ₗ emitBitTiming-chars
                                ++ₗ emitBU-chars nodes ++ₗ body))
        (trans
          (advancePositions-++ posV emitNamespace-chars
                                (emitBitTiming-chars
                                  ++ₗ emitBU-chars nodes ++ₗ body))
          (trans
            (advancePositions-++ posN emitBitTiming-chars
                                  (emitBU-chars nodes ++ₗ body))
            (advancePositions-++ posBS (emitBU-chars nodes) body))))
      where
        open import Aletheia.DBC.TextParser.DecRatParse.Properties using
          (advancePositions-++)

    pure-eq :
        pure (ver , nodes , stmts) posBody []
      ≡ just (mkResult (ver , nodes , stmts)
                       (advancePositions initialPosition (formatChars d))
                       [])
    pure-eq = cong (λ p → just (mkResult (ver , nodes , stmts) p [])) pos-bridge

-- ============================================================================
-- FINALIZE-PARSE CLOSURE
-- ============================================================================
--
-- Once `parseDBCText pos (formatChars d) ≡ just (mkResult (ver, nodes,
-- stmts) pos-end [])`, `finalizeParse` walks 5 `with` steps (post E.7):
--   1. `remaining res = []` — definitional from `mkResult … []`.
--   2. `value res = (ver, nodes, stmts)` — definitional pattern unbox.
--   3. `partitionTopStmts stmts` — Layer 4c task C bridges to
--      `mkCollectedTop … (map (rawOf defs) attrs) … (collectFromMessages
--      d.messages)` (E.7 wired the 7th field into `toTopStmtsTyped`).
--   4. `refineAttributes (CollectedTop.rawAttributes collected)` —
--      Layer 4c task D bridges to `just attrs`.
--   5. `attachValueDescs (CollectedTop.rawValueDescs collected) … `
--      inside `buildDBC` — discharged via E.9a's
--      `map-attachToMessage-on-clearVdsMsgs-collected` consuming
--      `msg-ids-unique` + `msg-wfs` from the WF record (E.6 layer
--      composed with the E.9a `clearVds` bridge to handle the cleared
--      messages produced by `liftTopStmt (TM m) = TSMessage (clearVdsMsg m)`).
-- The final `inj₂ (buildDBC ver nodes collected attrs)` reconstructs
-- `d` by record-η.
--
-- Split into two stages to bound rewrite scope: stage 1 lifts the
-- parser result through `cong finalizeParse`; stage 2 closes
-- `finalizeParse` on a concrete `mkResult` — only this stage's
-- rewrites need to walk the inner `with` chain.

finalizeParse-on-mkResult-clean :
    ∀ (d : DBC) (pos-end : Position) → WellFormedDBC d
  → finalizeParse
      (just (mkResult
              ( DBC.version d
              , DBC.nodes   d
              , map (liftTopStmt (collectDefs (DBC.attributes d)))
                    (toTopStmtsTyped d) )
              pos-end []))
    ≡ inj₂ d
finalizeParse-on-mkResult-clean d pos-end wf
  rewrite partitionTopStmts-bridge (collectDefs (DBC.attributes d)) d
        | refineAttributes-on-rawOf (DBC.attributes d) (WellFormedDBC.attr-wfs wf)
  = cong₂
      (λ msgs unres → inj₂ (record d { messages             = msgs
                                     ; unresolvedValueDescs = unres }))
      (map-attachToMessage-on-clearVdsMsgs-collected (DBC.messages d)
         (WellFormedDBC.msg-ids-unique wf)
         (WellFormedDBC.msg-wfs wf))
      (trans
        (unresolvedRVDs-on-clearVdsMsgs-collectFromMessages (DBC.messages d))
        (sym (WellFormedDBC.unresolved-empty wf)))

parseTextChars-on-formatChars :
    ∀ (d : DBC) → WellFormedDBC d
  → parseTextChars (formatChars d) ≡ inj₂ d
parseTextChars-on-formatChars d wf =
  trans (cong finalizeParse (parseDBCText-on-formatChars d wf))
        (finalizeParse-on-mkResult-clean d
          (advancePositions initialPosition (formatChars d)) wf)
