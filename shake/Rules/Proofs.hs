-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
-- | The proof gates: the proof-only modules check-properties type-checks,
-- the import and invariant checks over the Agda tree, and the module count.
module Rules.Proofs (proofRules) where

import Development.Shake
import System.Exit (ExitCode(..))
import Data.List (isPrefixOf, stripPrefix)
import Data.Char (isAlphaNum)
import Control.Monad (when, unless)
import Shared

-- | Proof-only modules — the SINGLE SOURCE for `check-properties`, type-checked
-- in one warm `agda --interaction-json` process (tools.warm_check_properties).
-- Each is unreachable from Main.agda's runtime closure, so the main
-- build walk does not cover it; each is an explicit walk root, and dropping one
-- silently stops type-checking its subtree.

proofModules :: [String]
proofModules =
    -- Parser / top-level JSON
    [ "Aletheia/Parser/Properties.agda"
    , "Aletheia/JSON/Properties.agda"
    -- Protocol
    , "Aletheia/Protocol/JSON/Properties.agda"
    , "Aletheia/Protocol/JSON/Properties/Sound.agda"
    , "Aletheia/Protocol/JSON/Properties/Roundtrip.agda"
    , "Aletheia/Protocol/ResponseFormat/Properties.agda"
    , "Aletheia/Protocol/ResponseFormat/Properties/JSONText.agda"
    , "Aletheia/Protocol/FrameProcessor/Properties.agda"
    , "Aletheia/Protocol/Handlers/Properties.agda"
    -- The FormatDBCText handler emits a DBCTextResponse ONLY when its text
    -- provably re-parses to the input DBC.  This root machine-checks that
    -- promise (`formatDBCTextResult-sound`), so the "provably round-trips, or
    -- refuse" guarantee is a verified theorem, not merely definitional.  Its own
    -- root (mirrors the RoundTripCheck/Sound + WellFormedCheck/Sound roots): the
    -- narrow Handlers/Properties.agda covers only SetProperties routing.
    , "Aletheia/Protocol/Handlers/Properties/FormatDBCText.agda"
    , "Aletheia/Protocol/Adequacy/WarmCache.agda"
    -- Discharges WarmCache's `AllCached` premise (streaming-warms-cache);
    -- unreachable from Main's runtime closure and unimported by other proofs,
    -- so an explicit root keeps the dedicated proof gate covering it.
    , "Aletheia/Protocol/Adequacy/StreamingWarm.agda"
    -- CAN
    , "Aletheia/CAN/Encoding/Properties.agda"
    , "Aletheia/CAN/Batch/Properties.agda"
    , "Aletheia/CAN/DLC/Properties.agda"
    -- What the binary entries' frame parser accepts and refuses
    -- (CAN/Frame/Parse.agda): reached by no other proof, so its own root.
    , "Aletheia/CAN/Frame/Parse/Properties.agda"
    , "Aletheia/CAN/SignalExtraction/Properties.agda"
    , "Aletheia/CAN/Endianness/Properties.agda"
    -- DBC
    , "Aletheia/DBC/Properties.agda"
    -- Gate⇒checker geometry deadness/liveness theorem: entry-gate acceptance
    -- (either route) empties every geometry checker arm, and the arms are
    -- non-vacuous.  Unimported by other proofs, so it needs its own root.
    , "Aletheia/DBC/Properties/GeometryGateDeadness.agda"
    , "Aletheia/DBC/JSONParser/Properties.agda"
    -- What the size-bound checker (DBC/Bounds.agda) accepts and refuses:
    -- reached by no other proof, so its own root.
    , "Aletheia/DBC/Bounds/Properties.agda"
    , "Aletheia/DBC/Validity/Theorem.agda"
    , "Aletheia/DBC/Formatter/Properties.agda"
    , "Aletheia/DBC/Formatter/Bounded.agda"
    , "Aletheia/DBC/TextParser/Properties.agda"
    , "Aletheia/DBC/TextParser/DecRatParse/Properties.agda"
    -- RationalRenderer itself IS reached from Main (FFI shim); .Properties is not.
    , "Aletheia/DBC/RationalRenderer/Properties.agda"
    , "Aletheia/DBC/RationalRenderer/Faithful.agda"
    -- DecimalEntry itself IS reached from Main (FFI shim); .Properties is not.
    , "Aletheia/DBC/TextParser/DecimalEntry/Properties.agda"
    -- TextParser / TextFormatter aggregators: not proofs, but pulling them in
    -- forces the full submodule tree to type-check (unreachable from Main).
    , "Aletheia/DBC/TextParser.agda"
    , "Aletheia/DBC/TextFormatter.agda"
    -- The TextFormatter theorem facade (mirrors TextParser/Properties, which is
    -- a root above); the module itself imports it from neither runtime nor proof
    -- closure, so it needs its own root.
    , "Aletheia/DBC/TextFormatter/Properties.agda"
    , "Aletheia/DBC/DecRat/RationalRoundtrip.agda"
    , "Aletheia/DBC/DecRat/RationalSoundness.agda"
    -- WellFormedText / ValueDescResolves / Format DSL: walk roots currently
    -- unimported by downstream proofs; explicit roots keep them from bit-rotting.
    , "Aletheia/DBC/Formatter/WellFormedText.agda"
    , "Aletheia/DBC/Formatter/WellFormedText/ValueDescResolves.agda"
    -- E.2 bounded slice: derives the five per-section name-stop fields of
    -- WellFormedTextDBCAgg from Identifier-validity.
    -- Unimported — the FFI-boundary consumer is deferred along with the two
    -- heavy fields (MessageWF / WFAttribute) — so an explicit root keeps it
    -- from bit-rotting.
    , "Aletheia/DBC/TextParser/Properties/WellFormedFromValidity.agda"
    -- Text round-trip checker soundness facade: proves the runtime decision
    -- procedure `wfTextIssues` decides `WellFormedTextDBCAgg` — `wfTextIssues d
    -- ≡ [] ⟺ WellFormedTextDBCAgg d`.  One root here covers
    -- the whole subtree transitively: the checker (`WellFormedCheck`) and the
    -- two soundness leaves (`Sound/{Signal,Attr}`).  Needs an explicit
    -- root: proof modules are never in Main's closure (`check-no-properties-in-
    -- runtime` enforces that), so nothing else would type-check them.
    , "Aletheia/DBC/TextParser/Properties/WellFormedCheck/Sound.agda"
    -- The exact-check soundness (axiom-free):
    -- `roundTripsᵇ d ≡ true → parseText (formatText d) ≡ inj₂ d`.  Its own root
    -- because nothing else imports it — `RoundTripCheck` and the equality tower
    -- `Decidable.Equality.Full` are reached via the Substrate.Unsafe root, which
    -- imports them for the coherence theorems.
    , "Aletheia/DBC/TextParser/Properties/RoundTripCheck/Sound.agda"
    -- A.2 BO_TX_BU_ inverse-bridge: `attachSenders (collectSenders msgs) msgs
    -- ≡ msgs` under msg-id uniqueness.  Unimported
    -- until the formatter/parser integration lands the senders section on the
    -- text wire — explicit root keeps the base bridge from bit-rotting.
    , "Aletheia/DBC/TextParser/Properties/Aggregator/Refine/Senders.agda"
    -- A.2 composition: nests the senders bridge with the VAL_ value-desc
    -- bridge over `clearBothMsg` parse output — the form `buildDBC` presents
    -- once the senders section is wired.  Also unimported until integration;
    -- explicit root keeps the composition green in the interim.
    , "Aletheia/DBC/TextParser/Properties/Aggregator/Refine/SendersCompose.agda"
    , "Aletheia/DBC/TextParser/Format.agda"
    , "Aletheia/DBC/TextParser/Format/RegressionTests.agda"
    , "Aletheia/DBC/TextParser/Format/ValueTable.agda"
    , "Aletheia/DBC/CanonicalReceivers.agda"
    , "Aletheia/DBC/TextParser/Format/Receivers.agda"
    , "Aletheia/DBC/TextParser/Format/Receivers/Roundtrip.agda"
    -- A.2 BO_TX_BU_ line Format DSL + roundtrip (mirrors ValueDescription).
    -- Unimported until the parser/formatter integration; explicit root keeps
    -- the DSL roundtrip green in the interim.
    , "Aletheia/DBC/TextParser/Format/MessageSenders.agda"
    -- A.2 BO_TX_BU_ dispatcher slim + section stops + emit bridge (mirrors
    -- Dispatcher.Simple.ValueDesc).  Transitively covers the formatter emitter
    -- (TextFormatter.MessageSenders).  Unimported until the atomic integration
    -- wires the TBO dispatch arm; explicit root keeps it green meanwhile.
    , "Aletheia/DBC/TextParser/Properties/Aggregator/Dispatcher/Simple/MsgSenders.agda"
    , "Aletheia/DBC/TextParser/Format/SignalLine.agda"
    , "Aletheia/DBC/TextParser/Format/SignalLine/Roundtrip.agda"
    , "Aletheia/DBC/TextParser/Format/Nodes.agda"
    , "Aletheia/DBC/TextParser/Format/Preamble.agda"
    -- This ONE root (Substrate/Unsafe, the sole non-`--safe` module) transitively
    -- covers the entire Aggregator/Universal subtree (Dispatcher / ManyTopStmts /
    -- Partition / Refine / BodyBridge / Foundations).
    , "Aletheia/DBC/TextParser/Properties/Substrate/Unsafe.agda"
    -- LTL
    , "Aletheia/LTL/JSON/Properties.agda"
    , "Aletheia/LTL/Adequacy.agda"
    , "Aletheia/LTL/Adequacy/Pipeline.agda"
    , "Aletheia/LTL/Coalgebra/Properties.agda"
    , "Aletheia/LTL/Semantics/MTL.agda"
    , "Aletheia/LTL/Semantics/Duality.agda"
    , "Aletheia/LTL/TruthVal/Properties.agda"
    , "Aletheia/LTL/SignalPredicate/Cache/Properties.agda"
    , "Aletheia/LTL/SignalPredicate/Evaluation/Properties.agda"
    ]

-- | The proof gates and the module count.
proofRules :: Rules ()
proofRules = do
    phony "check-properties" $ do
        -- Type-check every proof-only module in ONE warm `agda --interaction-json`
        -- process (stdlib + shared deps load once) instead of one `agda Module.agda`
        -- subprocess per module.  Catches proof-obligation failures (Status
        -- checked:false) and writes `.agdai` so the downstream build reuses the
        -- interfaces.  Replaces the former cold batch (one agda process per module,
        -- ~13× slower: 629s -> ~48s); same `proofModules` single source of truth.
        putInfo "Type-checking proof-only modules (one warm agda process)..."
        cmd_ pythonBin ("-m" : "tools.warm_check_properties" : proofModules)

    -- `iwyu` — regenerate the relevant .agdai and run the import analysis WITHOUT a
    -- full .hs/.so rebuild.  The .agda → .agdai (type-check) route is distinct from
    -- the .agda → .hs (compile) route the .so rule tracks; iwyu consumes .agdai
    -- only, so this does NOT depend on `build`.  The .agdai are regenerated
    -- incrementally by Agda's OWN interface cache — tools.iwyu's warm process
    -- re-checks each scoped module and Agda reuses unchanged interfaces, so only
    -- what actually changed is recomputed (no Shake-side .agdai tracking needed).
    -- A plain phony, like the other check-* gates: it always runs the analysis (a
    -- check should run, not be skipped behind a result-cache stamp — which would
    -- also miss changes to the iwyu tool itself).  Whole-tree (`--all`); for the
    -- branch-diff scope run `tools.iwyu --check --diff`.  `cabal run shake -- iwyu`.
    phony "iwyu" $ do
        need ["check-stdlib-version"]
        putInfo "Regenerating .agdai (Agda interface cache) + running IWYU..."
        cmd_ pythonBin "-m" "tools.iwyu" "--check" "--all"

    phony "check-invariants" $ do
        -- Enforce "postulates and Unsafe modules are limited to the
        -- allowlisted substrate" project-wide.
        --
        -- Allowlist policy: exactly one Unsafe module is permitted —
        -- `Aletheia/DBC/TextParser/Properties/Substrate/Unsafe.agda`,
        -- which carries the two `String ↔ List Char` bridging axioms
        -- (`toList∘fromList`, `fromList∘toList`) needed to compose the
        -- universal roundtrip theorem.  These mirror stdlib's
        -- `Data.String.Unsafe` (proven by `trustMe` under `--with-K`),
        -- which is structurally unprovable in `--safe --without-K`.
        -- Any other `Unsafe`-named module OR any other `^postulate`
        -- line is rejected — adding one requires a paired update of
        -- `allowedUnsafe` below and explicit user approval.
        --
        -- The grep below uses -l (filenames only) so we can compare
        -- paths against the allowlist; -r recurses; --include limits
        -- to .agda; -E enables the regex.  grep exits 1 when there
        -- are no matches, so we take Exit + Stdout explicitly and
        -- ignore the exit code.
        let allowedUnsafe =
                ["Aletheia/DBC/TextParser/Properties/Substrate/Unsafe.agda"]
        -- The scan must be able to say "I could not look" out loud.  grep exits
        -- 0 (matched), 1 (no match) or >=2 (ERROR: unreadable path, bad regex) —
        -- and an error prints nothing.  Empty output is exactly how this gate
        -- spells "no unauthorised postulates", so discarding the exit code would
        -- let a scan that never ran certify the tree clean.
        (Exit postulateRc, Stdout postulateOut) <-
            cmd "grep" "-rln" "--include=*.agda" "-E" "^postulate" "src/"
        case postulateRc of
            ExitFailure n | n >= 2 ->
                error $ "check-invariants failed: grep could not scan src/ for "
                     ++ "postulates (exit " ++ show n ++ "). The scan did not run, "
                     ++ "so its empty result says nothing about the tree."
            _ -> return ()
        -- Assert the input exists, not that postulates do: a tree with ZERO
        -- postulates is the goal state and must pass, but a scan over ZERO Agda
        -- sources has lost its input rather than proved anything.
        agdaSourceCount <- length <$> getDirectoryFiles "src" ["//*.agda"]
        when (agdaSourceCount == 0) $
            error $ "check-invariants failed: no .agda sources found under src/. "
                 ++ "The postulate/Unsafe scan would pass vacuously over an empty "
                 ++ "tree; fix the checkout before trusting this gate."
        let postulateFiles = lines (postulateOut :: String)
            stripSrc f = case stripPrefix "src/" f of
                           Just rest -> rest
                           Nothing   -> f
            unauthorisedPostulate =
                filter (\f -> stripSrc f `notElem` allowedUnsafe) postulateFiles
        unless (null unauthorisedPostulate) $ do
            putError $ "^postulate found in non-allowlisted Agda source:\n"
                    ++ unlines unauthorisedPostulate
            error "check-invariants failed"
        -- Two glob forms: "//*.Unsafe.agda" matches dotted suffixes
        -- (e.g. `Foo.Unsafe.agda`); "//Unsafe.agda" matches leaf
        -- `Unsafe.agda` files (the stdlib-style layout used by the
        -- substrate module).  Union of matches is the candidate set.
        unsafeMatches <-
            getDirectoryFiles "src" ["//*.Unsafe.agda", "//Unsafe.agda"]
        let unauthorisedUnsafe =
                filter (`notElem` allowedUnsafe) unsafeMatches
        unless (null unauthorisedUnsafe) $ do
            putError $ "Unauthorised Unsafe-named module(s) found: "
                    ++ show unauthorisedUnsafe
            error "check-invariants failed"
        putInfo $ "Invariants OK: postulates and Unsafe modules limited "
               ++ "to the allowlisted substrate."

    phony "check-no-properties-in-runtime" $ do
        -- EXACT runtime-closure gate: the compiled foreign library
        -- `libaletheia-ffi.so` must contain NO `Aletheia.DBC.Properties.*` module.
        -- That namespace is RESERVED for proofs (standalone lemmas); the decision
        -- procedures the runtime needs live in `Aletheia.DBC.Decidable.*`.  The
        -- foreign-library `other-modules` in aletheia.cabal is the honest closure
        -- (its `-Werror=missing-home-modules` drift gate keeps it exact), so a
        -- `DBC.Properties.*` line there means a runtime path reached a proof module.
        --
        -- SCOPE: `DBC.Properties.*` ONLY, not every `.Properties`.  The Format-DSL
        -- proofs under `DBC.TextParser.*.Properties.*` ride in the closure BY
        -- DESIGN — the proof-carrying `iso`/`refined` DSL bundles a printer+parser
        -- with its round-trip proof (`@0`-erased in the binary, so zero runtime
        -- cost), reached via `Format.agda`.  No naming scheme removes them without
        -- gutting the verified-by-construction DSL, and this pattern does not match
        -- them (their `.Properties` sits deeper than `DBC.Properties`).
        --
        -- Naming-blind closure drift (a runtime import transitively dragging proof
        -- modules that do NOT match this prefix) is covered by the sibling
        -- snapshot gate `tools/check_runtime_closure.py`, which pins the whole
        -- closure to a reviewed snapshot.
        let cabalFile = "haskell-shim/aletheia.cabal"
        -- Read and match here rather than shelling out to grep: the comparison is
        -- exact (no regex dialect whose portability must be reasoned about), a
        -- missing file throws instead of yielding the empty output this gate reads
        -- as "clean", and there is no subprocess exit code to discard.
        cabalText <- liftIO $ readFile cabalFile
        let numbered = zip [(1 :: Int) ..] (lines cabalText)
            -- The boundary is whatever follows `…DBC.Properties`: end-of-name is a
            -- hit (the facade module itself), and so is any character that cannot
            -- continue a module name.  A sibling such as `DBC.PropertiesFoo` is a
            -- different module and must not trip the gate.
            isModuleChar c = isAlphaNum c || c == '_' || c == '\''
            offending =
                [ (n, l)
                | (n, l) <- numbered
                , Just rest <- [stripPrefix "MAlonzo.Code.Aletheia.DBC.Properties"
                                            (strip l)]
                , case rest of
                    []      -> True
                    (c : _) -> not (isModuleChar c)
                ]
            malonzoCount =
                length [ () | (_, l) <- numbered, "MAlonzo.Code." `isPrefixOf` strip l ]
        -- Assert the input: the foreign library's closure always lists MAlonzo
        -- modules, so finding none means this read lost the file's shape rather
        -- than that the closure is free of DBC.Properties.*.
        -- The count is the `MAlonzo.Code.*` subset: the closure also carries
        -- MAlonzo's own runtime modules (MAlonzo.RTE, MAlonzo.RTE.Float), which
        -- are not compiled Agda and cannot be a DBC.Properties.* leak.
        when (malonzoCount == 0) $
            error $ "check-no-properties-in-runtime failed: " ++ cabalFile
                 ++ " lists no MAlonzo.Code.* modules, so there was nothing to "
                 ++ "check and a pass here would be vacuous."
        unless (null offending) $ do
            putError $ "A DBC.Properties.* module is in the runtime .so closure "
                    ++ "(it must live in DBC.Decidable.*):\n"
                    ++ unlines [ show n ++ ": " ++ strip l | (n, l) <- offending ]
            error "check-no-properties-in-runtime failed"
        putInfo $ "No DBC.Properties.* modules in the runtime .so closure ("
               ++ show malonzoCount ++ " MAlonzo.Code.* modules checked)."

    phony "check-proof-coverage" $ do
        -- Exhaustiveness gate for the proof checker.  Every module under src/
        -- must be type-checked by `build` (Main's runtime closure) OR
        -- `check-properties` (the `proofModules` walk roots + their imports).
        -- A module covered only by the whole-tree `iwyu --all` pass is silently
        -- skipped by `cabal run shake -- check-properties` (the documented proof
        -- gate), so a broken proof there would slip past a local proof run.
        -- This gate forbids that — `proofModules` cannot drift incomplete again
        -- (it had, twice: TextFormatter/Properties + Adequacy/StreamingWarm).
        -- The tool reads `proofModules` from this file, so there is no second
        -- copy to keep in sync.
        cmd_ pythonBin "-m" "tools.check_proof_coverage"

    phony "count-modules" $ do
        agdaFiles <- getDirectoryFiles "src" ["//*.agda"]
        let n = length agdaFiles
        putInfo $ "Agda modules under src/: " ++ show n
