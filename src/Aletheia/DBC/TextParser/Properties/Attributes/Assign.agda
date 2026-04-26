{-# OPTIONS --without-K #-}

-- B.3.d Layer 3 Commit 3c.3 — `parseRawAttrAssign` and `parseRawAttrRel`
-- per-line construct roundtrips — facade module.
--
-- `parseRawAttrAssign` consumes
--   `"BA_" ws string-lit ws (attr-target ws)? raw-value ws? ";" newline ...`
-- with 5 target cases (ATgtNetwork as fall-through, ATgtNode /
-- ATgtMessage / ATgtSignal / ATgtEnvVar via 4-way `<|>` keyword
-- dispatch in `parseStandardAttrTarget`).
--
-- `parseRawAttrRel` consumes
--   `"BA_REL_" ws string-lit ws rel-target raw-value ws? ";" newline ...`
-- with 2 target cases (ATgtNodeMsg / ATgtNodeSig via `parseRelTarget`
-- 2-way `<|>`).
--
-- Sub-files (per-target × per emit-shape, 21 cases total):
--   * `Assign/Common.agda`  — shared head-classify and value-stops
--     helpers.
--   * `Assign/Network.agda` — ATgtNetwork × {RavString, frac, bareInt}
--     (3 dispatchers; fall-through case).
--   * `Assign/Node.agda`    — ATgtNode × 3 (BU_ keyword + ident).
--   * `Assign/Message.agda` — ATgtMessage × 3 (BO_ keyword + nat ID +
--     `wrapMsgTarget`).
--   * `Assign/Signal.agda`  — ATgtSignal × 3 (SG_ keyword + nat ID +
--     ident + `wrapSigTarget`).
--   * `Assign/EnvVar.agda`  — ATgtEnvVar × 3 (EV_ keyword + ident).
--   * `Assign/Rel.agda`     — ATgtNodeMsg + ATgtNodeSig × 3 (BA_REL_
--     plus per-target rel-keyword chain).
--
-- Splitting follows `feedback_properties_facade_split.md` and
-- pre-empts the soft-cap line growth.

module Aletheia.DBC.TextParser.Properties.Attributes.Assign where

open import Aletheia.DBC.TextParser.Properties.Attributes.Assign.Network public
  using ( parseRawAttrAssign-after-keyword-Network
        ; parseRawAttrAssign-roundtrip-ATgtNetwork-RavString
        ; parseRawAttrAssign-roundtrip-ATgtNetwork-RavDecRatFrac
        ; parseRawAttrAssign-roundtrip-ATgtNetwork-RavDecRatBareInt)

open import Aletheia.DBC.TextParser.Properties.Attributes.Assign.Node public
  using ( IdentNameStop
        ; parseRawAttrAssign-after-keyword-Node
        ; parseRawAttrAssign-roundtrip-ATgtNode-RavString
        ; parseRawAttrAssign-roundtrip-ATgtNode-RavDecRatFrac
        ; parseRawAttrAssign-roundtrip-ATgtNode-RavDecRatBareInt)

open import Aletheia.DBC.TextParser.Properties.Attributes.Assign.Message public
  using ( wrapMsgTarget-roundtrip
        ; parseMsgTgt-roundtrip
        ; parseRawAttrAssign-after-keyword-Message
        ; parseRawAttrAssign-roundtrip-ATgtMessage-RavString
        ; parseRawAttrAssign-roundtrip-ATgtMessage-RavDecRatFrac
        ; parseRawAttrAssign-roundtrip-ATgtMessage-RavDecRatBareInt)

open import Aletheia.DBC.TextParser.Properties.Attributes.Assign.Signal public
  using ( wrapSigTarget-roundtrip
        ; parseSigTgt-roundtrip
        ; parseRawAttrAssign-after-keyword-Signal
        ; parseRawAttrAssign-roundtrip-ATgtSignal-RavString
        ; parseRawAttrAssign-roundtrip-ATgtSignal-RavDecRatFrac
        ; parseRawAttrAssign-roundtrip-ATgtSignal-RavDecRatBareInt)

open import Aletheia.DBC.TextParser.Properties.Attributes.Assign.EnvVar public
  using ( parseEvTgt-roundtrip
        ; parseRawAttrAssign-after-keyword-EnvVar
        ; parseRawAttrAssign-roundtrip-ATgtEnvVar-RavString
        ; parseRawAttrAssign-roundtrip-ATgtEnvVar-RavDecRatFrac
        ; parseRawAttrAssign-roundtrip-ATgtEnvVar-RavDecRatBareInt)

open import Aletheia.DBC.TextParser.Properties.Attributes.Assign.Rel public
  using ( wrapNodeMsgTarget-roundtrip; wrapNodeSigTarget-roundtrip
        ; parseNodeMsgTgt-roundtrip; parseNodeSigTgt-roundtrip
        ; parseRawAttrRel-after-keyword-NodeMsg
        ; parseRawAttrRel-after-keyword-NodeSig
        ; parseRawAttrRel-roundtrip-ATgtNodeMsg-RavString
        ; parseRawAttrRel-roundtrip-ATgtNodeMsg-RavDecRatFrac
        ; parseRawAttrRel-roundtrip-ATgtNodeMsg-RavDecRatBareInt
        ; parseRawAttrRel-roundtrip-ATgtNodeSig-RavString
        ; parseRawAttrRel-roundtrip-ATgtNodeSig-RavDecRatFrac
        ; parseRawAttrRel-roundtrip-ATgtNodeSig-RavDecRatBareInt)
