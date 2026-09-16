#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes cpp/include/aletheia/client.hpp.
# Claim: every identifier, document section and event name the header's
# comments cite resolves in the tree: the Agda adequacy lemma and its module,
# the PROTOCOL.md and CANCELLATION.md sections, the GLOSSARY entry, the error
# kind and code, the log events, the FFI export, and the client method the
# constructor comment names. Non-zero exit: a citation resolves nowhere.
set -u
cd "$(dirname "$0")/.." || exit 2
status=0
need() { grep -qE "$2" "$3" || { echo "unresolved: $1"; status=1; }; }
need "lemma streaming-warms-cache" '^streaming-warms-cache' src/Aletheia/Protocol/Adequacy/StreamingWarm.agda
need "PROTOCOL.md streaming semantics section" '^### Streaming Semantics: Soundness vs\. Completeness' docs/architecture/PROTOCOL.md
need "CANCELLATION.md partial-work section" '^## .*Partial-Work Semantics: Commit-Prefix-and-Report' docs/architecture/CANCELLATION.md
need "GLOSSARY well-formed DBC entry" '^\*\*Well-formed DBC\*\*' docs/GLOSSARY.md
need "ErrorKind::TextRoundtrip" '^    TextRoundtrip' cpp/include/aletheia/error.hpp
need "ErrorCode::HandlerTextRoundtripFailed" 'HandlerTextRoundtripFailed,' cpp/include/aletheia/error.hpp
need "log event frame.processed" 'name: frame\.processed' docs/LOG_EVENTS.yaml
need "log event cache.full" 'name: cache\.full' docs/LOG_EVENTS.yaml
need "FFI export aletheia_process" 'foreign export ccall aletheia_process' haskell-shim/src/AletheiaFFI.hs
need "Agda wfTextIssues" 'wfTextIssues' src/Aletheia/DBC/TextParser/WellFormedCheck.agda
need "method add_checks cited by the constructor comment" 'auto add_checks\(' cpp/include/aletheia/client.hpp
need "dlc_to_bytes" 'auto dlc_to_bytes\(' cpp/include/aletheia/types.hpp
exit $status
