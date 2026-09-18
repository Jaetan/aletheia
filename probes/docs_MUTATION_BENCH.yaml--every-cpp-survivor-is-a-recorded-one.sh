#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes docs/MUTATION_BENCH.yaml.
# Claim: every mutant that survives the C++ sweep is one of the recorded
# survivors, named by its mutator, its file and the text of its source line
# with how many share that line, and every recorded survivor still survives. The recorded set is the ledger
# below: a temporary's destructor removed (the void call Mull found at the
# site is the destructor, not the named call), a reserve given a constant, a
# hash mixed differently, a guard the code cannot reach, a wire field the
# kernel does not read, or a path held by a probe of its own. The count the
# baseline records is what this ledger says it is. Non-zero exit: a mutant
# survives that the ledger does not name, or a ledger row no longer
# survives; the diff names each. Exits 0 with a note when Mull or the
# mutation tree is not available, since the claim is untestable then.
set -u
cd "$(dirname "$0")/.." || exit 2
command -v mull-runner-23 > /dev/null || { echo "Mull not installed, claim untestable"; exit 0; }
[ -x cpp/build-mutation/unit_tests ] || { echo "no mutation tree built, claim untestable"; exit 0; }
py=python/.venv/bin/python
[ -x "$py" ] || exit 2
report=cpp/build-mutation/probe-ledger.json
rm -f "$report"
(cd cpp/build-mutation &&
    env -u ALETHEIA_LIB ALETHEIA_REPO_ROOT="$OLDPWD" mull-runner-23 ./unit_tests \
        --report-name=probe-ledger --reporters=Elements > /dev/null 2>&1) || true
[ -s "$report" ] || {
    echo "the sweep produced no report"
    exit 1
}
"$py" - "$report" <<'PY'
import collections
import json
import sys

LEDGER = """\
3	cxx_add_to_sub	include/aletheia/detail/cache_keys.hpp	return seed ^ (h + 0x9e3779b9 + (seed << 6U) + (seed >> 2U));
1	cxx_add_to_sub	src/client.cpp	if (off + k_absent_record_bytes > buf.size())
1	cxx_gt_to_ge	src/client.cpp	if (off + k_value_record_bytes > buf.size())
1	cxx_gt_to_ge	src/detail/loader_utils.cpp	if (uncompressed > std::numeric_limits<std::uint64_t>::max() - total)
1	cxx_lt_to_le	src/excel.cpp	for (std::size_t i = 0; i < count; ++i) {
1	cxx_remove_void_call	src/client.cpp	diags_.push_back(build_diagnostic(f));
1	cxx_remove_void_call	src/client.cpp	errors.push_back({.name = std::move(name), .reason = std::move(reason)});
1	cxx_remove_void_call	src/client.cpp	formulas.push_back(ltl::clone(*f));
2	cxx_remove_void_call	src/client.cpp	last_frames_.clear();
1	cxx_remove_void_call	src/client.cpp	result.absent.push_back(signal_name_at(names, read_u16(off)));
1	cxx_remove_void_call	src/detail/ffi_logic.cpp	args.push_back("-N" + std::to_string(rts_cores));
1	cxx_remove_void_call	src/excel.cpp	doc.create(path.string(), OpenXLSX::XLForceOverwrite);
2	cxx_remove_void_call	src/excel.cpp	doc.open(path.string());
1	cxx_remove_void_call	src/excel.cpp	doc.workbook().addWorksheet("Checks");
1	cxx_remove_void_call	src/excel.cpp	doc.workbook().addWorksheet("When-Then");
1	cxx_remove_void_call	src/excel.cpp	doc.workbook().worksheet("Sheet1").setName("DBC");
1	cxx_remove_void_call	src/excel.cpp	result.push_back(val.get<std::string>());
1	cxx_remove_void_call	src/excel.cpp	results.push_back(parse_simple_row(row.cells, row.number));
1	cxx_remove_void_call	src/excel.cpp	results.push_back(parse_when_then_row(row.cells, row.number));
1	cxx_remove_void_call	src/excel.cpp	rows.push_back(DataRow{.number = static_cast<int>(r), .cells = std::move(cells)});
1	cxx_remove_void_call	src/excel.cpp	signals.push_back(parse_dbc_signal(data_rows[idx].cells, data_rows[idx].number));
1	cxx_remove_void_call	src/json_parse.cpp	entries.push_back(parse_value_entry(e, "value-description value"));
1	cxx_remove_void_call	src/json_parse.cpp	entries.push_back(parse_value_entry(e, "valueTable entry value"));
1	cxx_remove_void_call	src/json_parse.cpp	errors.push_back({.name = SignalName{e.at("name").get<std::string>()},
1	cxx_remove_void_call	src/json_parse.cpp	messages.push_back(parse_message_def(m));
2	cxx_remove_void_call	src/json_parse.cpp	results.push_back(parse_property_result_entry(r));
1	cxx_remove_void_call	src/json_parse.cpp	signals.push_back(parse_signal_def(s));
1	cxx_remove_void_call	src/json_parse.cpp	values.push_back(v.get<std::string>());
1	cxx_remove_void_call	src/json_parse.cpp	values.push_back({.name = SignalName{v.at("name").get<std::string>()},
1	cxx_remove_void_call	src/json_parse.cpp	warnings.push_back(parse_stream_warning_entry(w));
1	cxx_remove_void_call	src/json_serialize.cpp	out.push_back(n.get());
1	cxx_remove_void_call	src/yaml.cpp	results.push_back(parse_check(entry));
1	cxx_replace_scalar_call	include/aletheia/detail/cache_keys.hpp	auto h = std::hash<std::uint32_t>{}(k.id_value);
2	cxx_replace_scalar_call	include/aletheia/detail/cache_keys.hpp	h = hash_combine(h, std::hash<bool>{}(k.is_extended));
2	cxx_replace_scalar_call	include/aletheia/detail/cache_keys.hpp	return hash_combine(h, std::hash<std::string>{}(k.signal_name));
3	cxx_replace_scalar_call	include/aletheia/detail/cache_keys.hpp	return hash_combine(std::hash<std::uint32_t>{}(k.first), std::hash<bool>{}(k.second));
1	cxx_replace_scalar_call	src/backend.cpp	if (!std::in_range<std::uint32_t>(indices.size()))
1	cxx_replace_scalar_call	src/backend.cpp	indices.size()));
1	cxx_replace_scalar_call	src/client.cpp	batch.responses.reserve(frames.size());
1	cxx_replace_scalar_call	src/client.cpp	diags_.reserve(properties.size());
2	cxx_replace_scalar_call	src/client.cpp	formulas.reserve(default_checks_.size() + checks.size());
1	cxx_replace_scalar_call	src/client.cpp	if (!diags_.empty()) {
1	cxx_replace_scalar_call	src/client.cpp	if (!slice.empty())
1	cxx_replace_scalar_call	src/client.cpp	names.reserve(msg.signals.size());
1	cxx_replace_scalar_call	src/client.cpp	resolved.denominators.reserve(signals.size());
1	cxx_replace_scalar_call	src/client.cpp	resolved.indices.reserve(signals.size());
1	cxx_replace_scalar_call	src/client.cpp	resolved.numerators.reserve(signals.size());
1	cxx_replace_scalar_call	src/excel.cpp	auto const headers = headers_from_row(ws, static_cast<std::size_t>(ws.columnCount()));
1	cxx_replace_scalar_call	src/excel.cpp	if (headers[i].empty())
1	cxx_replace_scalar_call	src/excel.cpp	signals.reserve(indices.size());
2	cxx_replace_scalar_call	src/ffi_backend.cpp	auto const timestamp = static_cast<std::uint64_t>(ts.count());
1	cxx_replace_scalar_call	src/ffi_backend.cpp	dlclose(handle_);
1	cxx_replace_scalar_call	src/ffi_backend.cpp	if (!b.has_value())
1	cxx_replace_scalar_call	src/ffi_backend.cpp	ptrs.reserve(rts_argv.size());
1	cxx_replace_scalar_call	src/json_parse.cpp	: std::in_range<T>(j.get<std::int64_t>());
2	cxx_replace_scalar_call	src/json_parse.cpp	if (input == ack_compact || input == ack_spaced)
1	cxx_replace_scalar_call	src/json_parse.cpp	issues.reserve(j.at("issues").size());
1	cxx_replace_scalar_call	src/json_parse.cpp	out.reserve(arr.size());
1	cxx_replace_scalar_call	src/json_parse.cpp	payload.reserve(data.size());
1	cxx_replace_scalar_call	src/json_parse.cpp	results.reserve(raw_results.size());
1	cxx_replace_scalar_call	src/json_parse.cpp	vals.reserve(arr.size());
1	cxx_replace_scalar_call	src/rational_renderer.cpp	if (!d.path.empty()) {
1	cxx_replace_scalar_call	src/rational_renderer.cpp	if (!env_sv.empty()) {
1	cxx_replace_scalar_call	src/rational_renderer.cpp	if (d.path.empty()) // first-write-wins
1	cxx_replace_scalar_call	src/rational_renderer.cpp	if (lib_path.empty()) {
"""
recorded = collections.Counter()
for row in LEDGER.strip("\n").split("\n"):
    count, mutator, rel, text = row.split("\t", 3)
    recorded[(mutator, rel, text)] = int(count)
observed = collections.Counter()
for f in json.load(open(sys.argv[1], encoding="utf-8"))["files"].values():
    for m in f.get("mutants", []):
        if m["status"] != "Survived":
            continue
        rel = m["id"].split("/cpp/", 1)[1].split(":")[0]
        line = int(m["location"]["start"]["line"])
        with open("cpp/" + rel, encoding="utf-8") as src:
            text = src.read().split("\n")[line - 1].strip()
        observed[(m["mutatorName"], rel, text)] += 1
bad = False
for row, n in sorted((observed - recorded).items()):
    print(f"survives {n} more than the ledger records:", "\t".join(row))
    bad = True
for row, n in sorted((recorded - observed).items()):
    print(f"in the ledger, {n} no longer survive:", "\t".join(row))
    bad = True
sys.exit(1 if bad else 0)
PY
