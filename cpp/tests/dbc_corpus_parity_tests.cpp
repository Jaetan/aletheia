// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// DBC text parser cross-binding parity gate (C++ side).
//
// Scope. This is a binding-layer integration test on a finite fixture corpus.
// It does NOT extend, replace, or stand in for the universal Agda roundtrip
// theorem (∀ d → WellFormedDBC d → parseText (formatText d)
// ≡ inj₂ d, in Aletheia/DBC/TextParser/Properties/Substrate/Unsafe.agda).
// Parser correctness is established by that proof, universally over the DBC
// domain. What this test validates instead is that the C++ binding's
// wire-to-native conversion (Agda JSON → DbcDefinition) preserves the wire
// bytes faithfully. A failure here means the C++ binding lost or mangled
// fields on parse, not that the Agda parser is wrong.
//
// The committed parity snapshots in
// python/tests/fixtures/dbc_corpus/parity_snapshots/ are the cross-binding
// oracle — the Python (test_dbc_corpus_parity.py) and Go
// (dbc_corpus_parity_test.go) parity tests assert byte equality against the
// same files. When all three match, the bindings have observed identical
// DbcDefinition structure for every fixture.
//
// Canonical form: sorted JSON keys, 2-space indent, trailing newline and the
// "emit int when denominator=1" rule, all of which the binding's own
// serializer already produces. nlohmann::json is std::map-backed, so dump(2)
// sorts the keys, and json_serialize.cpp omits "extended" on standard frames
// the way the Agda wire form does, so the snapshot is the dump with nothing
// done to it afterwards.

#include "detail/json.hpp"

#include <catch2/catch_test_macros.hpp>

#include <aletheia/aletheia.hpp>

#include <nlohmann/json.hpp>

#include <algorithm>
#include <cstdlib>
#include <filesystem>
#include <fstream>
#include <sstream>
#include <stop_token>
#include <string>
#include <utility>
#include <vector>

#include "repo_root.hpp"

using aletheia::test::repo_root;

using namespace aletheia;
namespace fs = std::filesystem;

namespace {

auto find_lib() -> fs::path {
    // An empty or stale ALETHEIA_LIB must not shadow a library that is present,
    // else a missing file becomes a construction failure rather than the skip.
    if (auto* env = std::getenv("ALETHEIA_LIB")) {
        if (const fs::path p{env}; !p.empty() && fs::exists(p))
            return p;
    }
    auto project_root = repo_root();
    auto lib = project_root / "build" / "libaletheia-ffi.so";
    if (fs::exists(lib))
        return lib;
    auto dist = project_root / "dist" / "aletheia" / "lib" / "libaletheia-ffi.so";
    if (fs::exists(dist))
        return dist;
    SKIP("libaletheia-ffi.so not found — run 'cabal run shake -- build' first");
    return {};
}

auto corpus_dir() -> fs::path {
    return repo_root() / "python" / "tests" / "fixtures" / "dbc_corpus";
}

auto read_file(const fs::path& p) -> std::string {
    std::ifstream f(p);
    std::stringstream buf;
    buf << f.rdbuf();
    return buf.str();
}

auto canonical_dbc_json(const DbcDefinition& dbc) -> std::string {
    // Round-trip via the existing detail::serialize_parsed_dbc_response so
    // we don't duplicate the dbc_to_json walker; extract the "dbc" field
    // back out and dump(2). nlohmann::json is std::map-backed so dump
    // produces sorted keys naturally; json_serialize.cpp already mirrors
    // the Agda wire form for "extended" (omitted on standard frames) and
    // "presence" (explicit "always"), so no post-processing is needed.
    auto envelope = detail::serialize_parsed_dbc_response(dbc);
    auto parsed = nlohmann::json::parse(envelope);
    return parsed.at("dbc").dump(2) + "\n";
}

} // namespace

TEST_CASE("DBC corpus parity — Agda parse_dbc_text matches Python oracle",
          "[integration][parity][dbc]") {
    auto lib = find_lib();
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));

    auto dir = corpus_dir();
    auto parity_dir = dir / "parity_snapshots";
    REQUIRE(fs::exists(dir));
    REQUIRE(fs::exists(parity_dir));

    std::vector<fs::path> dbc_files;
    for (const auto& entry : fs::directory_iterator(dir))
        if (entry.path().extension() == ".dbc")
            dbc_files.push_back(entry.path());
    std::ranges::sort(dbc_files);
    REQUIRE_FALSE(dbc_files.empty());

    for (const auto& dbc_path : dbc_files) {
        DYNAMIC_SECTION("corpus DBC: " << dbc_path.filename().string()) {
            auto text = read_file(dbc_path);
            auto result = client.parse_dbc_text(std::stop_token{}, text);
            REQUIRE(result.has_value());

            auto actual = canonical_dbc_json(result->dbc);

            auto snapshot_path = parity_dir / (dbc_path.stem().string() + ".json");
            REQUIRE(fs::exists(snapshot_path));
            auto expected = read_file(snapshot_path);

            CHECK(actual == expected);
        }
    }
}
