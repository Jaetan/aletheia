// SPDX-License-Identifier: BSD-2-Clause
//
// B.3.j — DBC text parser cross-binding parity gate (C++ side).
//
// Scope. This is a binding-layer integration test on a finite fixture corpus.
// It does NOT extend, replace, or stand in for the universal Agda roundtrip
// theorem proven in B.3.d (∀ d → WellFormedDBC d → parseText (formatText d)
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
// Canonical form: sorted JSON keys + 2-space indent + trailing newline + the
// "emit int when denominator=1" rule (already shared by the binding's
// internal serializer). nlohmann::json is std::map-backed by default and
// dump(2) produces sorted keys naturally; one post-processing pass drops
// "extended": false from message envelopes (Agda's wire format omits
// "extended" for standard CAN frames; comment / attribute targets already
// follow the same convention via attach_can_id).

#include "detail/json.hpp"

#include <catch2/catch_test_macros.hpp>

#include <aletheia/aletheia.hpp>

#include <nlohmann/json.hpp>

#include <cstdlib>
#include <filesystem>
#include <fstream>
#include <sstream>
#include <string>
#include <vector>

using namespace aletheia;
namespace fs = std::filesystem;

namespace {

auto find_lib() -> fs::path {
    if (auto* env = std::getenv("ALETHEIA_LIB"))
        return env;
    auto project_root = fs::path{__FILE__}.parent_path().parent_path().parent_path();
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
    auto project_root = fs::path{__FILE__}.parent_path().parent_path().parent_path();
    return project_root / "python" / "tests" / "fixtures" / "dbc_corpus";
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
    std::sort(dbc_files.begin(), dbc_files.end());
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
