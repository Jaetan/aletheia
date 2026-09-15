# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes docs/FEATURE_MATRIX.yaml and docs/development/DEFERRED_ITEMS.md.
# Claim: both describe the installed C++ surface as shipping a fixed
# canned-acknowledgement factory plus the backend interface as a seam for a
# consumer's own double. Each half is checked against the installed headers: the
# factory answers, and a double written outside the tree compiles and runs
# through a client.
# Non-zero exit: one of the two halves does not hold.
# Exits 2 when the library archive is not built.
set -u
cd "$(dirname "$0")/.." || exit 2
lib=cpp/build/libaletheia-cpp.so
# The library is shared and carries its own dependencies, so a scratch binary
# links it alone; -Wl,-rpath gives the loader the directory the linker already has.
rpath="-Wl,-rpath,$(cd cpp/build && pwd)"
[ -f "$lib" ] || exit 2

fail=0
grep -q 'a fixed canned-ack/success backend' docs/FEATURE_MATRIX.yaml || {
    echo "FAIL: the matrix note no longer describes a fixed canned-acknowledgement factory"
    fail=1
}
grep -q 'factory (canned acks/successes)' docs/development/DEFERRED_ITEMS.md || {
    echo "FAIL: the deferred item no longer describes a fixed canned-acknowledgement factory"
    fail=1
}

scratch=cpp/build/probe-scratch/di-seam
mkdir -p "$scratch" || exit 2
cat > "$scratch/t.cpp" <<'CPP'
#include <aletheia/backend.hpp>
#include <aletheia/client.hpp>

#include <memory>
#include <string>

// A double written the way an outside consumer would write one: derived from
// the published interface, using no header the install does not carry.
namespace {
class OwnDouble : public aletheia::IBackend {
    static inline char sentinel = 0;

public:
    auto init() -> aletheia::BackendState override {
        return aletheia::BackendState{*this, &sentinel};
    }
    auto process(const aletheia::BackendState&, std::string_view) -> std::string override {
        return R"({"status":"ack"})";
    }
    auto send_frame_binary(const aletheia::BackendState&, aletheia::Timestamp,
                           const aletheia::CanId&, aletheia::Dlc, std::span<const std::byte>,
                           std::optional<bool>, std::optional<bool>) -> std::string override {
        return R"({"status":"ack"})";
    }
    auto send_error_binary(const aletheia::BackendState&, aletheia::Timestamp)
        -> std::string override {
        return R"({"status":"ack"})";
    }
    auto send_remote_binary(const aletheia::BackendState&, aletheia::Timestamp,
                            const aletheia::CanId&) -> std::string override {
        return R"({"status":"ack"})";
    }
    auto start_stream_binary(const aletheia::BackendState&) -> std::string override {
        return R"({"status":"ack"})";
    }
    auto end_stream_binary(const aletheia::BackendState&) -> std::string override {
        return R"({"status":"ack"})";
    }
    auto format_dbc_binary(const aletheia::BackendState&) -> std::string override {
        return R"({"status":"ack"})";
    }
    auto extract_signals_binary(const aletheia::BackendState&, const aletheia::CanId&,
                                aletheia::Dlc, std::span<const std::byte>) -> std::string override {
        return R"({"status":"ack"})";
    }

protected:
    void close(void*) override {}
};
} // namespace

int main() {
    // The seam: a consumer's own double drives a client.
    aletheia::AletheiaClient own{std::make_unique<OwnDouble>()};
    // The factory: the fixed double the documents describe.
    auto fixed = aletheia::make_mock_backend();
    if (!fixed)
        return 3;
    aletheia::AletheiaClient canned{std::move(fixed)};
    return 0;
}
CPP
clang++-22 -std=c++23 -Icpp/include "$scratch/t.cpp" "$lib" $rpath -ldl -lpthread \
    -o "$scratch/t" > "$scratch/compile.log" 2>&1 || {
    echo "FAIL: a consumer's own double does not compile against the installed headers"
    tail -5 "$scratch/compile.log"
    exit 1
}
"$scratch/t" || {
    echo "FAIL: a consumer's own double does not drive a client"
    exit 1
}

[ "$fail" -eq 0 ] || exit 1
echo "PASS: the fixed factory and the interface seam are both as the documents describe"
