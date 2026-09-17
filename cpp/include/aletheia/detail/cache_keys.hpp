// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
#pragma once

// =====================================================================
// WARNING: PRIVATE IMPLEMENTATION HEADER — DO NOT INCLUDE DIRECTLY.
// Use #include <aletheia/client.hpp> instead.
// =====================================================================
//
// Internal cache key types for AletheiaClient. Lives under
// `aletheia::detail::` and is **not part of the supported public API**:
//   * Names, layouts, and signatures may change in any minor release
//     without notice or migration path.
//   * No source-level or ABI compatibility guarantees apply.
//   * Out-of-scope of semver — patch releases may break consumers that
//     touched these types directly.
//
// Why is the header installed at all?
//   `<aletheia/client.hpp>` includes this file and uses the concrete
//   types (FrameKey, FrameKeyLess, SignalKey, MessageKey) in
//   AletheiaClient's *private* member declarations, so stripping it from
//   the install would leave the installed facade uncompilable. The
//   `IWYU pragma: private, include "aletheia/client.hpp"` line on the
//   facade directs IWYU-style tools to never suggest this file directly.
//
// Why not pImpl this away?
//   pImpl would let us hide everything in `src/detail/`, but it turns
//   every AletheiaClient method into a cross-TU call and blocks the
//   small-function inlining that keeps the hot extraction path
//   competitive with the Go and Python bindings. The tradeoff
//   chosen here: expose the types at compile time, document them as
//   off-limits, and rely on the WARNING above to deter direct use.

#include <aletheia/types.hpp>

#include <algorithm>
#include <compare>
#include <cstddef>
#include <cstdint>
#include <functional>
#include <span>
#include <string>
#include <tuple>
#include <utility>

namespace aletheia::detail {

// FrameKey identifies a unique (can id, dlc, payload) triple for the
// extraction cache. Ordering is lexicographic across all fields via the
// defaulted three-way comparison.
struct FrameKey {
    std::uint32_t id_value;
    bool is_extended;
    std::uint8_t dlc;
    FramePayload data;
    auto operator<=>(const FrameKey&) const = default;
};

// FrameKeyView is a non-owning counterpart to FrameKey used for
// heterogeneous cache lookup — the payload is referenced by span rather than
// copied into a FramePayload. This avoids the per-frame allocation of the
// payload vector on hot-path cache hits.
struct FrameKeyView {
    std::uint32_t id_value;
    bool is_extended;
    std::uint8_t dlc;
    std::span<const std::byte> data;
};

// Transparent comparator enabling std::map heterogeneous lookup with
// FrameKeyView. The is_transparent typedef opts the map into C++14's
// heterogeneous find(). It orders exactly as FrameKey's defaulted three-way
// comparison (a probe under probes/ checks the two agree): the scalar prefix
// first, then the payload bytes lexicographically.
struct FrameKeyLess {
    using is_transparent = void; // NOLINT(readability-identifier-naming) - STL protocol

    [[nodiscard]] static auto prefix(const FrameKey& k)
        -> std::tuple<std::uint32_t, bool, std::uint8_t> {
        return {k.id_value, k.is_extended, k.dlc};
    }
    [[nodiscard]] static auto prefix(const FrameKeyView& k)
        -> std::tuple<std::uint32_t, bool, std::uint8_t> {
        return {k.id_value, k.is_extended, k.dlc};
    }
    [[nodiscard]] static auto payload(const FrameKey& k) -> std::span<const std::byte> {
        return k.data;
    }
    [[nodiscard]] static auto payload(const FrameKeyView& k) -> std::span<const std::byte> {
        return k.data;
    }

    template<typename A, typename B>
    [[nodiscard]] auto operator()(const A& a, const B& b) const -> bool {
        auto const pa = prefix(a);
        auto const pb = prefix(b);
        if (pa != pb)
            return pa < pb;
        return std::ranges::lexicographical_compare(payload(a), payload(b));
    }
};

// SignalKey maps (can id, signal name) → signal index within the DBC
// message's signal list for the binary build/update FFI paths.
struct SignalKey {
    std::uint32_t id_value;
    bool is_extended;
    std::string signal_name;
    auto operator==(const SignalKey&) const -> bool = default;
};

// Folds one more hash into a seed (the usual golden-ratio mixing).
[[nodiscard]] inline auto hash_combine(std::size_t seed, std::size_t h) -> std::size_t {
    return seed ^ (h + 0x9e3779b9 + (seed << 6U) + (seed >> 2U));
}

struct SignalKeyHash {
    [[nodiscard]] auto operator()(const SignalKey& k) const -> std::size_t {
        auto h = std::hash<std::uint32_t>{}(k.id_value);
        h = hash_combine(h, std::hash<bool>{}(k.is_extended));
        return hash_combine(h, std::hash<std::string>{}(k.signal_name));
    }
};

// MessageKey is the (can id value, is_extended) pair used for the reverse
// index → signal name lookup populated in parse_dbc.
using MessageKey = std::pair<std::uint32_t, bool>;

struct MessageKeyHash {
    [[nodiscard]] auto operator()(const MessageKey& k) const -> std::size_t {
        return hash_combine(std::hash<std::uint32_t>{}(k.first), std::hash<bool>{}(k.second));
    }
};

} // namespace aletheia::detail
