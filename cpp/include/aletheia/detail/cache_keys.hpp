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
//   competitive with Go/Python (~109k fps Stream LTL). The tradeoff
//   chosen here: expose the types at compile time, document them as
//   off-limits, and rely on the WARNING above to deter direct use.

#include <aletheia/types.hpp>

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
// heterogeneous find().
struct FrameKeyLess {
    using is_transparent = void; // NOLINT(readability-identifier-naming) - STL protocol

    static auto tie(const FrameKey& k)
        -> std::tuple<std::uint32_t, bool, std::uint8_t, std::span<const std::byte>> {
        return {k.id_value, k.is_extended, k.dlc,
                std::span<const std::byte>{k.data.data(), k.data.size()}};
    }

    static auto tie(const FrameKeyView& k)
        -> std::tuple<std::uint32_t, bool, std::uint8_t, std::span<const std::byte>> {
        return {k.id_value, k.is_extended, k.dlc, k.data};
    }

    template<typename A, typename B>
    auto operator()(const A& a, const B& b) const -> bool {
        const auto ta = tie(a);
        const auto tb = tie(b);
        if (std::get<0>(ta) != std::get<0>(tb))
            return std::get<0>(ta) < std::get<0>(tb);
        if (std::get<1>(ta) != std::get<1>(tb))
            return std::get<1>(ta) < std::get<1>(tb);
        if (std::get<2>(ta) != std::get<2>(tb))
            return std::get<2>(ta) < std::get<2>(tb);
        const auto& da = std::get<3>(ta);
        const auto& db = std::get<3>(tb);
        const auto n = std::min(da.size(), db.size());
        for (std::size_t i = 0; i < n; ++i) {
            if (da[i] != db[i])
                return da[i] < db[i];
        }
        return da.size() < db.size();
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

struct SignalKeyHash {
    auto operator()(const SignalKey& k) const -> std::size_t {
        auto h1 = std::hash<std::uint32_t>{}(k.id_value);
        auto h2 = std::hash<bool>{}(k.is_extended);
        auto h3 = std::hash<std::string>{}(k.signal_name);
        h1 ^= h2 + 0x9e3779b9 + (h1 << 6U) + (h1 >> 2U);
        h1 ^= h3 + 0x9e3779b9 + (h1 << 6U) + (h1 >> 2U);
        return h1;
    }
};

// MessageKey is the (can id value, is_extended) pair used for the reverse
// index → signal name lookup populated in parse_dbc.
using MessageKey = std::pair<std::uint32_t, bool>;

struct MessageKeyHash {
    auto operator()(const MessageKey& k) const -> std::size_t {
        auto h = std::hash<std::uint32_t>{}(k.first);
        h ^= std::hash<bool>{}(k.second) + 0x9e3779b9 + (h << 6U) + (h >> 2U);
        return h;
    }
};

} // namespace aletheia::detail
