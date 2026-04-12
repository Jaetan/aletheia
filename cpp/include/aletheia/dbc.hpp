// SPDX-License-Identifier: BSD-2-Clause
#pragma once

// DbcSignal/DbcMessage embed vocabulary types (SignalName, CanId, Dlc,
// NodeName, BitPosition, BitLength, ByteOrder, RationalFactor, ...), so
// callers that include dbc.hpp always need those symbols as well.
#include <aletheia/types.hpp> // IWYU pragma: export

#include <cstddef>
#include <optional>
#include <string>
#include <unordered_map>
#include <variant>
#include <vector>

namespace aletheia {

// ---------------------------------------------------------------------------
// Lazy mutable index — encapsulates the cache behind a private optional map.
// Public interface is const-safe: ensure() populates once, find() reads.
// ---------------------------------------------------------------------------

namespace detail {

template<typename Key, typename Hash = std::hash<Key>>
class LazyIndex {
public:
    /// Populate the index once via a builder callback: void(map&).
    template<typename Builder>
    void ensure(Builder&& build) const {
        if (cache_)
            return;
        cache_.emplace();
        build(*cache_);
    }

    /// Look up a key; returns std::nullopt if absent or not yet built.
    [[nodiscard]] auto find(const Key& key) const -> std::optional<std::size_t> {
        if (!cache_)
            return std::nullopt;
        auto it = cache_->find(key);
        return (it != cache_->end()) ? std::optional{it->second} : std::nullopt;
    }

private:
    mutable std::optional<std::unordered_map<Key, std::size_t, Hash>> cache_;
};

} // namespace detail

// ---------------------------------------------------------------------------
// Signal presence (always vs multiplexed)
// ---------------------------------------------------------------------------

struct AlwaysPresent {};

struct Multiplexed {
    SignalName multiplexor;
    std::vector<MultiplexValue> mux_values;
};

using SignalPresence = std::variant<AlwaysPresent, Multiplexed>;

// ---------------------------------------------------------------------------
// DBC signal definition
// ---------------------------------------------------------------------------

struct DbcSignal {
    SignalName name;
    BitPosition start_bit;
    BitLength bit_length;
    ByteOrder byte_order;
    bool is_signed;
    RationalFactor factor;
    RationalOffset offset;
    RationalBound minimum;
    RationalBound maximum;
    Unit unit;
    SignalPresence presence;
};

// ---------------------------------------------------------------------------
// DBC message definition
// ---------------------------------------------------------------------------

struct DbcMessage {
    CanId id;
    MessageName name;
    Dlc dlc;
    NodeName sender;
    std::vector<DbcSignal> signals;

    // --- Multiplexing query helpers (defined in dbc.cpp) ---

    [[nodiscard]] auto is_multiplexed() const -> bool;
    [[nodiscard]] auto always_present_signals() const -> std::vector<DbcSignal>;
    [[nodiscard]] auto multiplexed_signals() const -> std::vector<DbcSignal>;
    [[nodiscard]] auto multiplexor_names() const -> std::vector<SignalName>;
    [[nodiscard]] auto mux_values(const SignalName& multiplexor) const
        -> std::vector<MultiplexValue>;
    [[nodiscard]] auto signals_for_mux_value(const SignalName& multiplexor,
                                             MultiplexValue value) const -> std::vector<DbcSignal>;
    [[nodiscard]] auto signal_by_name(const SignalName& name) const -> const DbcSignal*;

    // Implementation detail — lazily populated by signal_by_name().
    // Mutable so const methods can populate the cache.  Trailing underscore
    // signals "internal, do not access directly".
    mutable detail::LazyIndex<std::string> signal_index_cache_;
};

// ---------------------------------------------------------------------------
// Complete DBC definition
// ---------------------------------------------------------------------------

struct DbcDefinition {
    std::string version; // plain string (not a domain identifier)
    std::vector<DbcMessage> messages;

    // --- Lookup helpers (defined in dbc.cpp) ---

    [[nodiscard]] auto message_by_id(const CanId& id) const -> const DbcMessage*;
    [[nodiscard]] auto message_by_name(const MessageName& name) const -> const DbcMessage*;

    // Implementation detail — lazily populated by message_by_id/name().
    mutable detail::LazyIndex<std::string> name_index_cache_;
    mutable detail::LazyIndex<std::uint64_t> id_index_cache_;
};

} // namespace aletheia
