// SPDX-License-Identifier: BSD-2-Clause
#pragma once

#include <aletheia/types.hpp>

#include <algorithm>
#include <set>
#include <string>
#include <unordered_map>
#include <variant>
#include <vector>

namespace aletheia {

// ---------------------------------------------------------------------------
// Signal presence (always vs multiplexed)
// ---------------------------------------------------------------------------

struct AlwaysPresent {};

struct Multiplexed {
    SignalName multiplexor;
    MultiplexValue mux_value;
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

    // --- Multiplexing query helpers ---

    /// True if the message contains any multiplexed signals.
    [[nodiscard]] auto is_multiplexed() const -> bool {
        return std::ranges::any_of(
            signals, [](const auto& s) { return std::holds_alternative<Multiplexed>(s.presence); });
    }

    /// Signals that are present in every frame (not multiplexed).
    [[nodiscard]] auto always_present_signals() const -> std::vector<DbcSignal> {
        std::vector<DbcSignal> out;
        for (const auto& s : signals)
            if (std::holds_alternative<AlwaysPresent>(s.presence))
                out.push_back(s);
        return out;
    }

    /// Signals that are conditionally present (multiplexed).
    [[nodiscard]] auto multiplexed_signals() const -> std::vector<DbcSignal> {
        std::vector<DbcSignal> out;
        for (const auto& s : signals)
            if (std::holds_alternative<Multiplexed>(s.presence))
                out.push_back(s);
        return out;
    }

    /// Distinct multiplexor signal names referenced by multiplexed signals,
    /// in order of first occurrence.
    [[nodiscard]] auto multiplexor_names() const -> std::vector<SignalName> {
        std::set<SignalName> seen;
        std::vector<SignalName> out;
        for (const auto& s : signals) {
            if (const auto* m = std::get_if<Multiplexed>(&s.presence)) {
                if (seen.insert(m->multiplexor).second)
                    out.push_back(m->multiplexor);
            }
        }
        return out;
    }

    /// All multiplex values for the given multiplexor, in order of first occurrence.
    [[nodiscard]] auto mux_values(const SignalName& multiplexor) const
        -> std::vector<MultiplexValue> {
        std::set<MultiplexValue> seen;
        std::vector<MultiplexValue> out;
        for (const auto& s : signals) {
            if (const auto* m = std::get_if<Multiplexed>(&s.presence);
                m != nullptr && m->multiplexor == multiplexor) {
                if (seen.insert(m->mux_value).second)
                    out.push_back(m->mux_value);
            }
        }
        return out;
    }

    /// Signals present when the given multiplexor has the given value.
    /// Includes all always-present signals plus matching multiplexed signals.
    [[nodiscard]] auto signals_for_mux_value(const SignalName& multiplexor,
                                             MultiplexValue value) const -> std::vector<DbcSignal> {
        std::vector<DbcSignal> out;
        for (const auto& s : signals) {
            const bool dominated = std::holds_alternative<AlwaysPresent>(s.presence);
            const auto* m = std::get_if<Multiplexed>(&s.presence);
            if (dominated ||
                (m != nullptr && m->multiplexor == multiplexor && m->mux_value == value))
                out.push_back(s);
        }
        return out;
    }

    /// First signal with the given name, or nullptr if not found.
    /// Returns a pointer into the signals vector.
    [[nodiscard]] auto signal_by_name(const SignalName& name) const -> const DbcSignal* {
        ensure_signal_index();
        auto it = signal_idx.find(name.get());
        if (it == signal_idx.end())
            return nullptr;
        return &signals[it->second];
    }

    // Lazy index — mutable to preserve aggregate initialization.
    mutable bool signal_indexed = false;
    mutable std::unordered_map<std::string, std::size_t> signal_idx;
    void ensure_signal_index() const {
        if (signal_indexed)
            return;
        for (std::size_t i = 0; i < signals.size(); ++i)
            signal_idx.emplace(signals[i].name.get(), i);
        signal_indexed = true;
    }
};

// ---------------------------------------------------------------------------
// Complete DBC definition
// ---------------------------------------------------------------------------

struct DbcDefinition {
    std::string version; // plain string (not a domain identifier)
    std::vector<DbcMessage> messages;

    /// First message with the given CAN ID, or nullptr if not found.
    /// Returns a pointer into the messages vector.
    [[nodiscard]] auto message_by_id(const CanId& id) const -> const DbcMessage* {
        ensure_id_index();
        auto id_value = std::visit([](const auto& v) -> std::uint32_t { return v.value(); }, id);
        auto ext = std::holds_alternative<ExtendedId>(id);
        const std::uint64_t key = static_cast<std::uint64_t>(id_value) | (ext ? (1ULL << 32U) : 0);
        auto it = id_idx.find(key);
        if (it == id_idx.end())
            return nullptr;
        return &messages[it->second];
    }

    /// First message with the given name, or nullptr if not found.
    /// Returns a pointer into the messages vector.
    [[nodiscard]] auto message_by_name(const MessageName& name) const -> const DbcMessage* {
        ensure_name_index();
        auto it = name_idx.find(name.get());
        if (it == name_idx.end())
            return nullptr;
        return &messages[it->second];
    }

    // Lazy indexes — mutable to preserve aggregate initialization.
    mutable bool name_indexed = false;
    mutable std::unordered_map<std::string, std::size_t> name_idx;
    mutable bool id_indexed = false;
    mutable std::unordered_map<std::uint64_t, std::size_t> id_idx;
    void ensure_name_index() const {
        if (name_indexed)
            return;
        for (std::size_t i = 0; i < messages.size(); ++i)
            name_idx.emplace(messages[i].name.get(), i);
        name_indexed = true;
    }
    void ensure_id_index() const {
        if (id_indexed)
            return;
        for (std::size_t i = 0; i < messages.size(); ++i) {
            auto val = std::visit([](const auto& v) -> std::uint32_t { return v.value(); },
                                  messages[i].id);
            auto ext = std::holds_alternative<ExtendedId>(messages[i].id);
            const std::uint64_t key = static_cast<std::uint64_t>(val) | (ext ? (1ULL << 32U) : 0);
            id_idx.emplace(key, i);
        }
        id_indexed = true;
    }
};

} // namespace aletheia
