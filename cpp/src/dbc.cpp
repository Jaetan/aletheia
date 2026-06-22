// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
// DbcMessage / DbcDefinition out-of-line query helpers.
#include <aletheia/dbc.hpp>

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <set>
#include <variant>
#include <vector>

namespace aletheia {

// ---------------------------------------------------------------------------
// DbcMessage helpers
// ---------------------------------------------------------------------------

auto DbcMessage::is_multiplexed() const -> bool {
    return std::ranges::any_of(
        signals, [](const auto& s) { return std::holds_alternative<Multiplexed>(s.presence); });
}

auto DbcMessage::always_present_signals() const -> std::vector<DbcSignal> {
    std::vector<DbcSignal> out;
    for (const auto& s : signals) {
        if (std::holds_alternative<AlwaysPresent>(s.presence)) {
            out.push_back(s);
        }
    }
    return out;
}

auto DbcMessage::multiplexed_signals() const -> std::vector<DbcSignal> {
    std::vector<DbcSignal> out;
    for (const auto& s : signals) {
        if (std::holds_alternative<Multiplexed>(s.presence)) {
            out.push_back(s);
        }
    }
    return out;
}

auto DbcMessage::multiplexor_names() const -> std::vector<SignalName> {
    std::set<SignalName> seen;
    std::vector<SignalName> out;
    for (const auto& s : signals) {
        if (const auto* m = std::get_if<Multiplexed>(&s.presence)) {
            if (seen.insert(m->multiplexor).second) {
                out.push_back(m->multiplexor);
            }
        }
    }
    return out;
}

auto DbcMessage::multiplex_values(const SignalName& multiplexor) const
    -> std::vector<MultiplexValue> {
    std::set<MultiplexValue> seen;
    std::vector<MultiplexValue> out;
    for (const auto& s : signals) {
        if (const auto* m = std::get_if<Multiplexed>(&s.presence);
            m != nullptr && m->multiplexor == multiplexor) {
            for (const auto& v : m->multiplex_values) {
                if (seen.insert(v).second) {
                    out.push_back(v);
                }
            }
        }
    }
    return out;
}

auto DbcMessage::signals_for_mux_value(const SignalName& multiplexor, MultiplexValue value) const
    -> std::vector<DbcSignal> {
    std::vector<DbcSignal> out;
    for (const auto& s : signals) {
        const bool is_always = std::holds_alternative<AlwaysPresent>(s.presence);
        const auto* m = std::get_if<Multiplexed>(&s.presence);
        if (is_always ||
            (m != nullptr && m->multiplexor == multiplexor &&
             std::ranges::find(m->multiplex_values, value) != m->multiplex_values.end())) {
            out.push_back(s);
        }
    }
    return out;
}

auto DbcMessage::signal_by_name(const SignalName& name) const -> const DbcSignal* {
    signal_index_cache.ensure([this](auto& map) {
        for (std::size_t i = 0; i < signals.size(); ++i) {
            map.emplace(signals[i].name.get(), i);
        }
    });
    auto idx = signal_index_cache.find(name.get());
    // A cached index is trusted only if the element there still matches the key.
    // The public `signals` vector may have been mutated since the cache was built
    // (shrunk, reordered, or replaced in place); a stale index could be OOB (UB)
    // or point at the wrong signal.  The bounds term short-circuits before the
    // name compare; either failure reads as not-found → nullptr.
    if (!idx || *idx >= signals.size() || signals[*idx].name.get() != name.get()) {
        return nullptr;
    }
    return &signals[*idx];
}

// ---------------------------------------------------------------------------
// DbcDefinition helpers
// ---------------------------------------------------------------------------

// Composite lookup key for the id index: the CAN id value plus the
// standard/extended discriminator in bit 32 (a standard and an extended frame
// may share a numeric id). Single source of truth for the cache build, the
// lookup, and the stale-index validation below.
static auto message_key(const CanId& id) -> std::uint64_t {
    return static_cast<std::uint64_t>(can_id_value(id)) |
           (can_id_is_extended(id) ? (1ULL << 32U) : 0);
}

auto DbcDefinition::message_by_id(const CanId& id) const -> const DbcMessage* {
    id_index_cache.ensure([this](auto& map) {
        for (std::size_t i = 0; i < messages.size(); ++i) {
            map.emplace(message_key(messages[i].id), i);
        }
    });
    const std::uint64_t key = message_key(id);
    auto idx = id_index_cache.find(key);
    // A cached index is trusted only if the message there still has the requested
    // id.  The public `messages` vector may have been mutated since the cache was
    // built (shrunk, reordered, or replaced in place); a stale index could be OOB
    // (UB) or point at the wrong message.  The bounds term short-circuits before
    // the key compare; either failure reads as not-found → nullptr.
    if (!idx || *idx >= messages.size() || message_key(messages[*idx].id) != key) {
        return nullptr;
    }
    return &messages[*idx];
}

auto DbcDefinition::message_by_name(const MessageName& name) const -> const DbcMessage* {
    name_index_cache.ensure([this](auto& map) {
        for (std::size_t i = 0; i < messages.size(); ++i) {
            map.emplace(messages[i].name.get(), i);
        }
    });
    auto idx = name_index_cache.find(name.get());
    // A cached index is trusted only if the message there still has the requested
    // name (the public `messages` vector may have been shrunk/reordered/replaced
    // since the cache was built).  The bounds term short-circuits before the name
    // compare; either failure reads as not-found → nullptr.
    if (!idx || *idx >= messages.size() || messages[*idx].name.get() != name.get()) {
        return nullptr;
    }
    return &messages[*idx];
}

} // namespace aletheia
