// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
// DbcMessage / DbcDefinition out-of-line query helpers.
#include <aletheia/dbc.hpp>

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <iterator>
#include <optional>
#include <set>
#include <variant>
#include <vector>

namespace aletheia {

// The signals of a message that satisfy a predicate, copied out in order.
// Written as a copy rather than as a `views::filter | ranges::to` pipe: the
// pipe form of ranges::to only works from a libstdc++ point release newer
// than the one the build's own CI pins, and the break shows up nowhere but
// there, on a machine whose standard library is older than the developer's.
static auto signals_where(const std::vector<DbcSignal>& signals, auto pred)
    -> std::vector<DbcSignal> {
    std::vector<DbcSignal> out;
    std::ranges::copy_if(signals, std::back_inserter(out), pred);
    return out;
}

static auto is_always_present(const DbcSignal& s) -> bool {
    return std::holds_alternative<AlwaysPresent>(s.presence);
}

static auto is_multiplexed_signal(const DbcSignal& s) -> bool {
    return std::holds_alternative<Multiplexed>(s.presence);
}

// The element a lazily built index points at, trusted only if it still
// matches the key. The public vectors may have been shrunk, reordered or
// replaced in place since the index was built, so a stale index could be out
// of bounds or name the wrong element; either failure reads as not found.
template<typename Item, typename Matches>
static auto cached_element(std::optional<std::size_t> idx, const std::vector<Item>& items,
                           Matches matches) -> const Item* {
    if (!idx || *idx >= items.size() || !matches(items[*idx]))
        return nullptr;
    return &items[*idx];
}

// ---------------------------------------------------------------------------
// DbcMessage helpers
// ---------------------------------------------------------------------------

auto DbcMessage::is_multiplexed() const -> bool {
    return std::ranges::any_of(signals, is_multiplexed_signal);
}

auto DbcMessage::always_present_signals() const -> std::vector<DbcSignal> {
    return signals_where(signals, is_always_present);
}

auto DbcMessage::multiplexed_signals() const -> std::vector<DbcSignal> {
    return signals_where(signals, is_multiplexed_signal);
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
    return signals_where(signals, [&](const DbcSignal& s) {
        const auto* m = std::get_if<Multiplexed>(&s.presence);
        return is_always_present(s) || (m != nullptr && m->multiplexor == multiplexor &&
                                        std::ranges::contains(m->multiplex_values, value));
    });
}

auto DbcMessage::signal_by_name(const SignalName& name) const -> const DbcSignal* {
    signal_index_cache.ensure([this](auto& map) {
        for (std::size_t i = 0; i < signals.size(); ++i) {
            map.emplace(signals[i].name.get(), i);
        }
    });
    return cached_element(signal_index_cache.find(name.get()), signals,
                          [&](const DbcSignal& s) { return s.name == name; });
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
    return cached_element(id_index_cache.find(key), messages,
                          [&](const DbcMessage& m) { return message_key(m.id) == key; });
}

auto DbcDefinition::message_by_name(const MessageName& name) const -> const DbcMessage* {
    name_index_cache.ensure([this](auto& map) {
        for (std::size_t i = 0; i < messages.size(); ++i) {
            map.emplace(messages[i].name.get(), i);
        }
    });
    return cached_element(name_index_cache.find(name.get()), messages,
                          [&](const DbcMessage& m) { return m.name == name; });
}

} // namespace aletheia
