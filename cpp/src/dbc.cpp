// DbcMessage / DbcDefinition out-of-line query helpers.
#include <aletheia/dbc.hpp>

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <set>
#include <string>
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

auto DbcMessage::mux_values(const SignalName& multiplexor) const -> std::vector<MultiplexValue> {
    std::set<MultiplexValue> seen;
    std::vector<MultiplexValue> out;
    for (const auto& s : signals) {
        if (const auto* m = std::get_if<Multiplexed>(&s.presence);
            m != nullptr && m->multiplexor == multiplexor) {
            for (const auto& v : m->mux_values) {
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
        if (is_always || (m != nullptr && m->multiplexor == multiplexor &&
                          std::ranges::find(m->mux_values, value) != m->mux_values.end())) {
            out.push_back(s);
        }
    }
    return out;
}

auto DbcMessage::signal_by_name(const SignalName& target) const -> const DbcSignal* {
    signal_index_cache_.ensure([this](auto& map) {
        for (std::size_t i = 0; i < signals.size(); ++i) {
            map.emplace(signals[i].name.get(), i);
        }
    });
    auto idx = signal_index_cache_.find(target.get());
    if (!idx) {
        return nullptr;
    }
    return &signals[*idx];
}

// ---------------------------------------------------------------------------
// DbcDefinition helpers
// ---------------------------------------------------------------------------

auto DbcDefinition::message_by_id(const CanId& id) const -> const DbcMessage* {
    id_index_cache_.ensure([this](auto& map) {
        for (std::size_t i = 0; i < messages.size(); ++i) {
            auto val = std::visit([](const auto& v) -> std::uint32_t { return v.value(); },
                                  messages[i].id);
            auto ext = std::holds_alternative<ExtendedId>(messages[i].id);
            const std::uint64_t key = static_cast<std::uint64_t>(val) | (ext ? (1ULL << 32U) : 0);
            map.emplace(key, i);
        }
    });
    auto id_value = std::visit([](const auto& v) -> std::uint32_t { return v.value(); }, id);
    auto ext = std::holds_alternative<ExtendedId>(id);
    const std::uint64_t key = static_cast<std::uint64_t>(id_value) | (ext ? (1ULL << 32U) : 0);
    auto idx = id_index_cache_.find(key);
    if (!idx) {
        return nullptr;
    }
    return &messages[*idx];
}

auto DbcDefinition::message_by_name(const MessageName& target) const -> const DbcMessage* {
    name_index_cache_.ensure([this](auto& map) {
        for (std::size_t i = 0; i < messages.size(); ++i) {
            map.emplace(messages[i].name.get(), i);
        }
    });
    auto idx = name_index_cache_.find(target.get());
    if (!idx) {
        return nullptr;
    }
    return &messages[*idx];
}

} // namespace aletheia
