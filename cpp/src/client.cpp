// AletheiaClient — orchestrates backend + JSON serialization/parsing.
#include <aletheia/client.hpp>
#include <aletheia/enrich.hpp>

#include "detail/json.hpp"

#include <format>
#include <string>

namespace aletheia {

AletheiaClient::AletheiaClient(std::unique_ptr<IBackend> backend)
    : backend_(std::move(backend))
    , state_(backend_->init()) {
}

AletheiaClient::~AletheiaClient() {
    if (backend_ != nullptr && state_ != nullptr)
        backend_->close(state_);
}

AletheiaClient::AletheiaClient(AletheiaClient&& other) noexcept
    : backend_(std::move(other.backend_))
    , state_(std::exchange(other.state_, nullptr)) {
}

AletheiaClient& AletheiaClient::operator=(AletheiaClient&& other) noexcept {
    if (this != &other) {
        if (backend_ != nullptr && state_ != nullptr)
            backend_->close(state_);
        backend_ = std::move(other.backend_);
        state_ = std::exchange(other.state_, nullptr);
    }
    return *this;
}

// ---------------------------------------------------------------------------
// DBC
// ---------------------------------------------------------------------------

auto AletheiaClient::parse_dbc(const DbcDefinition& dbc) -> Result<void> {
    auto cmd = detail::serialize_parse_dbc(dbc);
    auto resp = backend_->process(state_, cmd);
    return detail::parse_success(resp);
}

auto AletheiaClient::validate_dbc(const DbcDefinition& dbc) -> Result<ValidationResult> {
    auto cmd = detail::serialize_validate_dbc(dbc);
    auto resp = backend_->process(state_, cmd);
    return detail::parse_validation(resp);
}

auto AletheiaClient::format_dbc() -> Result<DbcDefinition> {
    auto cmd = detail::serialize_format_dbc();
    auto resp = backend_->process(state_, cmd);
    return detail::parse_dbc_response(resp);
}

// ---------------------------------------------------------------------------
// Signals
// ---------------------------------------------------------------------------

auto AletheiaClient::extract_signals(CanId id, std::span<const std::byte, 8> data)
    -> Result<ExtractionResult> {
    auto cmd = detail::serialize_extract_signals(id, data);
    auto resp = backend_->process(state_, cmd);
    return detail::parse_extraction(resp);
}

auto AletheiaClient::build_frame(CanId id, std::span<const SignalValue> signals)
    -> Result<FramePayload> {
    auto cmd = detail::serialize_build_frame(id, signals);
    auto resp = backend_->process(state_, cmd);
    return detail::parse_frame_data(resp);
}

auto AletheiaClient::update_frame(CanId id, std::span<const std::byte, 8> data,
                                  std::span<const SignalValue> signals) -> Result<FramePayload> {
    auto cmd = detail::serialize_update_frame(id, data, signals);
    auto resp = backend_->process(state_, cmd);
    return detail::parse_frame_data(resp);
}

// ---------------------------------------------------------------------------
// Streaming
// ---------------------------------------------------------------------------

auto AletheiaClient::set_properties(std::span<const LtlFormula> properties) -> Result<void> {
    auto cmd = detail::serialize_set_properties(properties);
    auto resp = backend_->process(state_, cmd);
    auto result = detail::parse_success(resp);
    if (!result.has_value())
        return result;
    diags_.clear();
    diags_.reserve(properties.size());
    for (const auto& f : properties)
        diags_.push_back(build_diagnostic(f));
    cache_.clear();
    return result;
}

auto AletheiaClient::start_stream() -> Result<void> {
    auto cmd = detail::serialize_start_stream();
    auto resp = backend_->process(state_, cmd);
    auto result = detail::parse_success(resp);
    if (result.has_value())
        cache_.clear();
    return result;
}

auto AletheiaClient::send_frame(Timestamp ts, CanId id, std::span<const std::byte, 8> data)
    -> Result<FrameResponse> {
    auto cmd = detail::serialize_send_frame(ts, id, data);
    auto resp = backend_->process(state_, cmd);
    auto result = detail::parse_frame_response(resp);
    if (result.has_value()) {
        if (auto* v = std::get_if<Violation>(&*result); v != nullptr && !diags_.empty())
            enrich_violation(*v, id, data);
    }
    return result;
}

auto AletheiaClient::end_stream() -> Result<StreamResult> {
    auto cmd = detail::serialize_end_stream();
    auto resp = backend_->process(state_, cmd);
    auto result = detail::parse_stream_result(resp);
    if (result.has_value() && !diags_.empty()) {
        for (auto& pr : result->results) {
            if (pr.verdict == Verdict::Fails)
                enrich_property_result(pr);
        }
    }
    return result;
}

// ---------------------------------------------------------------------------
// Enrichment internals
// ---------------------------------------------------------------------------

void AletheiaClient::enrich_violation(Violation& v, CanId id,
                                      std::span<const std::byte, 8> data) {
    auto idx = v.property_index.get();
    if (idx >= diags_.size())
        return;
    const auto& diag = diags_[idx];
    auto values = extract_signal_values(diag, id, data);
    std::string reason;
    if (values.empty()) {
        reason = "violated: " + diag.formula_desc;
    } else {
        bool first = true;
        for (const auto& sig : diag.signals) {
            if (auto it = values.find(sig); it != values.end()) {
                if (!first)
                    reason += ", ";
                reason += std::format("{} = {:g}", std::string_view{sig}, it->second.get());
                first = false;
            }
        }
        if (first) {
            reason = "violated: " + diag.formula_desc;
        } else {
            reason += " (formula: " + diag.formula_desc + ")";
        }
    }
    v.enrichment = ViolationEnrichment{
        .signals = std::move(values),
        .formula_desc = diag.formula_desc,
        .enriched_reason = std::move(reason),
    };
}

void AletheiaClient::enrich_property_result(PropertyResult& pr) {
    auto idx = pr.property_index.get();
    if (idx >= diags_.size())
        return;
    const auto& diag = diags_[idx];
    pr.enrichment = ViolationEnrichment{
        .signals = {},
        .formula_desc = diag.formula_desc,
        .enriched_reason = "violated: " + diag.formula_desc,
    };
}

auto AletheiaClient::extract_signal_values(const PropertyDiagnostic& diag, CanId id,
                                           std::span<const std::byte, 8> data)
    -> std::map<SignalName, PhysicalValue> {
    auto id_value = std::visit([](const auto& v) -> std::uint32_t { return v.value(); }, id);
    auto is_extended = std::holds_alternative<ExtendedId>(id);
    FramePayload payload{};
    std::copy_n(data.begin(), 8, payload.begin());
    FrameKey key{.id_value = id_value, .is_extended = is_extended, .data = payload};

    auto cache_it = cache_.find(key);
    if (cache_it == cache_.end()) {
        auto extraction = extract_signals_internal(id, data);
        if (!extraction.has_value())
            return {};
        if (cache_.size() < max_cache_size_)
            cache_it = cache_.emplace(key, std::move(*extraction)).first;
        else {
            // Over capacity — use result directly without caching
            std::map<SignalName, PhysicalValue> values;
            for (const auto& sig : diag.signals) {
                for (const auto& sv : extraction->values) {
                    if (sv.name == sig) {
                        values.emplace(sig, sv.value);
                        break;
                    }
                }
            }
            return values;
        }
    }

    std::map<SignalName, PhysicalValue> values;
    for (const auto& sig : diag.signals) {
        for (const auto& sv : cache_it->second.values) {
            if (sv.name == sig) {
                values.emplace(sig, sv.value);
                break;
            }
        }
    }
    return values;
}

auto AletheiaClient::extract_signals_internal(CanId id, std::span<const std::byte, 8> data)
    -> std::optional<ExtractionResult> {
    auto cmd = detail::serialize_extract_signals(id, data);
    auto resp = backend_->process(state_, cmd);
    auto result = detail::parse_extraction(resp);
    if (!result.has_value())
        return std::nullopt;
    return std::move(*result);
}

} // namespace aletheia
