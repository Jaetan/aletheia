// AletheiaClient — orchestrates backend + JSON serialization/parsing.
#include <aletheia/client.hpp>

#include "detail/json.hpp"

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
    return detail::parse_success(resp);
}

auto AletheiaClient::start_stream() -> Result<void> {
    auto cmd = detail::serialize_start_stream();
    auto resp = backend_->process(state_, cmd);
    return detail::parse_success(resp);
}

auto AletheiaClient::send_frame(Timestamp ts, CanId id, std::span<const std::byte, 8> data)
    -> Result<FrameResponse> {
    auto cmd = detail::serialize_send_frame(ts, id, data);
    auto resp = backend_->process(state_, cmd);
    return detail::parse_frame_response(resp);
}

auto AletheiaClient::end_stream() -> Result<StreamResult> {
    auto cmd = detail::serialize_end_stream();
    auto resp = backend_->process(state_, cmd);
    return detail::parse_stream_result(resp);
}

} // namespace aletheia
