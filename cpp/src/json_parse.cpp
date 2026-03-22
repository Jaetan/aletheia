// JSON parsing: Agda core response strings → C++ types.
#include "detail/json.hpp"

#include <nlohmann/json.hpp>

#include <cstdint>

using json = nlohmann::json; // NOLINT(readability-identifier-naming)

namespace aletheia::detail {

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

static auto make_error(ErrorKind kind, std::string msg) -> AletheiaError {
    return {kind, std::move(msg)};
}

// Agda emits numbers as int, float, or {"numerator": n, "denominator": d}.
static auto parse_number(const json& j) -> double {
    if (j.is_number())
        return j.get<double>();
    if (j.is_object() && j.contains("numerator") && j.contains("denominator")) {
        auto num = j["numerator"].get<double>();
        auto den = j["denominator"].get<double>();
        return num / den;
    }
    return 0.0;
}

static auto parse_issue_code(const std::string& code) -> IssueCode {
    if (code == "duplicate_message_id")
        return IssueCode::DuplicateMessageId;
    if (code == "duplicate_message_name")
        return IssueCode::DuplicateMessageName;
    if (code == "duplicate_signal_name")
        return IssueCode::DuplicateSignalName;
    if (code == "factor_zero")
        return IssueCode::FactorZero;
    if (code == "multiplexor_not_found")
        return IssueCode::MultiplexorNotFound;
    if (code == "multiplexor_not_always_present")
        return IssueCode::MultiplexorNotAlwaysPresent;
    if (code == "global_name_collision")
        return IssueCode::GlobalNameCollision;
    if (code == "min_exceeds_max")
        return IssueCode::MinExceedsMax;
    if (code == "signal_exceeds_dlc")
        return IssueCode::SignalExceedsDlc;
    if (code == "signal_overlap")
        return IssueCode::SignalOverlap;
    if (code == "bit_length_zero")
        return IssueCode::BitLengthZero;
    if (code == "dlc_out_of_range")
        return IssueCode::DlcOutOfRange;
    if (code == "offset_scale_range")
        return IssueCode::OffsetScaleRange;
    if (code == "empty_message")
        return IssueCode::EmptyMessage;
    if (code == "start_bit_out_of_range")
        return IssueCode::StartBitOutOfRange;
    if (code == "bit_length_excessive")
        return IssueCode::BitLengthExcessive;
    return IssueCode::DuplicateMessageId; // fallback
}

static auto parse_rational_as_int(const json& j) -> std::int64_t {
    if (j.is_number_integer())
        return j.get<std::int64_t>();
    if (j.is_object() && j.contains("numerator") && j.contains("denominator")) {
        auto num = j["numerator"].get<std::int64_t>();
        auto den = j["denominator"].get<std::int64_t>();
        return num / den;
    }
    return 0;
}

// ---------------------------------------------------------------------------
// DBC parsing (for formatDBC response)
// ---------------------------------------------------------------------------

static auto parse_signal_def(const json& j) -> DbcSignal {
    auto bo_str = j.value("byteOrder", "little_endian");
    auto bo = (bo_str == "big_endian") ? ByteOrder::BigEndian : ByteOrder::LittleEndian;

    SignalPresence presence = AlwaysPresent{};
    if (j.contains("multiplexor")) {
        presence =
            Multiplexed{.multiplexor = SignalName{j["multiplexor"].get<std::string>()},
                        .mux_value = MultiplexValue{j["multiplex_value"].get<std::uint32_t>()}};
    }

    return DbcSignal{
        .name = SignalName{j["name"].get<std::string>()},
        .start_bit = BitPosition{j["startBit"].get<std::uint16_t>()},
        .bit_length = BitLength{j["length"].get<std::uint8_t>()},
        .byte_order = bo,
        .is_signed = j.value("signed", false),
        .factor = ScaleFactor{parse_number(j["factor"])},
        .offset = ScaleOffset{parse_number(j["offset"])},
        .minimum = PhysicalValue{parse_number(j["minimum"])},
        .maximum = PhysicalValue{parse_number(j["maximum"])},
        .unit = Unit{j.value("unit", "")},
        .presence = std::move(presence),
    };
}

static auto parse_message_def(const json& j) -> DbcMessage {
    auto id_val = j["id"].get<std::uint32_t>();
    const bool extended = j.value("extended", false);
    const CanId id = extended
                         ? CanId{ExtendedId::create(id_val).value()}
                         : CanId{StandardId::create(static_cast<std::uint16_t>(id_val)).value()};

    auto dlc = Dlc::create(j["dlc"].get<std::uint8_t>()).value();

    std::vector<DbcSignal> signals;
    for (const auto& s : j["signals"])
        signals.push_back(parse_signal_def(s));

    return DbcMessage{
        .id = id,
        .name = MessageName{j["name"].get<std::string>()},
        .dlc = dlc,
        .sender = NodeName{j.value("sender", "")},
        .signals = std::move(signals),
    };
}

static auto parse_dbc_definition(const json& j) -> DbcDefinition {
    std::vector<DbcMessage> messages;
    for (const auto& m : j["messages"])
        messages.push_back(parse_message_def(m));
    return DbcDefinition{
        .version = j.value("version", ""),
        .messages = std::move(messages),
    };
}

// ---------------------------------------------------------------------------
// Public parsing functions
// ---------------------------------------------------------------------------

auto parse_success(std::string_view input) -> Result<void> {
    auto j = json::parse(input);
    auto status = j.value("status", "");
    if (status == "success")
        return {};
    if (status == "error")
        return std::unexpected(
            make_error(ErrorKind::Protocol, j.value("message", "Unknown error")));
    return std::unexpected(make_error(ErrorKind::Protocol, "Unexpected status: " + status));
}

auto parse_validation(std::string_view input) -> Result<ValidationResult> {
    auto j = json::parse(input);
    auto status = j.value("status", "");
    if (status == "error")
        return std::unexpected(
            make_error(ErrorKind::Validation, j.value("message", "Unknown error")));
    if (status != "validation")
        return std::unexpected(make_error(ErrorKind::Protocol, "Expected validation response"));

    std::vector<ValidationIssue> issues;
    for (const auto& issue : j["issues"]) {
        auto sev_str = issue.value("severity", "error");
        auto severity = (sev_str == "warning") ? IssueSeverity::Warning : IssueSeverity::Error;
        issues.push_back({
            .severity = severity,
            .code = parse_issue_code(issue.value("code", "")),
            .detail = issue.value("detail", ""),
        });
    }
    return ValidationResult{
        .has_errors = j.value("has_errors", false),
        .issues = std::move(issues),
    };
}

auto parse_extraction(std::string_view input) -> Result<ExtractionResult> {
    auto j = json::parse(input);
    auto status = j.value("status", "");
    if (status == "error")
        return std::unexpected(
            make_error(ErrorKind::Protocol, j.value("message", "Unknown error")));

    std::vector<SignalValue> values;
    for (const auto& v : j.value("values", json::array()))
        values.push_back(
            {SignalName{v["name"].get<std::string>()}, PhysicalValue{parse_number(v["value"])}});

    std::vector<std::pair<SignalName, std::string>> errors;
    for (const auto& e : j.value("errors", json::array()))
        errors.emplace_back(SignalName{e["name"].get<std::string>()}, e.value("error", ""));

    std::vector<SignalName> absent;
    for (const auto& a : j.value("absent", json::array()))
        absent.emplace_back(a.get<std::string>());

    return ExtractionResult{
        .values = std::move(values),
        .errors = std::move(errors),
        .absent = std::move(absent),
    };
}

auto parse_frame_data(std::string_view input) -> Result<FramePayload> {
    auto j = json::parse(input);
    auto status = j.value("status", "");
    if (status == "error")
        return std::unexpected(
            make_error(ErrorKind::Protocol, j.value("message", "Unknown error")));

    const auto& data = j["data"];
    if (data.size() != 8)
        return std::unexpected(make_error(ErrorKind::Protocol, "Expected 8-byte frame data"));

    FramePayload payload{};
    for (std::size_t i = 0; i < 8; ++i)
        payload[i] = static_cast<std::byte>(data[i].get<std::uint8_t>());
    return payload;
}

auto parse_frame_response(std::string_view input) -> Result<FrameResponse> {
    auto j = json::parse(input);
    auto status = j.value("status", "");

    if (status == "ack")
        return FrameResponse{Ack{}};

    if (status == "violation") {
        auto idx = parse_rational_as_int(j["property_index"]);
        auto ts = parse_rational_as_int(j["timestamp"]);
        std::optional<std::string> reason;
        if (j.contains("reason") && j["reason"].is_string())
            reason = j["reason"].get<std::string>();
        return FrameResponse{Violation{
            .property_index = PropertyIndex{static_cast<std::size_t>(idx)},
            .timestamp = Timestamp{ts},
            .reason = std::move(reason),
        }};
    }

    if (status == "error")
        return std::unexpected(
            make_error(ErrorKind::Protocol, j.value("message", "Unknown error")));

    return std::unexpected(make_error(ErrorKind::Protocol, "Unexpected frame status: " + status));
}

auto parse_stream_result(std::string_view input) -> Result<StreamResult> {
    auto j = json::parse(input);
    auto status = j.value("status", "");

    if (status == "error")
        return std::unexpected(
            make_error(ErrorKind::Protocol, j.value("message", "Unknown error")));
    if (status != "complete")
        return std::unexpected(make_error(ErrorKind::Protocol, "Expected complete response"));

    std::vector<PropertyResult> results;
    for (const auto& r : j["results"]) {
        auto entry_status = r.value("status", "");
        auto verdict = (entry_status == "satisfaction") ? Verdict::Holds : Verdict::Fails;
        auto idx = parse_rational_as_int(r["property_index"]);

        std::optional<Timestamp> ts;
        if (r.contains("timestamp"))
            ts = Timestamp{parse_rational_as_int(r["timestamp"])};

        std::optional<std::string> reason;
        if (r.contains("reason") && r["reason"].is_string())
            reason = r["reason"].get<std::string>();

        results.push_back({
            .property_index = PropertyIndex{static_cast<std::size_t>(idx)},
            .verdict = verdict,
            .timestamp = ts,
            .reason = std::move(reason),
        });
    }
    return StreamResult{.results = std::move(results)};
}

auto parse_dbc_response(std::string_view input) -> Result<DbcDefinition> {
    auto j = json::parse(input);
    auto status = j.value("status", "");
    if (status == "error")
        return std::unexpected(
            make_error(ErrorKind::Protocol, j.value("message", "Unknown error")));
    if (!j.contains("dbc"))
        return std::unexpected(make_error(ErrorKind::Protocol, "Missing 'dbc' field in response"));
    return parse_dbc_definition(j["dbc"]);
}

} // namespace aletheia::detail
