// JSON parsing: Agda core response strings → C++ types.
#include "detail/json.hpp"

#include <nlohmann/json.hpp>

#include <cstdint>
#include <limits>
#include <stdexcept>
#include <string>

using json = nlohmann::json; // NOLINT(readability-identifier-naming)

namespace aletheia::detail {

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

static auto make_error(ErrorKind kind, std::string msg) -> AletheiaError {
    return {kind, std::move(msg)};
}

// Agda emits numbers as int, float, or {"numerator": n, "denominator": d}.
// Throws on unrecognized formats; callers catch at the public API boundary.
static auto parse_number(const json& j) -> double {
    if (j.is_number())
        return j.get<double>();
    if (j.is_object() && j.contains("numerator") && j.contains("denominator")) {
        auto num = j.at("numerator").get<double>();
        auto den = j.at("denominator").get<double>();
        if (den == 0.0)
            throw std::runtime_error("Zero denominator in rational: " + j.dump());
        return num / den;
    }
    throw std::runtime_error("Expected number or {numerator, denominator}, got: " + j.dump());
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
    return IssueCode::Unknown;
}

static auto parse_rational_as_int(const json& j) -> std::int64_t {
    if (j.is_number_integer())
        return j.get<std::int64_t>();
    if (j.is_object() && j.contains("numerator") && j.contains("denominator")) {
        auto num = j.at("numerator").get<std::int64_t>();
        auto den = j.at("denominator").get<std::int64_t>();
        if (den == 0)
            throw std::runtime_error("Zero denominator in rational: " + j.dump());
        if (num % den != 0)
            throw std::runtime_error("Non-exact rational in integer field: " + j.dump());
        return num / den;
    }
    throw std::runtime_error("Expected integer or {numerator, denominator}, got: " + j.dump());
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
            Multiplexed{.multiplexor = SignalName{j.at("multiplexor").get<std::string>()},
                        .mux_value = MultiplexValue{j.at("multiplex_value").get<std::uint32_t>()}};
    }

    return DbcSignal{
        .name = SignalName{j.at("name").get<std::string>()},
        .start_bit = BitPosition{j.at("startBit").get<std::uint16_t>()},
        .bit_length = BitLength{j.at("length").get<std::uint8_t>()},
        .byte_order = bo,
        .is_signed = j.value("signed", false),
        .factor = ScaleFactor{parse_number(j.at("factor"))},
        .offset = ScaleOffset{parse_number(j.at("offset"))},
        .minimum = PhysicalValue{parse_number(j.at("minimum"))},
        .maximum = PhysicalValue{parse_number(j.at("maximum"))},
        .unit = Unit{j.value("unit", "")},
        .presence = std::move(presence),
    };
}

static auto parse_message_def(const json& j) -> DbcMessage {
    auto id_val = j.at("id").get<std::uint32_t>();
    const bool extended = j.value("extended", false);

    const CanId id = [&]() -> CanId {
        if (extended) {
            auto result = ExtendedId::create(id_val);
            if (!result)
                throw std::runtime_error("Invalid extended CAN ID " + std::to_string(id_val) +
                                         ": " + result.error());
            return CanId{*result};
        }
        if (id_val > std::numeric_limits<std::uint16_t>::max())
            throw std::runtime_error("Standard CAN ID value " + std::to_string(id_val) +
                                     " exceeds uint16 range");
        auto result = StandardId::create(static_cast<std::uint16_t>(id_val));
        if (!result)
            throw std::runtime_error("Invalid standard CAN ID " + std::to_string(id_val) + ": " +
                                     result.error());
        return CanId{*result};
    }();

    auto dlc_result = bytes_to_dlc(j.at("dlc").get<std::size_t>());
    if (!dlc_result)
        throw std::runtime_error("Invalid DLC: " + dlc_result.error());

    std::vector<DbcSignal> signals;
    for (const auto& s : j.at("signals"))
        signals.push_back(parse_signal_def(s));

    return DbcMessage{
        .id = id,
        .name = MessageName{j.at("name").get<std::string>()},
        .dlc = *dlc_result,
        .sender = NodeName{j.value("sender", "")},
        .signals = std::move(signals),
    };
}

static auto parse_dbc_definition(const json& j) -> DbcDefinition {
    std::vector<DbcMessage> messages;
    for (const auto& m : j.at("messages"))
        messages.push_back(parse_message_def(m));
    return DbcDefinition{
        .version = j.value("version", ""),
        .messages = std::move(messages),
    };
}

// ---------------------------------------------------------------------------
// Public parsing functions
//
// Each function catches exceptions from JSON access and validated-type
// construction, converting them to Result<> errors at the public boundary.
// ---------------------------------------------------------------------------

auto parse_success(std::string_view input) -> Result<void> {
    try {
        auto j = json::parse(input);
        auto status = j.value("status", "");
        if (status == "success")
            return {};
        if (status == "error")
            return std::unexpected(
                make_error(ErrorKind::Protocol, j.value("message", "Unknown error")));
        return std::unexpected(make_error(ErrorKind::Protocol, "Unexpected status: " + status));
    } catch (const std::exception& e) {
        return std::unexpected(make_error(ErrorKind::Protocol, e.what()));
    }
}

auto parse_validation(std::string_view input) -> Result<ValidationResult> {
    try {
        auto j = json::parse(input);
        auto status = j.value("status", "");
        if (status == "error")
            return std::unexpected(
                make_error(ErrorKind::Validation, j.value("message", "Unknown error")));
        if (status != "validation")
            return std::unexpected(make_error(ErrorKind::Protocol, "Expected validation response"));

        std::vector<ValidationIssue> issues;
        for (const auto& issue : j.at("issues")) {
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
    } catch (const std::exception& e) {
        return std::unexpected(make_error(ErrorKind::Protocol, e.what()));
    }
}

auto parse_extraction(std::string_view input) -> Result<ExtractionResult> {
    try {
        auto j = json::parse(input);
        auto status = j.value("status", "");
        if (status == "error")
            return std::unexpected(
                make_error(ErrorKind::Protocol, j.value("message", "Unknown error")));
        if (status != "success")
            return std::unexpected(
                make_error(ErrorKind::Protocol, "Unexpected extraction status: " + status));

        std::vector<SignalValue> values;
        for (const auto& v : j.value("values", json::array()))
            values.push_back({SignalName{v.at("name").get<std::string>()},
                              PhysicalValue{parse_number(v.at("value"))}});

        std::vector<std::pair<SignalName, std::string>> errors;
        for (const auto& e : j.value("errors", json::array()))
            errors.emplace_back(SignalName{e.at("name").get<std::string>()}, e.value("error", ""));

        std::vector<SignalName> absent;
        for (const auto& a : j.value("absent", json::array()))
            absent.emplace_back(a.get<std::string>());

        return ExtractionResult{
            .values = std::move(values),
            .errors = std::move(errors),
            .absent = std::move(absent),
        };
    } catch (const std::exception& e) {
        return std::unexpected(make_error(ErrorKind::Protocol, e.what()));
    }
}

auto parse_frame_data(std::string_view input) -> Result<FramePayload> {
    try {
        auto j = json::parse(input);
        auto status = j.value("status", "");
        if (status == "error")
            return std::unexpected(
                make_error(ErrorKind::Protocol, j.value("message", "Unknown error")));
        if (status != "success")
            return std::unexpected(
                make_error(ErrorKind::Protocol, "Unexpected frame data status: " + status));

        const auto& data = j.at("data");
        FramePayload payload;
        payload.reserve(data.size());
        for (const auto& byte_val : data)
            payload.push_back(static_cast<std::byte>(byte_val.get<std::uint8_t>()));
        return payload;
    } catch (const std::exception& e) {
        return std::unexpected(make_error(ErrorKind::Protocol, e.what()));
    }
}

auto parse_frame_response(std::string_view input) -> Result<FrameResponse> {
    // Fast path: byte-level check for the common ack response.
    // Avoids full JSON parsing for ~99% of streaming frames.
    static constexpr std::string_view ack_compact = R"({"status":"ack"})";
    static constexpr std::string_view ack_spaced = R"({"status": "ack"})";
    if (input == ack_compact || input == ack_spaced)
        return FrameResponse{Ack{}};

    try {
        auto j = json::parse(input);
        auto status = j.value("status", "");

        if (status == "ack")
            return FrameResponse{Ack{}};

        if (status == "fails") {
            auto idx = parse_rational_as_int(j.at("property_index"));
            if (idx < 0)
                throw std::runtime_error("Negative property_index: " + std::to_string(idx));
            auto ts = parse_rational_as_int(j.at("timestamp"));
            if (ts < 0)
                throw std::runtime_error("Negative timestamp: " + std::to_string(ts));
            std::string reason;
            if (j.contains("reason") && j.at("reason").is_string())
                reason = j.at("reason").get<std::string>();
            return FrameResponse{Violation{
                .property_index = PropertyIndex{static_cast<std::size_t>(idx)},
                .timestamp = Timestamp{ts},
                .reason = std::move(reason),
            }};
        }

        if (status == "error")
            return std::unexpected(
                make_error(ErrorKind::Protocol, j.value("message", "Unknown error")));

        return std::unexpected(
            make_error(ErrorKind::Protocol, "Unexpected frame status: " + status));
    } catch (const std::exception& e) {
        return std::unexpected(make_error(ErrorKind::Protocol, e.what()));
    }
}

auto parse_stream_result(std::string_view input) -> Result<StreamResult> {
    try {
        auto j = json::parse(input);
        auto status = j.value("status", "");

        if (status == "error")
            return std::unexpected(
                make_error(ErrorKind::Protocol, j.value("message", "Unknown error")));
        if (status != "complete")
            return std::unexpected(make_error(ErrorKind::Protocol, "Expected complete response"));

        std::vector<PropertyResult> results;
        for (const auto& r : j.at("results")) {
            auto entry_status = r.value("status", "");
            Verdict verdict{};
            if (entry_status == "holds")
                verdict = Verdict::Holds;
            else if (entry_status == "fails")
                verdict = Verdict::Fails;
            else
                throw std::runtime_error("Unknown verdict status: " + entry_status);
            auto idx = parse_rational_as_int(r.at("property_index"));
            if (idx < 0)
                throw std::runtime_error("Negative property_index: " + std::to_string(idx));

            std::optional<Timestamp> ts;
            if (r.contains("timestamp")) {
                auto ts_val = parse_rational_as_int(r.at("timestamp"));
                if (ts_val < 0)
                    throw std::runtime_error("Negative timestamp: " + std::to_string(ts_val));
                ts = Timestamp{ts_val};
            }

            std::string reason;
            if (r.contains("reason") && r.at("reason").is_string())
                reason = r.at("reason").get<std::string>();

            results.push_back({
                .property_index = PropertyIndex{static_cast<std::size_t>(idx)},
                .verdict = verdict,
                .timestamp = ts,
                .reason = std::move(reason),
            });
        }
        return StreamResult{.results = std::move(results)};
    } catch (const std::exception& e) {
        return std::unexpected(make_error(ErrorKind::Protocol, e.what()));
    }
}

auto parse_dbc_response(std::string_view input) -> Result<DbcDefinition> {
    try {
        auto j = json::parse(input);
        auto status = j.value("status", "");
        if (status == "error")
            return std::unexpected(
                make_error(ErrorKind::Protocol, j.value("message", "Unknown error")));
        if (status != "success")
            return std::unexpected(
                make_error(ErrorKind::Protocol, "Unexpected DBC response status: " + status));
        if (!j.contains("dbc"))
            return std::unexpected(
                make_error(ErrorKind::Protocol, "Missing 'dbc' field in response"));
        return parse_dbc_definition(j.at("dbc"));
    } catch (const std::exception& e) {
        return std::unexpected(make_error(ErrorKind::Protocol, e.what()));
    }
}

} // namespace aletheia::detail
