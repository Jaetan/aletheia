// SPDX-License-Identifier: BSD-2-Clause
#pragma once

#include <aletheia/types.hpp>

#include <map>
#include <optional>
#include <string>
#include <utility>
#include <variant>
#include <vector>

namespace aletheia {

// ---------------------------------------------------------------------------
// Enrichment types (auto-derived from formula structure)
// ---------------------------------------------------------------------------

struct PropertyDiagnostic {
    std::vector<SignalName> signals;
    std::string formula_desc;
};

struct ViolationEnrichment {
    std::map<SignalName, PhysicalValue> signals;
    std::string formula_desc;
    std::string enriched_reason;
};

// ---------------------------------------------------------------------------
// Signal extraction result
// ---------------------------------------------------------------------------

struct ExtractionResult {
    std::vector<SignalValue> values;
    std::vector<std::pair<SignalName, std::string>> errors;
    std::vector<SignalName> absent;

    [[nodiscard]] auto get(const SignalName& name,
                           PhysicalValue fallback = PhysicalValue{0.0}) const -> PhysicalValue {
        for (const auto& sv : values)
            if (sv.name == name)
                return sv.value;
        return fallback;
    }

    [[nodiscard]] auto has_errors() const -> bool { return !errors.empty(); }
};

// ---------------------------------------------------------------------------
// Streaming frame response
// ---------------------------------------------------------------------------

struct Ack {};

struct Violation {
    PropertyIndex property_index;
    Timestamp timestamp;
    std::string reason;
    std::optional<ViolationEnrichment> enrichment;
};

using FrameResponse = std::variant<Ack, Violation>;

// ---------------------------------------------------------------------------
// End-of-stream result
// ---------------------------------------------------------------------------

enum class Verdict { Holds, Fails };

struct PropertyResult {
    PropertyIndex property_index{0};
    Verdict verdict = Verdict::Fails;
    std::optional<Timestamp> timestamp;
    std::string reason;
    std::optional<ViolationEnrichment> enrichment;
};

struct StreamResult {
    std::vector<PropertyResult> results;
};

} // namespace aletheia
