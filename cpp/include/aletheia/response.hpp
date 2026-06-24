// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
#pragma once

#include <aletheia/error.hpp>
#include <aletheia/types.hpp>

#include <map>
#include <optional>
#include <string>
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
    // Raw reason from the Agda core (e.g., "MetricEventually: window expired").
    // May be empty.
    std::string core_reason;
};

// ---------------------------------------------------------------------------
// Signal extraction result
// ---------------------------------------------------------------------------

// A single failed signal extraction: the signal name plus the human-readable
// reason from the core. Mirrors Go's `SignalError{Name, Error}`, Rust's
// `SignalError{name, reason}`, and Python's `errors: Mapping[str, str]`.
struct SignalError {
    SignalName name;
    std::string reason;
};

struct ExtractionResult {
    std::vector<SignalValue> values;
    std::vector<SignalError> errors;
    std::vector<SignalName> absent;

    [[nodiscard]] auto get(const SignalName& name,
                           PhysicalValue fallback = PhysicalValue{Rational{}}) const
        -> PhysicalValue {
        for (const auto& sv : values)
            if (sv.name == name)
                return sv.value;
        return fallback;
    }

    [[nodiscard]] auto has_errors() const -> bool { return !errors.empty(); }
};

// ---------------------------------------------------------------------------
// Per-property verdict (used by both streaming PropertyBatch + EndStream)
// ---------------------------------------------------------------------------

/// End-of-stream verdict for an LTL property.
///
/// ``Unresolved`` corresponds to the Agda coalgebra's three-valued Kleene
/// ``Unsure`` verdict: the property was neither proved to hold nor proved
/// to fail on the observed trace. Typical cause: an atomic predicate whose
/// signal was never observed (e.g. ``Always(p)`` where no frame carrying
/// ``p``'s signal arrived before end-of-stream). This is the
/// user-observable manifestation of a violated ``AllObserved`` invariant
/// — see ``aletheia/client.hpp`` § "Streaming adequacy" for the full
/// contract. The denotational semantics agrees this is Unknown, so it is
/// reported as a distinct verdict rather than collapsed to ``Fails``.
enum class Verdict { Holds, Fails, Unresolved };

struct PropertyResult {
    PropertyIndex property_index{0};
    Verdict verdict = Verdict::Fails;
    std::optional<Timestamp> timestamp;
    std::string reason;
    std::optional<ViolationEnrichment> enrichment;
};

// ---------------------------------------------------------------------------
// Streaming frame response
// ---------------------------------------------------------------------------

struct Ack {};

// Per-frame batch of property events emitted during streaming.  R23 —
// AGDA-D-12.1: pre-R23 each frame carried at most one Violation (or no
// event = Ack); after the mid-stream-Satisfaction lift each frame can
// also produce one-or-more Holds entries that completed at this frame,
// in source-order, optionally terminated by a Fails entry.  The inner
// PropertyResult shape mirrors EndStream's per-property verdict.
//
// Empty `results` is unreachable — frames with no events return Ack.
struct PropertyBatch {
    std::vector<PropertyResult> results;

    /// First PropertyResult with Verdict == Fails, or nullptr if the
    /// batch carries only mid-stream Satisfactions.  Per the Agda
    /// invariant, a batch contains at most one violation and (if
    /// present) it is the last entry.
    [[nodiscard]] auto first_violation() -> PropertyResult* {
        for (auto& r : results)
            if (r.verdict == Verdict::Fails)
                return &r;
        return nullptr;
    }
    [[nodiscard]] auto first_violation() const -> const PropertyResult* {
        for (const auto& r : results)
            if (r.verdict == Verdict::Fails)
                return &r;
        return nullptr;
    }
};

using FrameResponse = std::variant<Ack, PropertyBatch>;

/// One EndStream diagnostic surfaced by the kernel.
///
/// R21 cluster 1 — AGDA-D-12.1: kind == "uncached_atom" is emitted when
/// a property's atom references a signal that never appeared in trace.
/// The Unresolved verdict on that property is sound (three-valued Kleene
/// Unknown) but indistinguishable from a genuine Kleene-undecidable
/// Unresolved without this warning.
///
/// New kinds are additive on the wire (kernel adds new WarningKind
/// constructors; bindings should accept unknown kinds rather than reject).
struct StreamWarning {
    std::string kind;
    PropertyIndex property_index{0};
    std::string detail;
};

struct StreamResult {
    std::vector<PropertyResult> results;
    std::vector<StreamWarning> warnings;
};

// ---------------------------------------------------------------------------
// Batch frame result
// ---------------------------------------------------------------------------

/// Result of sending multiple frames via send_frames().
/// On success, error is nullopt and responses contains all results.
/// On mid-batch failure, responses contains results from frames processed
/// before the error, and error carries the failure.
/// A Violation is a normal response and is included in responses — only
/// transport or validation errors stop the batch.
struct BatchResult {
    std::vector<FrameResponse> responses;
    std::optional<AletheiaError> error;

    [[nodiscard]] auto has_error() const -> bool { return error.has_value(); }
};

} // namespace aletheia
