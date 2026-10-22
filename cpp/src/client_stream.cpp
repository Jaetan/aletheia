// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
// AletheiaClient's streaming members, and the enrichment of the violations and
// end-of-stream results they report.
#include <aletheia/client.hpp>
#include <aletheia/detail/cache_keys.hpp>
#include <aletheia/detail/checked.hpp>
#include <aletheia/detail/rational_renderer.hpp>
#include <aletheia/enrich.hpp>

#include "detail/client_checks.hpp"
#include "detail/json.hpp"

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <exception>
#include <expected>
#include <format>
#include <iterator>
#include <map>
#include <optional>
#include <ranges>
#include <set>
#include <span>
#include <stop_token>
#include <string>
#include <string_view>
#include <utility>
#include <variant>
#include <vector>

namespace aletheia {

using detail::make_cancellation_error;
using detail::validate_payload;

static auto validate_timestamp(Timestamp ts) -> Result<void> {
    if (ts.count() < 0)
        return std::unexpected(
            AletheiaError{ErrorKind::Validation, "timestamp must be non-negative"});
    return {};
}

// ---------------------------------------------------------------------------
// Streaming
// ---------------------------------------------------------------------------

auto AletheiaClient::set_properties(std::stop_token stop, std::span<const LtlFormula> properties)
    -> Result<void> {
    if (stop.stop_requested()) [[unlikely]]
        return std::unexpected(make_cancellation_error("set_properties"));
    auto const cmd = detail::serialize_set_properties(properties);
    auto const resp = backend_->process(state_, cmd);
    auto result = detail::parse_success(resp);
    if (!result.has_value())
        return result;
    // build_diagnostic reaches format_rational_ffi which throws
    // AletheiaException(Ffi) on missing .so; lower to Result<> to honor
    // the documented contract (mirrors add_checks below).
    try {
        diags_.clear();
        for (auto const& f : properties)
            diags_.push_back(build_diagnostic(f));
        cache_.clear();
        logger_.info("properties.set", {{"count", static_cast<std::uint64_t>(properties.size())}});
        return result;
    } catch (const AletheiaException& e) {
        return std::unexpected(e.error());
    } catch (const std::exception& e) {
        return std::unexpected(AletheiaError{ErrorKind::Ffi, e.what()});
    }
}

auto AletheiaClient::add_checks(std::stop_token stop, std::vector<CheckResult> checks)
    -> Result<void> {
    if (stop.stop_requested()) [[unlikely]]
        return std::unexpected(make_cancellation_error("add_checks"));
    try {
        std::vector<LtlFormula> formulas;
        auto const to_formula = [](const CheckResult& c) { return c.to_formula(); };
        std::ranges::transform(default_checks_, std::back_inserter(formulas), to_formula);
        std::ranges::transform(checks, std::back_inserter(formulas), to_formula);
        return set_properties(stop, formulas);
    } catch (const AletheiaException& e) {
        return std::unexpected(e.error());
    } catch (const std::exception& e) {
        return std::unexpected(AletheiaError{ErrorKind::Validation, e.what()});
    }
}

auto AletheiaClient::start_stream(std::stop_token stop) -> Result<void> {
    if (stop.stop_requested()) [[unlikely]]
        return std::unexpected(make_cancellation_error("start_stream"));
    auto const resp = backend_->start_stream_binary(state_);
    auto result = detail::parse_success(resp);
    if (!result.has_value())
        return result;
    cache_.clear();
    logger_.info("stream.started");
    return result;
}

auto AletheiaClient::send_frame(std::stop_token stop, Timestamp ts, CanId id, Dlc dlc,
                                std::span<const std::byte> data, std::optional<bool> brs,
                                std::optional<bool> esi) -> Result<FrameResponse> {
    if (stop.stop_requested()) [[unlikely]]
        return std::unexpected(make_cancellation_error("send_frame"));
    if (auto const t = validate_timestamp(ts); !t.has_value())
        return std::unexpected(detail::error_of(t));
    if (auto const v = validate_payload(dlc, data); !v.has_value())
        return std::unexpected(detail::error_of(v));
    auto const resp = backend_->send_frame_binary(state_, ts, id, dlc, data, brs, esi);
    auto result = detail::parse_frame_response(resp);
    if (result.has_value()) {
        auto const id_value = can_id_value(id);
        auto const is_extended = can_id_is_extended(id);
        // Track last frame per CAN ID for end-of-stream enrichment.
        // Find-then-assign reuses the existing FramePayload's heap buffer
        // on subsequent frames for the same key — `assign` keeps the vector's
        // capacity intact when the new size fits, avoiding the temporary
        // `FramePayload(data.begin(), data.end())` allocation that
        // `insert_or_assign` would force per call.  First frame for a key
        // still allocates via `emplace`; this is the common cold path on a
        // bounded number of unique CAN IDs.
        auto const key = detail::MessageKey{id_value, is_extended};
        if (auto const it = last_frames_.find(key); it != last_frames_.end()) {
            it->second.id = id;
            it->second.dlc = dlc;
            it->second.data.assign(data.begin(), data.end());
        } else {
            last_frames_.emplace(
                key,
                LastFrame{.id = id, .dlc = dlc, .data = FramePayload(data.begin(), data.end())});
        }
        // PropertyBatch may carry mid-stream Satisfactions + a terminal
        // Violation; enrich each fails entry and emit the standard
        // frame.processed log event.  A helper, so send_frame stays under
        // clang-tidy's cognitive-complexity threshold.
        finalize_frame_response(result.value(), ts, id, dlc, data, id_value, is_extended);
    }
    return result;
}

auto AletheiaClient::send_frames(std::stop_token stop, std::span<const Frame> frames)
    -> BatchResult {
    BatchResult batch;
    for (auto const [i, frame] : std::views::enumerate(frames)) {
        // Per-frame check between FFI calls — the cancellation boundary for
        // batch ops. The most recent FFI call (if one was in flight when stop
        // fired) ran to completion and its response is in `responses`.
        if (stop.stop_requested()) [[unlikely]] {
            batch.error = make_cancellation_error("send_frames");
            return batch;
        }
        auto r = send_frame(stop, frame);
        if (!r.has_value()) {
            auto const& e = detail::error_of(r);
            // Cancellation propagates as-is so callers see ErrorKind::Cancellation
            // rather than a misleading "frame N: ..." wrap.
            if (e.kind() == ErrorKind::Cancellation) {
                batch.error = e;
            } else {
                // Forward `bound_info` so a mid-batch `InputBoundExceededError`
                // payload survives the per-frame context wrap, as the Python
                // and Go typed errors preserve it across their error paths.
                batch.error = AletheiaError{e.kind(), std::format("frame {}: {}", i, e.message()),
                                            e.code(), e.bound_info()};
            }
            return batch;
        }
        batch.responses.push_back(std::move(r).value());
    }
    return batch;
}

auto AletheiaClient::send_error(std::stop_token stop, Timestamp ts) -> Result<void> {
    if (stop.stop_requested()) [[unlikely]]
        return std::unexpected(make_cancellation_error("send_error"));
    if (auto const t = validate_timestamp(ts); !t.has_value())
        return std::unexpected(detail::error_of(t));
    auto const resp = backend_->send_error_binary(state_, ts);
    auto r = detail::parse_event_ack(resp);
    if (r.has_value()) {
        logger_.debug("error_event.sent", {{"ts", static_cast<std::int64_t>(ts.count())},
                                           {"response", std::string_view{"ack"}}});
    }
    return r;
}

auto AletheiaClient::send_remote(std::stop_token stop, Timestamp ts, CanId id) -> Result<void> {
    if (stop.stop_requested()) [[unlikely]]
        return std::unexpected(make_cancellation_error("send_remote"));
    if (auto const t = validate_timestamp(ts); !t.has_value())
        return std::unexpected(detail::error_of(t));
    auto const resp = backend_->send_remote_binary(state_, ts, id);
    auto r = detail::parse_event_ack(resp);
    if (r.has_value()) {
        logger_.debug("remote_event.sent", {{"ts", static_cast<std::int64_t>(ts.count())},
                                            {"canId", static_cast<std::uint64_t>(can_id_value(id))},
                                            {"extended", can_id_is_extended(id)},
                                            {"response", std::string_view{"ack"}}});
    }
    return r;
}

auto AletheiaClient::end_stream(std::stop_token stop) -> Result<StreamResult> {
    if (stop.stop_requested()) [[unlikely]]
        return std::unexpected(make_cancellation_error("end_stream"));
    auto const resp = backend_->end_stream_binary(state_);
    auto result = detail::parse_stream_result(resp);
    if (!result.has_value())
        return result;
    if (!diags_.empty())
        enrich_end_stream_results(result.value());
    log_end_stream_summary(result.value());
    // A finished stream holds no frame, so the next one starts with none.
    last_frames_.clear();
    return result;
}

void AletheiaClient::log_end_stream_summary(const StreamResult& result) {
    std::uint64_t num_fails = 0;
    std::uint64_t num_unresolved = 0;
    for (auto const& pr : result.results) {
        if (pr.verdict == Verdict::Fails)
            ++num_fails;
        else if (pr.verdict == Verdict::Unresolved)
            ++num_unresolved;
    }
    for (auto const& w : result.warnings) {
        if (w.kind == "uncached_atom") {
            logger_.warn("endstream.uncached_atom",
                         {{"property_index", static_cast<std::uint64_t>(w.property_index.get())},
                          {"detail", std::string_view{w.detail}}});
        }
    }
    logger_.info("stream.ended",
                 {{"numResults", static_cast<std::uint64_t>(result.results.size())},
                  {"numFails", num_fails},
                  {"numUnresolved", num_unresolved},
                  {"numWarnings", static_cast<std::uint64_t>(result.warnings.size())}});
}

// ---------------------------------------------------------------------------
// Enrichment internals
// ---------------------------------------------------------------------------

static auto collect_matching_signals(const PropertyDiagnostic& diag,
                                     const ExtractionResult& extraction)
    -> std::map<SignalName, PhysicalValue> {
    std::map<SignalName, PhysicalValue> values;
    for (auto const& sig : diag.signals) {
        for (auto const& sv : extraction.values) {
            if (sv.name == sig) {
                values.emplace(sig, sv.value);
                break;
            }
        }
    }
    return values;
}

static auto format_enriched_reason(const PropertyDiagnostic& diag,
                                   const std::map<SignalName, PhysicalValue>& values,
                                   std::string_view core_reason) -> std::string {
    std::string reason;
    auto const unrendered = "violated: " + diag.formula_desc;
    // Best-effort on the eval path: rendering the observed values needs the
    // runtime, which is up here (the frame was processed through it) — so this
    // is unreachable — but never sink an already-processed frame if the kernel
    // renderer throws. Degrade to the formula description (no value rendered,
    // no local fallback). set_properties, by contrast, propagates the throw.
    try {
        std::string parts;
        bool first = true;
        for (auto const& sig : diag.signals) {
            if (auto const it = values.find(sig); it != values.end()) {
                if (!first)
                    parts += ", ";
                // Render the observed value via the kernel formatℚ (same renderer
                // as the predicate threshold): exact, never a printf conversion or a
                // cast to double, and byte-identical to the other bindings.
                parts += std::format("{} = {}", std::string_view{sig},
                                     detail::format_rational_ffi(it->second.get().numerator(),
                                                                 it->second.get().denominator()));
                first = false;
            }
        }
        reason = first ? unrendered : parts + " (formula: " + diag.formula_desc + ")";
    } catch (const AletheiaException&) {
        reason = unrendered;
    }
    if (!core_reason.empty())
        reason += " [core: " + std::string{core_reason} + "]";
    return reason;
}

void AletheiaClient::finalize_frame_response(FrameResponse& fr, Timestamp ts, CanId id, Dlc dlc,
                                             std::span<const std::byte> data,
                                             std::uint32_t id_value, bool is_extended) {
    if (std::holds_alternative<PropertyBatch>(fr) && !diags_.empty()) {
        bool has_fail = false;
        for (auto& entry : std::get<PropertyBatch>(fr).results) {
            if (entry.verdict == Verdict::Fails) {
                enrich_violation(entry, id, dlc, data, id_value, is_extended);
                has_fail = true;
            }
        }
        logger_.debug("frame.processed",
                      {{"ts", static_cast<std::int64_t>(ts.count())},
                       {"canId", static_cast<std::uint64_t>(id_value)},
                       {"extended", is_extended},
                       {"response", std::string_view{has_fail ? "violation" : "satisfaction"}}});
        return;
    }
    logger_.debug("frame.processed", {{"ts", static_cast<std::int64_t>(ts.count())},
                                      {"canId", static_cast<std::uint64_t>(id_value)},
                                      {"extended", is_extended},
                                      {"response", std::string_view{"ack"}}});
}

void AletheiaClient::enrich_violation(PropertyResult& pr, CanId id, Dlc dlc,
                                      std::span<const std::byte> data, std::uint32_t id_value,
                                      bool is_extended) {
    auto& v = pr;
    auto const idx = v.property_index.get();
    if (idx >= diags_.size()) {
        // Property index out of range — protocol mismatch; skip enrichment.
        logger_.warn("enrichment.property_index_oob",
                     {{"index", static_cast<std::int64_t>(idx)},
                      {"count", static_cast<std::uint64_t>(diags_.size())}});
        return;
    }
    auto const& diag = diags_.at(idx);
    auto values = extract_signal_values(diag, id, dlc, data, id_value, is_extended);
    auto reason = format_enriched_reason(diag, values, v.reason);
    v.enrichment = ViolationEnrichment{
        .signals = std::move(values),
        .formula_desc = diag.formula_desc,
        .enriched_reason = std::move(reason),
        .core_reason = v.reason,
    };
}

void AletheiaClient::enrich_end_stream_results(StreamResult& result) {
    auto const todo = collect_enrichable_results(result);

    // Union of the signal names any collected diagnostic wants. When the
    // union is empty, skip the frame extraction loop entirely (zero FFI
    // extraction calls, no extraction_failed warnings) — but still attach
    // an enrichment to every collected result via the empty-values fallback.
    // Every formula names at least one signal, so the union is empty only
    // when nothing was collected.
    std::set<SignalName> wanted;
    for (auto const& [pr, diag] : todo)
        wanted.insert(diag->signals.begin(), diag->signals.end());
    std::map<SignalName, PhysicalValue> merged;
    if (!wanted.empty())
        merged = merge_last_known_values(std::move(wanted));

    // Distribute: each result's values are the merged map filtered to its
    // own diagnostic's signals; the enrichment is always attached (empty
    // values degrade to the "violated: <formula>" fallback reason).
    for (auto const& [pr, diag] : todo) {
        std::map<SignalName, PhysicalValue> values;
        for (auto const& sig : diag->signals) {
            if (auto const it = merged.find(sig); it != merged.end())
                values.emplace(sig, it->second);
        }
        auto reason = format_enriched_reason(*diag, values, pr->reason);
        pr->enrichment = ViolationEnrichment{
            .signals = std::move(values),
            .formula_desc = diag->formula_desc,
            .enriched_reason = std::move(reason),
            .core_reason = pr->reason,
        };
    }
}

auto AletheiaClient::collect_enrichable_results(StreamResult& result)
    -> std::vector<std::pair<PropertyResult*, const PropertyDiagnostic*>> {
    std::vector<std::pair<PropertyResult*, const PropertyDiagnostic*>> todo;
    for (auto& pr : result.results) {
        if (pr.verdict != Verdict::Fails && pr.verdict != Verdict::Unresolved)
            continue;
        auto const idx = pr.property_index.get();
        if (idx >= diags_.size()) {
            // Property index out of range — protocol mismatch; skip enrichment.
            logger_.warn("enrichment.property_index_oob",
                         {{"index", static_cast<std::int64_t>(idx)},
                          {"count", static_cast<std::uint64_t>(diags_.size())}});
            continue;
        }
        todo.emplace_back(&pr, &diags_.at(idx));
    }
    return todo;
}

auto AletheiaClient::extract_signal_values(const PropertyDiagnostic& diag, CanId id, Dlc dlc,
                                           std::span<const std::byte> data, std::uint32_t id_value,
                                           bool is_extended)
    -> std::map<SignalName, PhysicalValue> {
    // Heterogeneous lookup via FrameKeyView — avoids copying the payload into
    // a FramePayload on cache hits (the common hot-path case).
    const detail::FrameKeyView lookup{
        .id_value = id_value, .is_extended = is_extended, .dlc = dlc.value(), .data = data};

    auto cache_it = cache_.entries.find(lookup);
    if (cache_it == cache_.entries.end()) {
        logger_.debug("cache.miss", {{"canId", static_cast<std::uint64_t>(id_value)},
                                     {"dlc", static_cast<std::uint64_t>(dlc.value())}});
        auto extraction = extract_signals_internal(id, dlc, data, id_value, is_extended);
        if (!extraction.has_value())
            return {};
        if (cache_.entries.size() < max_cache_size) {
            // Construct the owning FrameKey only on insertion.
            detail::FrameKey key{.id_value = id_value,
                                 .is_extended = is_extended,
                                 .dlc = dlc.value(),
                                 .data = FramePayload(data.begin(), data.end())};
            cache_it = cache_.entries.emplace(std::move(key), std::move(extraction).value()).first;
        } else {
            if (!cache_.full_reported) {
                cache_.full_reported = true;
                logger_.warn("cache.full",
                             {{"size", static_cast<std::uint64_t>(cache_.entries.size())}});
            }
            // Over capacity — use result directly without caching
            return collect_matching_signals(diag, extraction.value());
        }
    } else {
        logger_.debug("cache.hit", {{"canId", static_cast<std::uint64_t>(id_value)},
                                    {"dlc", static_cast<std::uint64_t>(dlc.value())}});
    }

    return collect_matching_signals(diag, cache_it->second);
}

auto AletheiaClient::merge_last_known_values(std::set<SignalName> remaining)
    -> std::map<SignalName, PhysicalValue> {
    // One full-frame extraction per tracked frame, in ascending
    // (CAN id value, extended) order — std::map's key order is the sorted
    // contract. Every extracted signal merges first-frame-wins (emplace
    // never overwrites); a failed extraction warns once per frame per
    // end_stream. Stops early once every remaining wanted name is merged.
    std::map<SignalName, PhysicalValue> merged;
    for (auto const& [key, last_frame] : last_frames_) {
        auto const extraction = extract_signals_internal(last_frame.id, last_frame.dlc,
                                                         last_frame.data, key.first, key.second);
        if (!extraction.has_value()) {
            logger_.warn("enrichment.extraction_failed",
                         {{"canId", static_cast<std::uint64_t>(key.first)}});
            continue;
        }
        for (auto const& sv : extraction.value().values) {
            if (merged.emplace(sv.name, sv.value).second)
                remaining.erase(sv.name);
        }
        if (remaining.empty())
            break;
    }
    return merged;
}

} // namespace aletheia
