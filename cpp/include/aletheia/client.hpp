// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
#pragma once

// client.hpp is the umbrella facade for the public API — consumers include
// this header and get the full vocabulary types transitively. IWYU pragmas
// tell misc-include-cleaner the re-exports are intentional, so using (e.g.)
// aletheia::CanId after `#include <aletheia/client.hpp>` does not require a
// second direct include of types.hpp at every call site.
#include <aletheia/backend.hpp>    // IWYU pragma: export
#include <aletheia/check.hpp>      // IWYU pragma: export
#include <aletheia/dbc.hpp>        // IWYU pragma: export
#include <aletheia/error.hpp>      // IWYU pragma: export
#include <aletheia/log.hpp>        // IWYU pragma: export
#include <aletheia/ltl.hpp>        // IWYU pragma: export
#include <aletheia/response.hpp>   // IWYU pragma: export
#include <aletheia/types.hpp>      // IWYU pragma: export
#include <aletheia/validation.hpp> // IWYU pragma: export

#include <aletheia/detail/cache_keys.hpp> // IWYU pragma: private, include "aletheia/client.hpp"

#include <concepts>
#include <cstddef>
#include <cstdint>
#include <format>
#include <generator>
#include <map>
#include <memory>
#include <optional>
#include <ranges>
#include <span>
#include <stop_token>
#include <string>
#include <type_traits>
#include <unordered_map>
#include <utility>
#include <vector>

namespace aletheia {

// Thread safety: each AletheiaClient owns independent backend state (a separate
// StablePtr<IORef StreamState> on the Haskell side). Multiple clients may operate
// concurrently from different threads — there is no shared mutable state between
// instances. Create one client per CAN bus per thread.
//
// A single AletheiaClient is NOT thread-safe. Do not call methods on the same
// instance from multiple threads concurrently. For concurrent multi-bus
// monitoring, create separate client instances per thread.
//
// The GHC RTS is initialized once (hs_init is ref-counted and thread-safe).
// Individual aletheia_process() calls go through independent StablePtrs, so
// there is no contention between clients.
//
// Cancellation: every operation method takes a [std::stop_token] as its first
// parameter and honors cancellation cooperatively at FFI boundaries — see
// docs/architecture/CANCELLATION.md for the full contract. Callers who do not
// care about cancellation pass a default-constructed `std::stop_token{}`,
// which never reports stop_requested (mirrors Go's `context.Background()`).
// Construction and destruction do NOT take stop_token (synchronous and
// uncancellable by design).
//
// Streaming adequacy (Unresolved verdicts):
//
// The streaming evaluator is sound but requires that every property's
// target signal is observed in the input trace at least once — the
// AllObserved invariant from
// Aletheia.Protocol.Adequacy.StreamingWarm.streaming-warms-cache. This
// is a user obligation on the trace; the FFI does not check it.
//
// When the obligation is violated (e.g., a property references a signal
// that no frame in the trace carries), the property may finalize as
// Verdict::Unresolved — the three-valued Kleene "Unsure" — rather than
// Verdict::Holds or Verdict::Fails. Reported verdicts remain sound;
// coverage is the caller's responsibility.
//
// See docs/architecture/PROTOCOL.md § Streaming Semantics: Soundness
// vs. Completeness for the full contract.
class AletheiaClient {
public:
    /// \param backend  FFI / mock backend providing the kernel protocol.
    /// \param logger   Optional structured logger; default-constructed is a
    ///                 no-op sink-less logger.
    /// \param default_checks  Pre-loaded YAML/Excel check results.  Same
    ///                 shape as the per-call argument to `apply_checks`;
    ///                 useful when the client is constructed with a fixed
    ///                 ruleset and `apply_checks` is called repeatedly.
    explicit AletheiaClient(std::unique_ptr<IBackend> backend, Logger logger = {},
                            std::vector<CheckResult> default_checks = {});
    ~AletheiaClient();

    AletheiaClient(const AletheiaClient&) = delete;
    AletheiaClient& operator=(const AletheiaClient&) = delete;
    AletheiaClient(AletheiaClient&& other) noexcept;
    AletheiaClient& operator=(AletheiaClient&& other) noexcept;

    // --- DBC ---
    // Both parse paths run the structural validator alongside the parser.
    // On success the returned ParsedDBC carries the canonical body plus any
    // non-error issues (warnings).  Errors short-circuit to Result<>::error.
    [[nodiscard]] auto parse_dbc(std::stop_token stop, const DbcDefinition& dbc)
        -> Result<ParsedDBC>;
    [[nodiscard]] auto parse_dbc_text(std::stop_token stop, std::string_view text)
        -> Result<ParsedDBC>;
    [[nodiscard]] auto validate_dbc(std::stop_token stop, const DbcDefinition& dbc)
        -> Result<ValidationResult>;
    [[nodiscard]] auto format_dbc(std::stop_token stop) -> Result<DbcDefinition>;
    // Render a DbcDefinition as .dbc file text via the verified Agda formatter.
    // Inverse of parse_dbc_text at the wire level: parse_dbc_text(format_dbc_text(d))
    // returns d byte-identical for any well-formed DBC (Track E.9a coverage).
    // Does not modify client state — pass any DbcDefinition value (typically from
    // parse_dbc_text, format_dbc, or a JSON load).
    [[nodiscard]] auto format_dbc_text(std::stop_token stop, const DbcDefinition& dbc)
        -> Result<std::string>;

    // --- Signals ---
    // Payload length must match dlc_to_bytes(dlc); returns Validation error otherwise.
    [[nodiscard]] auto extract_signals(std::stop_token stop, CanId id, Dlc dlc,
                                       std::span<const std::byte> data) -> Result<ExtractionResult>;
    [[nodiscard]] auto build_frame(std::stop_token stop, CanId id, Dlc dlc,
                                   std::span<const SignalValue> signals) -> Result<FramePayload>;
    [[nodiscard]] auto update_frame(std::stop_token stop, CanId id, Dlc dlc,
                                    std::span<const std::byte> data,
                                    std::span<const SignalValue> signals) -> Result<FramePayload>;

    // --- Streaming ---
    // Expected workflow: set_properties → start_stream → send_frame* → end_stream.
    // start_stream() resets the extraction cache and last-frame tracking.
    // set_properties() may be called again after end_stream() to install new properties.
    [[nodiscard]] auto set_properties(std::stop_token stop, std::span<const LtlFormula> properties)
        -> Result<void>;
    [[nodiscard]] auto add_checks(std::stop_token stop, std::vector<CheckResult> checks)
        -> Result<void>;
    [[nodiscard]] auto start_stream(std::stop_token stop) -> Result<void>;
    // On violation, the Fails entry in the returned PropertyBatch carries an
    // optional ViolationEnrichment with extracted signal values and a formatted
    // reason string (requires set_properties() to have been called to install
    // diagnostics).
    // Payload length must match dlc_to_bytes(dlc); returns Validation error otherwise.
    // CAN-FD BRS / ESI bits (ISO 11898-1:2015 §10.4.2 / §10.4.3) are passed
    // as std::optional<bool> — std::nullopt for CAN 2.0B frames where the
    // bits do not exist on the wire.  The Aletheia kernel does not consume
    // BRS / ESI; they are pass-through metadata for binding consumers and
    // the JSON wire shape (R19P2 cluster 18 — AGDA-D-10.1 closure).
    // For batch operations, see send_frames().
    [[nodiscard]] auto send_frame(std::stop_token stop, Timestamp ts, CanId id, Dlc dlc,
                                  std::span<const std::byte> data,
                                  std::optional<bool> brs = std::nullopt,
                                  std::optional<bool> esi = std::nullopt) -> Result<FrameResponse>;
    // Convenience: send a Frame directly.
    [[nodiscard]] auto send_frame(std::stop_token stop, const Frame& f) -> Result<FrameResponse> {
        return send_frame(stop, f.timestamp, f.id, f.dlc, f.data, f.brs, f.esi);
    }
    // CAN error event (no ID, no payload). Acknowledged without LTL evaluation.
    [[nodiscard]] auto send_error(std::stop_token stop, Timestamp ts) -> Result<void>;
    // CAN remote frame (ID but no payload, CAN 2.0B only). Acknowledged without LTL evaluation.
    [[nodiscard]] auto send_remote(std::stop_token stop, Timestamp ts, CanId id) -> Result<void>;
    // Send multiple frames in a single batch. A Violation is a normal response
    // and does not stop the batch. Processing stops at the first transport or
    // validation error; earlier successful responses are returned via
    // BatchResult::responses alongside the error. Cancellation observed at
    // frame boundaries (commit-prefix-and-report per CANCELLATION.md §3.3): if
    // stop fires mid-batch, BatchResult::responses holds the committed prefix
    // and BatchResult::error carries ErrorKind::Cancellation.
    [[nodiscard]] auto send_frames(std::stop_token stop, std::span<const Frame> frames)
        -> BatchResult;
    // Lazy streaming variant of send_frames: a std::generator that pulls one
    // Frame from `frames` per resumption and co_yields its Result<FrameResponse>,
    // never materializing the whole input or the whole response set. The C++23
    // analogue of Python's send_frames_iter. Use it when the source is a live or
    // large producer (a log reader, a socket); a contiguous batch already in
    // memory can be passed as a std::span or std::views::all view over it.
    //
    // Contract (commit-prefix-and-report, per CANCELLATION.md §3.3): each value
    // co_yielded with a value is a frame already committed to the stream state.
    // The first failing frame is co_yielded as an std::unexpected (matching
    // send_frames' shaping: cancellation forwarded as-is, otherwise the frame
    // index is prefixed) and the generator then completes — no frame after a
    // failure is sent. Cancellation is the generator protocol: stop pulling (or
    // let `stop` fire) and the remaining frames are never sent.
    //
    // `frames` is taken by value into the coroutine frame, so it must own or
    // view storage that outlives the iteration: pass an owning range by move, or
    // a std::span / std::views::all view over a buffer you keep alive. The
    // per-frame `send_frame` is the shared primitive (identical validation,
    // logging, and cancellation as a single send); the eager send_frames is its
    // collecting sibling.
    template<std::ranges::input_range R>
        requires std::convertible_to<std::ranges::range_reference_t<R>, const Frame&>
    [[nodiscard]] auto send_frames_lazy(std::stop_token stop, R frames)
        -> std::generator<Result<FrameResponse>> {
        std::size_t index = 0;
        for (auto&& f : frames) {
            auto r = send_frame(stop, f);
            if (!r.has_value()) {
                const auto& e = r.error();
                if (e.kind() == ErrorKind::Cancellation) {
                    co_yield std::unexpected(e);
                } else {
                    co_yield std::unexpected(
                        AletheiaError{e.kind(), std::format("frame {}: {}", index, e.message()),
                                      e.code(), e.bound_info()});
                }
                co_return;
            }
            co_yield std::move(r);
            ++index;
        }
    }
    // Properties with Verdict::Fails or Verdict::Unresolved include an
    // optional ViolationEnrichment populated from the last-known frame values
    // for each relevant CAN ID.
    [[nodiscard]] auto end_stream(std::stop_token stop) -> Result<StreamResult>;

private:
    // Signal-to-index resolution for binary FFI build/update paths.
    struct ResolvedSignals {
        std::vector<std::uint32_t> indices;
        std::vector<std::int64_t> numerators;
        std::vector<std::int64_t> denominators;
        [[nodiscard]] auto injection() const -> SignalInjection;
    };
    auto resolve_signals(CanId id, std::span<const SignalValue> signals) -> Result<ResolvedSignals>;

    // R23 — AGDA-D-12.1: takes a single PropertyResult (one entry from a
    // PropertyBatch.results) rather than a top-level Violation struct.
    // The caller iterates the batch and invokes this per fails entry.
    void enrich_violation(PropertyResult& pr, CanId id, Dlc dlc, std::span<const std::byte> data,
                          std::uint32_t id_value, bool is_extended);
    // R23 — AGDA-D-12.1: post-parse hook for streaming frame responses.
    // Iterates a PropertyBatch's results, enriches each fails entry, and
    // emits the standard `frame.processed` log event.  Extracted from
    // send_frame to keep that function under clang-tidy's cognitive-
    // complexity threshold (25).
    void finalize_frame_response(FrameResponse& fr, Timestamp ts, CanId id, Dlc dlc,
                                 std::span<const std::byte> data, std::uint32_t id_value,
                                 bool is_extended);
    void enrich_property_result(PropertyResult& pr);
    void log_end_stream_summary(const StreamResult& result);
    auto extract_signal_values(const PropertyDiagnostic& diag, CanId id, Dlc dlc,
                               std::span<const std::byte> data, std::uint32_t id_value,
                               bool is_extended) -> std::map<SignalName, PhysicalValue>;
    auto extract_last_known_values(const PropertyDiagnostic& diag)
        -> std::map<SignalName, PhysicalValue>;
    auto extract_signals_internal(CanId id, Dlc dlc, std::span<const std::byte> data,
                                  std::uint32_t id_value, bool is_extended)
        -> std::optional<ExtractionResult>;

    // Refresh signal name → index cache from a parsed DBC.  Shared between
    // parse_dbc() and parse_dbc_text(); both paths land here on success.
    void populate_signal_lookup(const DbcDefinition& dbc);

    std::unique_ptr<IBackend> backend_;
    void* state_ = nullptr;
    Logger logger_;
    std::vector<CheckResult> default_checks_;
    std::vector<PropertyDiagnostic> diags_;

    // Extraction cache: keyed by (id_value, is_extended, dlc, payload).
    // Capped at max_cache_size entries; when full, new extractions are
    // performed but not cached (falls back to per-frame extraction, logging
    // a `cache.full` warning).
    // Cache key types live in detail/cache_keys.hpp — see there for the
    // transparent comparator that enables heterogeneous lookup by FrameKeyView.
    static constexpr std::size_t max_cache_size = 256;
    std::map<detail::FrameKey, ExtractionResult, detail::FrameKeyLess> cache_;

    // Last frame seen per CAN ID, for end-of-stream enrichment.
    // Populated by send_frame() (guarded by !diags_.empty()); cleared by
    // start_stream() and by end_stream() once enrichment has consumed it.
    // Storage: one entry per unique (CAN ID, extended) pair.
    struct LastFrame {
        CanId id;
        Dlc dlc;
        FramePayload data;
    };
    std::map<detail::MessageKey, LastFrame> last_frames_;

    // Signal name → 0-based index within the DBC message's signal list.
    // Rebuilt (cleared + repopulated) by populate_signal_lookup() on every
    // successful parse_dbc() / parse_dbc_text().
    std::unordered_map<detail::SignalKey, std::uint32_t, detail::SignalKeyHash> signal_index_;

    // Index → signal name reverse lookup, keyed by (can_id_value, is_extended).
    // Rebuilt alongside signal_index_ in populate_signal_lookup().
    std::unordered_map<detail::MessageKey, std::vector<std::string>, detail::MessageKeyHash>
        signal_names_;
};

static_assert(!std::is_copy_constructible_v<AletheiaClient>,
              "AletheiaClient is not thread-safe and must not be copied");
static_assert(!std::is_copy_assignable_v<AletheiaClient>,
              "AletheiaClient is not thread-safe and must not be copied");

} // namespace aletheia
