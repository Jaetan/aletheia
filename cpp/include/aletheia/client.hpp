// SPDX-License-Identifier: BSD-2-Clause
#pragma once

#include <aletheia/backend.hpp>
#include <aletheia/check.hpp>
#include <aletheia/dbc.hpp>
#include <aletheia/error.hpp>
#include <aletheia/log.hpp>
#include <aletheia/ltl.hpp>
#include <aletheia/response.hpp>
#include <aletheia/types.hpp>
#include <aletheia/validation.hpp>

#include <cstddef>
#include <cstdint>
#include <map>
#include <memory>
#include <optional>
#include <span>
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
class AletheiaClient {
public:
    explicit AletheiaClient(std::unique_ptr<IBackend> backend, Logger logger = {});
    ~AletheiaClient();

    AletheiaClient(const AletheiaClient&) = delete;
    AletheiaClient& operator=(const AletheiaClient&) = delete;
    AletheiaClient(AletheiaClient&& other) noexcept;
    AletheiaClient& operator=(AletheiaClient&& other) noexcept;

    // --- DBC ---
    auto parse_dbc(const DbcDefinition& dbc) -> Result<void>;
    auto validate_dbc(const DbcDefinition& dbc) -> Result<ValidationResult>;
    auto format_dbc() -> Result<DbcDefinition>;

    // --- Signals ---
    // Payload length must match dlc_to_bytes(dlc); returns Validation error otherwise.
    auto extract_signals(CanId id, Dlc dlc, std::span<const std::byte> data)
        -> Result<ExtractionResult>;
    auto build_frame(CanId id, Dlc dlc, std::span<const SignalValue> signals)
        -> Result<FramePayload>;
    auto update_frame(CanId id, Dlc dlc, std::span<const std::byte> data,
                      std::span<const SignalValue> signals) -> Result<FramePayload>;

    // --- Streaming ---
    // Expected workflow: set_properties → start_stream → send_frame* → end_stream.
    // start_stream() resets the extraction cache and last-frame tracking.
    // set_properties() may be called again after end_stream() to install new properties.
    auto set_properties(std::span<const LtlFormula> properties) -> Result<void>;
    auto add_checks(std::vector<CheckResult> checks) -> Result<void>;
    auto start_stream() -> Result<void>;
    // On violation, the returned Violation includes an optional ViolationEnrichment
    // with extracted signal values and a formatted reason string (requires
    // set_properties() to have been called to install diagnostics).
    // Payload length must match dlc_to_bytes(dlc); returns Validation error otherwise.
    // For batch operations, see send_frames().
    auto send_frame(Timestamp ts, CanId id, Dlc dlc, std::span<const std::byte> data)
        -> Result<FrameResponse>;
    // Send multiple frames in a single batch. A Violation is a normal response
    // and does not stop the batch. Processing stops at the first transport or
    // validation error; earlier successful responses are returned via
    // BatchResult::responses alongside the error.
    auto send_frames(std::span<const Frame> frames) -> BatchResult;
    // Properties with Verdict::Fails include an optional ViolationEnrichment
    // populated from the last-known frame values for each relevant CAN ID.
    auto end_stream() -> Result<StreamResult>;

private:
    void enrich_violation(Violation& v, CanId id, Dlc dlc, std::span<const std::byte> data);
    void enrich_property_result(PropertyResult& pr);
    auto extract_signal_values(const PropertyDiagnostic& diag, CanId id, Dlc dlc,
                               std::span<const std::byte> data)
        -> std::map<SignalName, PhysicalValue>;
    auto extract_last_known_values(const PropertyDiagnostic& diag)
        -> std::map<SignalName, PhysicalValue>;
    auto extract_signals_internal(CanId id, Dlc dlc, std::span<const std::byte> data)
        -> std::optional<ExtractionResult>;

    std::unique_ptr<IBackend> backend_;
    void* state_ = nullptr;
    Logger logger_;
    std::vector<PropertyDiagnostic> diags_;

    // Extraction cache: keyed by (id_value, is_extended, dlc, payload).
    // Capped at max_cache_size entries; when full, new extractions are
    // performed but not cached (silent fallback to per-frame extraction).
    struct FrameKey {
        std::uint32_t id_value;
        bool is_extended;
        std::uint8_t dlc;
        FramePayload data;
        auto operator<=>(const FrameKey&) const = default;
    };
    static constexpr std::size_t max_cache_size = 256;
    std::map<FrameKey, ExtractionResult> cache_;

    // Last frame seen per CAN ID, for end-of-stream enrichment.
    // Populated by send_frame(); cleared by start_stream().
    using LastFrameKey = std::pair<std::uint32_t, bool>; // {id_value, is_extended}
    struct LastFrame {
        CanId id;
        Dlc dlc;
        FramePayload data;
    };
    std::map<LastFrameKey, LastFrame> last_frames_;
};

} // namespace aletheia
