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

#include <aletheia/detail/cache_keys.hpp>

#include <cstddef>
#include <cstdint>
#include <map>
#include <memory>
#include <optional>
#include <span>
#include <string>
#include <type_traits>
#include <unordered_map>
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
    explicit AletheiaClient(std::unique_ptr<IBackend> backend, Logger logger = {},
                            std::vector<CheckResult> default_checks = {});
    ~AletheiaClient();

    AletheiaClient(const AletheiaClient&) = delete;
    AletheiaClient& operator=(const AletheiaClient&) = delete;
    AletheiaClient(AletheiaClient&& other) noexcept;
    AletheiaClient& operator=(AletheiaClient&& other) noexcept;

    // --- DBC ---
    [[nodiscard]] auto parse_dbc(const DbcDefinition& dbc) -> Result<void>;
    [[nodiscard]] auto validate_dbc(const DbcDefinition& dbc) -> Result<ValidationResult>;
    [[nodiscard]] auto format_dbc() -> Result<DbcDefinition>;

    // --- Signals ---
    // Payload length must match dlc_to_bytes(dlc); returns Validation error otherwise.
    [[nodiscard]] auto extract_signals(CanId id, Dlc dlc, std::span<const std::byte> data)
        -> Result<ExtractionResult>;
    [[nodiscard]] auto build_frame(CanId id, Dlc dlc, std::span<const SignalValue> signals)
        -> Result<FramePayload>;
    [[nodiscard]] auto update_frame(CanId id, Dlc dlc, std::span<const std::byte> data,
                                    std::span<const SignalValue> signals) -> Result<FramePayload>;

    // --- Streaming ---
    // Expected workflow: set_properties → start_stream → send_frame* → end_stream.
    // start_stream() resets the extraction cache and last-frame tracking.
    // set_properties() may be called again after end_stream() to install new properties.
    [[nodiscard]] auto set_properties(std::span<const LtlFormula> properties) -> Result<void>;
    [[nodiscard]] auto add_checks(std::vector<CheckResult> checks) -> Result<void>;
    [[nodiscard]] auto start_stream() -> Result<void>;
    // On violation, the returned Violation includes an optional ViolationEnrichment
    // with extracted signal values and a formatted reason string (requires
    // set_properties() to have been called to install diagnostics).
    // Payload length must match dlc_to_bytes(dlc); returns Validation error otherwise.
    // CAN-FD note: BRS/ESI flags are not part of the FFI protocol and are silently
    // dropped.  The Agda core operates on payload bytes + DLC only.
    // For batch operations, see send_frames().
    [[nodiscard]] auto send_frame(Timestamp ts, CanId id, Dlc dlc, std::span<const std::byte> data)
        -> Result<FrameResponse>;
    // CAN error event (no ID, no payload). Acknowledged without LTL evaluation.
    [[nodiscard]] auto send_error(Timestamp ts) -> Result<void>;
    // CAN remote frame (ID but no payload, CAN 2.0B only). Acknowledged without LTL evaluation.
    [[nodiscard]] auto send_remote(Timestamp ts, CanId id) -> Result<void>;
    // Send multiple frames in a single batch. A Violation is a normal response
    // and does not stop the batch. Processing stops at the first transport or
    // validation error; earlier successful responses are returned via
    // BatchResult::responses alongside the error.
    [[nodiscard]] auto send_frames(std::span<const Frame> frames) -> BatchResult;
    // Properties with Verdict::Fails include an optional ViolationEnrichment
    // populated from the last-known frame values for each relevant CAN ID.
    [[nodiscard]] auto end_stream() -> Result<StreamResult>;

private:
    // Signal-to-index resolution for binary FFI build/update paths.
    struct ResolvedSignals {
        std::vector<std::uint32_t> indices;
        std::vector<std::int64_t> numerators;
        std::vector<std::int64_t> denominators;
        [[nodiscard]] auto injection() const -> SignalInjection;
    };
    auto resolve_signals(CanId id, std::span<const SignalValue> signals) -> Result<ResolvedSignals>;

    void enrich_violation(Violation& v, CanId id, Dlc dlc, std::span<const std::byte> data,
                          std::uint32_t id_value, bool is_extended);
    void enrich_property_result(PropertyResult& pr);
    auto extract_signal_values(const PropertyDiagnostic& diag, CanId id, Dlc dlc,
                               std::span<const std::byte> data, std::uint32_t id_value,
                               bool is_extended) -> std::map<SignalName, PhysicalValue>;
    auto extract_last_known_values(const PropertyDiagnostic& diag)
        -> std::map<SignalName, PhysicalValue>;
    auto extract_signals_internal(CanId id, Dlc dlc, std::span<const std::byte> data,
                                  std::uint32_t id_value, bool is_extended)
        -> std::optional<ExtractionResult>;

    std::unique_ptr<IBackend> backend_;
    void* state_ = nullptr;
    Logger logger_;
    std::vector<CheckResult> default_checks_;
    std::vector<PropertyDiagnostic> diags_;

    // Extraction cache: keyed by (id_value, is_extended, dlc, payload).
    // Capped at max_cache_size entries; when full, new extractions are
    // performed but not cached (silent fallback to per-frame extraction).
    // Cache key types live in detail/cache_keys.hpp — see there for the
    // transparent comparator that enables heterogeneous lookup by FrameKeyView.
    static constexpr std::size_t max_cache_size = 256;
    std::map<detail::FrameKey, ExtractionResult, detail::FrameKeyLess> cache_;

    // Last frame seen per CAN ID, for end-of-stream enrichment.
    // Populated by send_frame(); cleared by start_stream().
    using LastFrameKey = std::pair<std::uint32_t, bool>; // {id_value, is_extended}
    struct LastFrame {
        CanId id;
        Dlc dlc;
        FramePayload data;
    };
    std::map<LastFrameKey, LastFrame> last_frames_;

    // Signal name → 0-based index within the DBC message's signal list.
    // Populated by parse_dbc(); cleared by parse_dbc().
    std::unordered_map<detail::SignalKey, std::uint32_t, detail::SignalKeyHash> signal_index_;

    // Index → signal name reverse lookup, keyed by (can_id_value, is_extended).
    // Populated alongside signal_index_ in parse_dbc().
    std::unordered_map<detail::MessageKey, std::vector<std::string>, detail::MessageKeyHash>
        signal_names_;
};

static_assert(!std::is_copy_constructible_v<AletheiaClient>,
              "AletheiaClient is not thread-safe and must not be copied");
static_assert(!std::is_copy_assignable_v<AletheiaClient>,
              "AletheiaClient is not thread-safe and must not be copied");

} // namespace aletheia
