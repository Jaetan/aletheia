// SPDX-License-Identifier: BSD-2-Clause
#pragma once

#include <aletheia/backend.hpp>
#include <aletheia/dbc.hpp>
#include <aletheia/error.hpp>
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
// The GHC RTS is initialized once (hs_init is ref-counted and thread-safe).
// Individual aletheia_process() calls go through independent StablePtrs, so
// there is no contention between clients.
class AletheiaClient {
public:
    explicit AletheiaClient(std::unique_ptr<IBackend> backend);
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
    auto extract_signals(CanId id, Dlc dlc, std::span<const std::byte> data)
        -> Result<ExtractionResult>;
    auto build_frame(CanId id, Dlc dlc, std::span<const SignalValue> signals) -> Result<FramePayload>;
    auto update_frame(CanId id, Dlc dlc, std::span<const std::byte> data,
                      std::span<const SignalValue> signals) -> Result<FramePayload>;

    // --- Streaming ---
    auto set_properties(std::span<const LtlFormula> properties) -> Result<void>;
    auto start_stream() -> Result<void>;
    auto send_frame(Timestamp ts, CanId id, Dlc dlc, std::span<const std::byte> data)
        -> Result<FrameResponse>;
    auto end_stream() -> Result<StreamResult>;

private:
    void enrich_violation(Violation& v, CanId id, Dlc dlc, std::span<const std::byte> data);
    void enrich_property_result(PropertyResult& pr);
    auto extract_signal_values(const PropertyDiagnostic& diag, CanId id, Dlc dlc,
                               std::span<const std::byte> data)
        -> std::map<SignalName, PhysicalValue>;
    auto extract_signals_internal(CanId id, Dlc dlc, std::span<const std::byte> data)
        -> std::optional<ExtractionResult>;

    std::unique_ptr<IBackend> backend_;
    void* state_ = nullptr;
    std::vector<PropertyDiagnostic> diags_;

    // Extraction cache: keyed by (id_value, is_extended, dlc, payload)
    struct FrameKey {
        std::uint32_t id_value;
        bool is_extended;
        std::uint8_t dlc;
        FramePayload data;
        auto operator<=>(const FrameKey&) const = default;
    };
    static constexpr std::size_t max_cache_size_ = 256;
    std::map<FrameKey, ExtractionResult> cache_;
};

} // namespace aletheia
