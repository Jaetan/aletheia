// SPDX-License-Identifier: BSD-2-Clause
#pragma once

#include <aletheia/backend.hpp>
#include <aletheia/dbc.hpp>
#include <aletheia/error.hpp>
#include <aletheia/ltl.hpp>
#include <aletheia/response.hpp>
#include <aletheia/types.hpp>
#include <aletheia/validation.hpp>

#include <memory>
#include <span>

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
    auto extract_signals(CanId id, std::span<const std::byte, 8> data) -> Result<ExtractionResult>;
    auto build_frame(CanId id, std::span<const SignalValue> signals) -> Result<FramePayload>;
    auto update_frame(CanId id, std::span<const std::byte, 8> data,
                      std::span<const SignalValue> signals) -> Result<FramePayload>;

    // --- Streaming ---
    auto set_properties(std::span<const LtlFormula> properties) -> Result<void>;
    auto start_stream() -> Result<void>;
    auto send_frame(Timestamp ts, CanId id, std::span<const std::byte, 8> data)
        -> Result<FrameResponse>;
    auto end_stream() -> Result<StreamResult>;

private:
    std::unique_ptr<IBackend> backend_;
    void* state_ = nullptr;
};

} // namespace aletheia
