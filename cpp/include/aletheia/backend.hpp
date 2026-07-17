// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
#pragma once

// Re-export: backend.hpp's interface references CanId, Dlc, Timestamp,
// AletheiaError, ErrorKind — callers that include backend.hpp should get
// those vocabulary types without an extra direct include.
#include <aletheia/error.hpp> // IWYU pragma: export
#include <aletheia/types.hpp> // IWYU pragma: export

#include <cstddef>
#include <cstdint>
#include <expected>
#include <filesystem>
#include <memory>
#include <optional>
#include <span>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

namespace aletheia {

// ---------------------------------------------------------------------------
// Signal injection parameter block
// ---------------------------------------------------------------------------

// Bundles the parallel arrays describing signal values to inject into a frame.
// Grouped into one struct to keep backend-method parameter counts reasonable and
// to document that the three arrays must all have length `count`.
struct SignalInjection {
    std::uint32_t count;
    const std::uint32_t* indices;
    const std::int64_t* numerators;
    const std::int64_t* denominators;
};

// ---------------------------------------------------------------------------
// Backend interface (dependency injection for testability)
// ---------------------------------------------------------------------------

class IBackend {
public:
    virtual ~IBackend() = default;

    IBackend(const IBackend&) = delete;
    IBackend& operator=(const IBackend&) = delete;
    IBackend(IBackend&&) = delete;
    IBackend& operator=(IBackend&&) = delete;

    // ========================================================================
    // [MANDATORY] — every backend MUST implement these.
    // Pure-virtual sites grouped together;
    // optional default-implementation overrides live in the [OPTIONAL]
    // section below so a new backend implementer can read off the surface.
    // ========================================================================
    virtual auto init() -> void* = 0;
    virtual auto process(void* state, std::string_view input) -> std::string = 0;
    virtual auto close(void* state) -> void = 0;

    // Binary frame FFI — bypasses JSON serialization on the send path.
    // Returns the raw JSON response string from the backend.
    // CAN-FD BRS / ESI bits (ISO 11898-1:2015 §10.4.2 / §10.4.3) are
    // passed as std::optional<bool> — std::nullopt for CAN 2.0B frames
    // where the bits do not exist.  The Aletheia kernel does not consume
    // BRS / ESI; they are pass-through metadata for binding consumers.
    [[nodiscard]] virtual auto send_frame_binary(void* state, Timestamp ts, const CanId& id,
                                                 Dlc dlc, std::span<const std::byte> data,
                                                 std::optional<bool> brs, std::optional<bool> esi)
        -> std::string = 0;

    // Streaming / event endpoints — also pure-virtual.  There is no honest
    // generic default: only the binary FFI (FFIBackend) or a test double
    // (MockBackend, which records `<binary:OP>` sentinels) can service these,
    // so every backend declares how it streams.  The former defaults routed
    // through the JSON `process()` path, mirroring streaming commands the Agda
    // core no longer accepts (and `send_error`/`send_remote` had no core JSON
    // command at all) — they were removed.
    [[nodiscard]] virtual auto send_error_binary(void* state, Timestamp ts) -> std::string = 0;
    [[nodiscard]] virtual auto send_remote_binary(void* state, Timestamp ts, const CanId& id)
        -> std::string = 0;
    [[nodiscard]] virtual auto start_stream_binary(void* state) -> std::string = 0;
    [[nodiscard]] virtual auto end_stream_binary(void* state) -> std::string = 0;
    [[nodiscard]] virtual auto format_dbc_binary(void* state) -> std::string = 0;
    [[nodiscard]] virtual auto extract_signals_binary(void* state, const CanId& id, Dlc dlc,
                                                      std::span<const std::byte> data)
        -> std::string = 0;

    // ========================================================================
    // [OPTIONAL] — base class provides a default implementation; specialized
    // backends (e.g. FFIBackend) override these to take the binary-FFI fast
    // path.  Non-FFI backends inherit a default that returns the
    // `BinaryUnsupported` sentinel (so Client can fall through to JSON) or, for
    // `rts_mismatch_info`, `std::nullopt`.
    // ========================================================================

    // Binary output endpoints — raw payload bytes on success, AletheiaError on failure.
    [[nodiscard]] virtual auto build_frame_bin(void* state, const CanId& id, Dlc dlc,
                                               SignalInjection signals, std::size_t expected_bytes)
        -> std::expected<std::vector<std::byte>, AletheiaError>;

    [[nodiscard]] virtual auto update_frame_bin(void* state, const CanId& id, Dlc dlc,
                                                std::span<const std::byte> data,
                                                SignalInjection signals, std::size_t expected_bytes)
        -> std::expected<std::vector<std::byte>, AletheiaError>;

    // Binary extraction (no JSON on input or output) — packed buffer on success.
    [[nodiscard]] virtual auto extract_signals_bin(void* state, const CanId& id, Dlc dlc,
                                                   std::span<const std::byte> data)
        -> std::expected<std::vector<std::byte>, AletheiaError>;

    // Startup diagnostic for the GHC RTS cores-mismatch case — emitted by
    // the Client as the `rts.cores_mismatch` log event. Returns
    // `std::nullopt` when no mismatch occurred, keeping the structured log
    // schema stable across bindings (Go + Python both emit `active_cores` /
    // `requested_cores` fields). Out-of-line default in backend.cpp keeps
    // the ABI stable across binding builds.
    [[nodiscard]] virtual auto rts_mismatch_info() const -> std::optional<std::pair<int, int>>;

protected:
    IBackend() = default;
};

// Production: loads libaletheia-ffi.so via dlopen
auto make_ffi_backend(const std::filesystem::path& lib_path, int rts_cores = 1)
    -> std::unique_ptr<IBackend>;

// Production, env-configured: loads the library named by the ALETHEIA_LIB
// environment variable, mirroring the Python and Rust bindings' env-based
// resolution — the zero-config entry point for a bundled install whose
// install.sh exports ALETHEIA_LIB. Throws AletheiaException(Validation) if
// ALETHEIA_LIB is unset or empty; for an explicit path use the overload above.
auto make_ffi_backend_from_env(int rts_cores = 1) -> std::unique_ptr<IBackend>;

// Test: returns canned responses
auto make_mock_backend() -> std::unique_ptr<IBackend>;

} // namespace aletheia
