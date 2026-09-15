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

class IBackend;

// ---------------------------------------------------------------------------
// Backend state handle
// ---------------------------------------------------------------------------

// Owns the opaque state a backend hands out at init and releases it exactly
// once, through the backend that created it. The handle holds the release
// policy in one place: it closes on destruction, a moved-from handle closes
// nothing, and a handle assigned over releases what it held first.
//
// A default-constructed or moved-from handle is empty; get() is then null and
// the bool conversion is false.
class BackendState {
public:
    BackendState() = default;
    BackendState(IBackend& backend, void* state) : backend_(&backend), state_(state) {}
    ~BackendState();

    BackendState(const BackendState&) = delete;
    auto operator=(const BackendState&) -> BackendState& = delete;
    BackendState(BackendState&& other) noexcept;
    auto operator=(BackendState&& other) noexcept -> BackendState&;

    // The opaque handle the backend's own methods read. Null when empty.
    [[nodiscard]] auto get() const -> void* { return state_; }
    [[nodiscard]] explicit operator bool() const { return state_ != nullptr; }

private:
    // Closes what the handle holds, if anything, and leaves it empty. Swallows,
    // because both callers run where a throw would terminate the program.
    void release() noexcept;

    IBackend* backend_ = nullptr;
    void* state_ = nullptr;
};

// ---------------------------------------------------------------------------
// Signal injection parameter block
// ---------------------------------------------------------------------------

// The signal values to inject into a frame, as the three arrays the FFI reads
// in parallel. The type carries what a comment used to state: create refuses a
// block whose three arrays differ in length, and one longer than the FFI's own
// 32-bit count can carry, so no caller can hand the boundary a length it would
// read past.
class SignalInjection {
public:
    [[nodiscard]] static auto create(std::span<const std::uint32_t> indices,
                                     std::span<const std::int64_t> numerators,
                                     std::span<const std::int64_t> denominators)
        -> std::expected<SignalInjection, std::string>;

    [[nodiscard]] auto count() const -> std::uint32_t {
        return static_cast<std::uint32_t>(indices_.size());
    }
    [[nodiscard]] auto indices() const -> std::span<const std::uint32_t> { return indices_; }
    [[nodiscard]] auto numerators() const -> std::span<const std::int64_t> { return numerators_; }
    [[nodiscard]] auto denominators() const -> std::span<const std::int64_t> {
        return denominators_;
    }

private:
    SignalInjection() = default;

    std::span<const std::uint32_t> indices_;
    std::span<const std::int64_t> numerators_;
    std::span<const std::int64_t> denominators_;
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
    // init hands out the backend's state as an owning handle, which closes
    // through this backend when it goes out of scope. The release primitive
    // itself is protected: the handle is the only caller of close, so no call
    // site releases state by hand.
    [[nodiscard]] virtual auto init() -> BackendState = 0;
    [[nodiscard]] virtual auto process(const BackendState& state, std::string_view input)
        -> std::string = 0;

    // Binary frame FFI — bypasses JSON serialization on the send path.
    // Returns the raw JSON response string from the backend.
    // CAN-FD BRS / ESI bits (ISO 11898-1:2015 §10.4.2 / §10.4.3) are
    // passed as std::optional<bool> — std::nullopt for CAN 2.0B frames
    // where the bits do not exist.  The Aletheia kernel does not consume
    // BRS / ESI; they are pass-through metadata for binding consumers.
    [[nodiscard]] virtual auto send_frame_binary(const BackendState& state, Timestamp ts,
                                                 const CanId& id, Dlc dlc,
                                                 std::span<const std::byte> data,
                                                 std::optional<bool> brs, std::optional<bool> esi)
        -> std::string = 0;

    // Streaming / event endpoints — also pure-virtual.  There is no honest
    // generic default: only the binary FFI (FFIBackend) or a test double
    // (MockBackend, which records `<binary:OP>` sentinels) can service these,
    // so every backend declares how it streams.
    [[nodiscard]] virtual auto send_error_binary(const BackendState& state, Timestamp ts)
        -> std::string = 0;
    [[nodiscard]] virtual auto send_remote_binary(const BackendState& state, Timestamp ts,
                                                  const CanId& id) -> std::string = 0;
    [[nodiscard]] virtual auto start_stream_binary(const BackendState& state) -> std::string = 0;
    [[nodiscard]] virtual auto end_stream_binary(const BackendState& state) -> std::string = 0;
    [[nodiscard]] virtual auto format_dbc_binary(const BackendState& state) -> std::string = 0;
    [[nodiscard]] virtual auto extract_signals_binary(const BackendState& state, const CanId& id,
                                                      Dlc dlc, std::span<const std::byte> data)
        -> std::string = 0;

    // ========================================================================
    // [OPTIONAL] — base class provides a default implementation; specialized
    // backends (e.g. FFIBackend) override these to take the binary-FFI fast
    // path.  Non-FFI backends inherit a default that returns the
    // `BinaryUnsupported` sentinel: on extract_signals_bin the Client then
    // falls through to the JSON path, while build_frame_bin and
    // update_frame_bin surface the error (the JSON path cannot carry signal
    // indices).  rts_mismatch_info defaults to `std::nullopt`.
    // ========================================================================

    // Binary output endpoints — raw payload bytes on success, AletheiaError on failure.
    [[nodiscard]] virtual auto build_frame_bin(const BackendState& state, const CanId& id, Dlc dlc,
                                               SignalInjection signals, std::size_t expected_bytes)
        -> std::expected<std::vector<std::byte>, AletheiaError>;

    [[nodiscard]] virtual auto update_frame_bin(const BackendState& state, const CanId& id, Dlc dlc,
                                                std::span<const std::byte> data,
                                                SignalInjection signals, std::size_t expected_bytes)
        -> std::expected<std::vector<std::byte>, AletheiaError>;

    // Binary extraction (no JSON on input or output) — packed buffer on success.
    [[nodiscard]] virtual auto extract_signals_bin(const BackendState& state, const CanId& id,
                                                   Dlc dlc, std::span<const std::byte> data)
        -> std::expected<std::vector<std::byte>, AletheiaError>;

    // Startup diagnostic for the GHC RTS cores-mismatch case — emitted by
    // the Client as the `rts.cores_mismatch` log event with the
    // `active_cores` / `requested_cores` fields the other bindings emit.
    // Returns `std::nullopt` when no mismatch occurred.  Defined out of line
    // in backend.cpp with the other defaults, so the vtable is emitted there
    // once.
    [[nodiscard]] virtual auto rts_mismatch_info() const -> std::optional<std::pair<int, int>>;

protected:
    IBackend() = default;

    // The release primitive, reached only through BackendState's destructor and
    // its move assignment. Every backend implements it; nothing else calls it.
    virtual auto close(void* state) -> void = 0;

    friend class BackendState;
};

// Production: loads libaletheia-ffi.so via dlopen
[[nodiscard]] auto make_ffi_backend(const std::filesystem::path& lib_path, int rts_cores = 1)
    -> std::unique_ptr<IBackend>;

// Production, env-configured: loads the library named by the ALETHEIA_LIB
// environment variable, mirroring the Python and Rust bindings' env-based
// resolution — the zero-config entry point for a bundled install whose
// install.sh exports ALETHEIA_LIB. Throws AletheiaException(Validation) if
// ALETHEIA_LIB is unset or empty; for an explicit path use the overload above.
[[nodiscard]] auto make_ffi_backend_from_env(int rts_cores = 1) -> std::unique_ptr<IBackend>;

// Test: returns canned responses
[[nodiscard]] auto make_mock_backend() -> std::unique_ptr<IBackend>;

} // namespace aletheia
