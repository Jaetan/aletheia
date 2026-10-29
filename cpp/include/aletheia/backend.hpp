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

    BackendState(BackendState const&) = delete;
    auto operator=(BackendState const&) -> BackendState& = delete;
    BackendState(BackendState&& other) noexcept;
    auto operator=(BackendState&& other) noexcept -> BackendState&;

    // The opaque handle the backend's own methods read. Null when empty.
    [[nodiscard]] auto get() const -> void* { return state_; }
    [[nodiscard]] explicit operator bool() const { return state_ != nullptr; }

private:
    // Closes what the handle holds, if anything, and leaves it empty.
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
    [[nodiscard]] static auto create(std::span<std::uint32_t const> indices,
                                     std::span<std::int64_t const> numerators,
                                     std::span<std::int64_t const> denominators)
        -> Result<SignalInjection>;

    [[nodiscard]] auto count() const -> std::uint32_t {
        return static_cast<std::uint32_t>(indices_.size());
    }
    [[nodiscard]] auto indices() const -> std::span<std::uint32_t const> { return indices_; }
    [[nodiscard]] auto numerators() const -> std::span<std::int64_t const> { return numerators_; }
    [[nodiscard]] auto denominators() const -> std::span<std::int64_t const> {
        return denominators_;
    }

private:
    SignalInjection() = default;

    std::span<std::uint32_t const> indices_;
    std::span<std::int64_t const> numerators_;
    std::span<std::int64_t const> denominators_;
};

// ---------------------------------------------------------------------------
// Backend interface (dependency injection for testability)
// ---------------------------------------------------------------------------

class IBackend {
public:
    virtual ~IBackend() = default;

    IBackend(IBackend const&) = delete;
    IBackend& operator=(IBackend const&) = delete;
    IBackend(IBackend&&) = delete;
    IBackend& operator=(IBackend&&) = delete;

    // ========================================================================
    // [MANDATORY] — every backend MUST implement these.
    // Pure-virtual sites grouped together;
    // optional default-implementation overrides live in the [OPTIONAL]
    // section below so a new backend implementer can read off the surface.
    // ========================================================================
    // init hands out the backend's state as an owning handle, which closes
    // through this backend when it goes out of scope, or refuses when the
    // backend has none to give. The release primitive itself is protected: the
    // handle is the only caller of close, so no call site releases state by
    // hand.
    //
    // Every endpoint answering text returns the kernel's response, or the error
    // that kept the backend from reaching the kernel or from reading its answer.
    [[nodiscard]] virtual auto init() -> Result<BackendState> = 0;
    [[nodiscard]] virtual auto process(BackendState const& state, std::string_view input)
        -> Result<std::string> = 0;

    // Binary frame FFI — bypasses JSON serialization on the send path.
    // Returns the raw JSON response string from the backend.
    // CAN-FD BRS / ESI bits (ISO 11898-1:2015 §10.4.2 / §10.4.3) are
    // passed as std::optional<bool> — std::nullopt for CAN 2.0B frames
    // where the bits do not exist.  The Aletheia kernel does not consume
    // BRS / ESI; they are pass-through metadata for binding consumers.
    [[nodiscard]] virtual auto send_frame_binary(BackendState const& state, Timestamp ts,
                                                 CanId const& id, Dlc dlc,
                                                 std::span<std::byte const> data,
                                                 std::optional<bool> brs, std::optional<bool> esi)
        -> Result<std::string> = 0;

    // Streaming / event endpoints — also pure-virtual.  There is no honest
    // generic default: only the binary FFI (FFIBackend) or a test double
    // (MockBackend, which records `<binary:OP>` sentinels) can service these,
    // so every backend declares how it streams.
    [[nodiscard]] virtual auto send_error_binary(BackendState const& state, Timestamp ts)
        -> Result<std::string> = 0;
    [[nodiscard]] virtual auto send_remote_binary(BackendState const& state, Timestamp ts,
                                                  CanId const& id) -> Result<std::string> = 0;
    [[nodiscard]] virtual auto start_stream_binary(BackendState const& state)
        -> Result<std::string> = 0;
    [[nodiscard]] virtual auto end_stream_binary(BackendState const& state)
        -> Result<std::string> = 0;
    [[nodiscard]] virtual auto format_dbc_binary(BackendState const& state)
        -> Result<std::string> = 0;
    [[nodiscard]] virtual auto extract_signals_binary(BackendState const& state, CanId const& id,
                                                      Dlc dlc, std::span<std::byte const> data)
        -> Result<std::string> = 0;

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
    [[nodiscard]] virtual auto build_frame_bin(BackendState const& state, CanId const& id, Dlc dlc,
                                               SignalInjection signals, std::size_t expected_bytes)
        -> std::expected<std::vector<std::byte>, AletheiaError>;

    [[nodiscard]] virtual auto update_frame_bin(BackendState const& state, CanId const& id, Dlc dlc,
                                                std::span<std::byte const> data,
                                                SignalInjection signals, std::size_t expected_bytes)
        -> std::expected<std::vector<std::byte>, AletheiaError>;

    // Binary extraction (no JSON on input or output) — packed buffer on success.
    [[nodiscard]] virtual auto extract_signals_bin(BackendState const& state, CanId const& id,
                                                   Dlc dlc, std::span<std::byte const> data)
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
    // It cannot fail: both callers run where a throw would terminate the
    // program, and noexcept holds every override to that.
    virtual auto close(void* state) noexcept -> void = 0;

    friend class BackendState;
};

// Production: loads libaletheia-ffi.so via dlopen and starts the GHC runtime
// on it unless `start_runtime` or another backend has. The count-less form
// asks for the count running, 1 when nothing runs; the counted form asks for
// `rts_cores`, and a runtime already up on another count keeps its own, the
// difference reported by `rts_mismatch_info()`. Refuses as `start_runtime`
// does: Validation for a count outside 1 to the CPUs the process may use or an
// empty path, Ffi for a library that does not open, is laid out for another ABI
// version or lacks an entry the backend reads.
[[nodiscard]] auto make_ffi_backend(std::filesystem::path const& lib_path)
    -> Result<std::unique_ptr<IBackend>>;
[[nodiscard]] auto make_ffi_backend(std::filesystem::path const& lib_path, int rts_cores)
    -> Result<std::unique_ptr<IBackend>>;

// Production, env-configured: loads the library named by the ALETHEIA_LIB
// environment variable, mirroring the Python and Rust bindings' env-based
// resolution: the zero-config entry point for a bundled install whose
// install.sh exports ALETHEIA_LIB. Refuses (Validation) if ALETHEIA_LIB is
// unset or empty; for an explicit path use the overloads above.
[[nodiscard]] auto make_ffi_backend_from_env() -> Result<std::unique_ptr<IBackend>>;
[[nodiscard]] auto make_ffi_backend_from_env(int rts_cores) -> Result<std::unique_ptr<IBackend>>;

// Starts the kernel's GHC runtime on `cores` capabilities, loading `lib`, unless
// it runs: 1 for one bus, the number of buses when several threads each
// monitor their own. The kernel reads every number a check carries
// (`Rational::from_decimal`, the YAML and Excel loaders), so a program that
// loads checks before it builds a client calls it first; a backend made later
// with no count asks for the count running. A runtime already up keeps its
// count, and the answer is then `{active, requested}` when they differ,
// `std::nullopt` otherwise. Refuses (Validation) a count outside 1 to the CPUs
// the process may use or an empty path, and (Ffi) a library that does not open,
// is laid out for another ABI version or lacks an entry the start reads.
[[nodiscard]] auto start_runtime(std::filesystem::path const& lib, int cores)
    -> Result<std::optional<std::pair<int, int>>>;

// `start_runtime` on the library ALETHEIA_LIB names. Refuses (Validation) if
// ALETHEIA_LIB is unset or empty.
[[nodiscard]] auto start_runtime_from_env(int cores) -> Result<std::optional<std::pair<int, int>>>;

// The bytes the kernel's runtime has allocated since it started, a count of the
// whole process, so the difference of two reads is what ran between them
// allocated. It is read through the library the runtime started on, and is
// `std::nullopt` until it has started. Each read runs a collection first,
// which a timed span should leave out.
[[nodiscard]] auto allocated_bytes() -> std::optional<std::uint64_t>;

// Where the binding looks for libaletheia-ffi.so, in one order that every
// caller shares: the ALETHEIA_LIB variable, which an empty value leaves unset;
// then the path a start or a make_ffi_backend call registered; then three build
// directories relative to the working directory, furthest first.
//
// AletheiaClient::open, the command line and the benchmarks share it, so they
// find the library one way; after a start it prefers the path the start
// opened, so a library looked for later is the one the runtime runs on.
//
// Refuses (Ffi) an ALETHEIA_LIB naming no file, as Python does, rather than
// trying the next route, and refuses when no route finds a library.
[[nodiscard]] auto find_ffi_library() -> Result<std::filesystem::path>;

// Test: a fixed backend that answers every operation with the wire's
// acknowledgement and every frame request with a zero-filled payload of the
// size asked for. It queues nothing and records nothing, so a consumer holding
// only these headers can drive a client without reaching into the tree. The
// configurable double, which records requests and refuses when its queue runs
// out, is test-internal and is not on this surface.
[[nodiscard]] auto make_mock_backend() -> std::unique_ptr<IBackend>;

} // namespace aletheia
