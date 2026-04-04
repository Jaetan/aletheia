// SPDX-License-Identifier: BSD-2-Clause
#pragma once

#include <aletheia/error.hpp>
#include <aletheia/types.hpp>

#include <cstddef>
#include <cstdint>
#include <expected>
#include <filesystem>
#include <memory>
#include <span>
#include <string>
#include <string_view>
#include <vector>

namespace aletheia {

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

    virtual auto init() -> void* = 0;
    virtual auto process(void* state, std::string_view input) -> std::string = 0;
    virtual auto close(void* state) -> void = 0;

    // Binary frame FFI — bypasses JSON serialization on the send path.
    // Returns the raw JSON response string from the backend.
    [[nodiscard]] virtual auto send_frame_binary(void* state, Timestamp ts, const CanId& id,
                                                 Dlc dlc, std::span<const std::byte> data)
        -> std::string = 0;

    // --- Binary FFI endpoints (bypass JSON input serialization) ---
    // Default implementations fall back to JSON via process() for backward
    // compatibility with MockBackend and other test doubles.

    // State transitions (no args → JSON response).
    [[nodiscard]] virtual auto start_stream_binary(void* state) -> std::string;
    [[nodiscard]] virtual auto end_stream_binary(void* state) -> std::string;
    [[nodiscard]] virtual auto format_dbc_binary(void* state) -> std::string;

    // Binary CAN frame → JSON response (signal extraction without streaming).
    [[nodiscard]] virtual auto extract_signals_binary(void* state, const CanId& id, Dlc dlc,
                                                      std::span<const std::byte> data)
        -> std::string;

    // Signal index-value pairs → JSON response (frame building).
    // indices/numerators/denominators are parallel arrays of length num_signals.
    [[nodiscard]] virtual auto build_frame_binary(void* state, const CanId& id, Dlc dlc,
                                                  std::uint32_t num_signals,
                                                  const std::uint32_t* indices,
                                                  const std::int64_t* numerators,
                                                  const std::int64_t* denominators)
        -> std::string;

    // Frame + signal pairs → JSON response (frame update).
    [[nodiscard]] virtual auto update_frame_binary(void* state, const CanId& id, Dlc dlc,
                                                   std::span<const std::byte> data,
                                                   std::uint32_t num_signals,
                                                   const std::uint32_t* indices,
                                                   const std::int64_t* numerators,
                                                   const std::int64_t* denominators)
        -> std::string;

    // --- Binary output endpoints (no JSON on output either) ---
    // Returns raw payload bytes on success, error string on failure.
    // Default implementations fall back to JSON path for MockBackend compatibility.

    [[nodiscard]] virtual auto build_frame_bin(void* state, const CanId& id, Dlc dlc,
                                               std::uint32_t num_signals,
                                               const std::uint32_t* indices,
                                               const std::int64_t* numerators,
                                               const std::int64_t* denominators,
                                               std::size_t expected_bytes)
        -> std::expected<std::vector<std::byte>, AletheiaError>;

    [[nodiscard]] virtual auto update_frame_bin(void* state, const CanId& id, Dlc dlc,
                                                std::span<const std::byte> data,
                                                std::uint32_t num_signals,
                                                const std::uint32_t* indices,
                                                const std::int64_t* numerators,
                                                const std::int64_t* denominators,
                                                std::size_t expected_bytes)
        -> std::expected<std::vector<std::byte>, AletheiaError>;

    // --- Binary extraction (no JSON on input or output) ---
    // Returns packed binary buffer on success, error string on failure.
    // Default implementation falls back to JSON path for MockBackend compatibility.
    [[nodiscard]] virtual auto extract_signals_bin(void* state, const CanId& id, Dlc dlc,
                                                    std::span<const std::byte> data)
        -> std::expected<std::vector<std::byte>, AletheiaError>;

protected:
    IBackend() = default;
};

// Production: loads libaletheia-ffi.so via dlopen
auto make_ffi_backend(const std::filesystem::path& lib_path, int rts_cores = 1)
    -> std::unique_ptr<IBackend>;

// Test: returns canned responses
auto make_mock_backend() -> std::unique_ptr<IBackend>;

} // namespace aletheia
