// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
// FFI backend: loads libaletheia-ffi.so via dlopen and starts the GHC runtime
// on it through the start `runtime_start.cpp` holds, unless the runtime runs.
#include <aletheia/backend.hpp>
#include <aletheia/detail/checked.hpp>
#include <aletheia/detail/rational_renderer.hpp>
#include <aletheia/types.hpp>

#include "detail/ffi_abi.hpp"
#include "detail/ffi_logic.hpp"
#include "detail/kernel_library.hpp"

#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <expected>
#include <filesystem>
#include <format>
#include <memory>
#include <optional>
#include <span>
#include <string>
#include <string_view>
#include <tuple>
#include <utility>
#include <vector>

namespace aletheia {

namespace {

using AletheiaInitFn = void* (*)();
using AletheiaProcessFn = char* (*)(void*, const detail::FfiText*);
using AletheiaSendFrameFn = char* (*)(void*, const detail::FfiFrame*);
using AletheiaFreeStrFn = void (*)(char*);
using AletheiaCloseFn = void (*)(void*);

// CAN error/remote event endpoints.
using AletheiaSendErrorFn = char* (*)(void*, const detail::FfiFrame*);
using AletheiaSendRemoteFn = char* (*)(void*, const detail::FfiFrame*);

// Binary FFI endpoints (no JSON input serialization).
using AletheiaNoArgFn = char* (*)(void*);
using AletheiaExtractFn = char* (*)(void*, const detail::FfiFrame*);

// Binary output endpoints (return a status code, write into the buffer).
using AletheiaFrameBinFn = std::int8_t (*)(void*, const detail::FfiFrame*,
                                           const detail::FfiSignalValues*, detail::FfiBuffer*);
using AletheiaExtractBinFn = std::int8_t (*)(void*, const detail::FfiFrame*, detail::FfiBuffer*);
using AletheiaFreeBufFn = void (*)(std::uint8_t*);
} // namespace

// ---------------------------------------------------------------------------
// Byte ↔ uint8_t pointer aliasing at the FFI boundary.
//
// The C++ surface holds payloads as std::span<const std::byte> / std::vector<
// std::byte>, while the Haskell FFI signatures expect const std::uint8_t* and
// std::uint8_t*. The reinterpret_cast here is well-defined: [basic.types]
// guarantees std::byte is layout-compatible with unsigned char, and std::
// uint8_t is unsigned char on every platform we target (Clang 23 on Linux
// x86_64/ARM64). The NOLINTs below are centralised so the FFI call
// sites stay free of noise; every byte-cast flows through these three fns.
static auto as_u8(const std::byte* p) -> const std::uint8_t* {
    // NOLINTNEXTLINE(cppcoreguidelines-pro-type-reinterpret-cast)
    return reinterpret_cast<const std::uint8_t*>(p);
}

static auto as_u8(std::byte* p) -> std::uint8_t* {
    // NOLINTNEXTLINE(cppcoreguidelines-pro-type-reinterpret-cast)
    return reinterpret_cast<std::uint8_t*>(p);
}

static auto as_byte(const std::uint8_t* p) -> const std::byte* {
    // NOLINTNEXTLINE(cppcoreguidelines-pro-type-reinterpret-cast)
    return reinterpret_cast<const std::byte*>(p);
}

// A trace event without payload: a remote frame's timestamp and identifier, or
// an error frame's timestamp alone.
static auto event_frame(Timestamp ts, std::uint32_t can_id, std::uint8_t extended)
    -> detail::FfiFrame {
    return {.timestamp = static_cast<std::uint64_t>(ts.count()),
            .data = nullptr,
            .can_id = can_id,
            .extended = extended,
            .dlc = 0,
            .data_len = 0,
            .brs_present = 0,
            .brs_value = 0,
            .esi_present = 0,
            .esi_value = 0};
}

// A frame carrying identifier and DLC only, for the entry that reads no payload.
static auto header_frame(const CanId& id, Dlc dlc) -> detail::FfiFrame {
    return {.timestamp = 0,
            .data = nullptr,
            .can_id = can_id_value(id),
            .extended = static_cast<std::uint8_t>(can_id_is_extended(id) ? 1 : 0),
            .dlc = dlc.value(),
            .data_len = 0,
            .brs_present = 0,
            .brs_value = 0,
            .esi_present = 0,
            .esi_value = 0};
}

// A frame carrying identifier, DLC and payload.  The caller has checked that
// the payload is the byte count its DLC names, at most 64, so the cast of its
// length to the byte the frame carries loses nothing.
static auto payload_frame(const CanId& id, Dlc dlc, std::span<const std::byte> data)
    -> detail::FfiFrame {
    auto frame = header_frame(id, dlc);
    frame.data = as_u8(data.data());
    frame.data_len = static_cast<std::uint8_t>(data.size());
    return frame;
}

static auto signal_values(const SignalInjection& signals) -> detail::FfiSignalValues {
    return {.indices = signals.indices().data(),
            .numerators = signals.numerators().data(),
            .denominators = signals.denominators().data(),
            .count = signals.count()};
}

// The payload of a frame is exactly the byte count its DLC names, the rule the
// kernel holds a frame to.  A payload of any other length is refused here,
// before the call, which also keeps its length within the byte the frame
// carries it in.
static auto payload_length_error(Dlc dlc, std::span<const std::byte> data)
    -> std::optional<AletheiaError> {
    auto const expected = dlc_to_bytes(dlc);
    if (data.size() == expected)
        return std::nullopt;
    return AletheiaError{ErrorKind::Validation,
                         std::format("payload length {} does not match DLC {} (expected {} bytes)",
                                     data.size(), dlc.value(), expected)};
}

namespace {

// The kernel entries a backend calls, read through the resolver that read the
// runtime's, so a library lacking one is refused naming the first missing.
struct KernelEntries {
    AletheiaInitFn init = nullptr;
    AletheiaProcessFn process = nullptr;
    AletheiaSendFrameFn send_frame = nullptr;
    AletheiaFreeStrFn free_str = nullptr;
    AletheiaCloseFn close = nullptr;
    AletheiaSendErrorFn send_error = nullptr;
    AletheiaSendRemoteFn send_remote = nullptr;
    AletheiaNoArgFn start_stream = nullptr;
    AletheiaNoArgFn end_stream = nullptr;
    AletheiaNoArgFn format_dbc = nullptr;
    AletheiaExtractFn extract_signals = nullptr;
    AletheiaFrameBinFn build_frame_bin = nullptr;
    AletheiaFrameBinFn update_frame_bin = nullptr;
    AletheiaExtractBinFn extract_signals_bin = nullptr;
    AletheiaFreeBufFn free_buf = nullptr;
};

// Backend wrapping libaletheia-ffi.so via dlopen.  Lifecycle invariant:
// the GHC RTS is process-global, so the destructor must NOT call
// `hs_exit()` (the RTS does not support reinitialisation) and must NOT
// `dlclose()` the library (the RTS owns threads that still reference it).
// The library handle and StablePtr state therefore leak by design at
// destruction — see `~FfiBackend` for the implementation.
class FfiBackend : public IBackend {
    void* handle_ = nullptr;
    KernelEntries fns_;
    // Populated when the backend detects that the GHC RTS was already
    // initialised with a different -N value than the caller requested.
    // Emitted by Client as the `rts.cores_mismatch` structured log event
    // with `active_cores` / `requested_cores` fields (Go + Python parity).
    std::optional<std::pair<int, int>> rts_mismatch_;

    // Wrap an FFI char* result with the standard null-check + RAII deleter
    // + std::string conversion pattern.  Refuses with ErrorKind::Protocol and
    // `error_msg` when result is null; otherwise materializes the C string
    // into a std::string and frees the FFI buffer via free_str.  Protocol is
    // the correct kind here per the narrow definition of ErrorKind::Ffi in
    // error.hpp ("Library load / RTS initialization failure": the boundary
    // itself failed before Agda ran); a runtime null-return means the kernel
    // was loaded but did not produce a response, which mirrors the
    // ProtocolError the Python client raises for the same condition.  Every
    // string-returning endpoint below goes through it.
    [[nodiscard]] auto wrap_str_result(char* result, std::string_view error_msg)
        -> Result<std::string> {
        if (result == nullptr)
            return std::unexpected(AletheiaError{ErrorKind::Protocol, std::string{error_msg}});
        auto const deleter = [this](char* p) { fns_.free_str(p); };
        const std::unique_ptr<char, decltype(deleter)> guard{result, deleter};
        return std::string{result};
    }

public:
    // Takes the library once the start has run on it, which the destructor
    // deliberately keeps (see the class-level docstring).
    FfiBackend(void* handle, KernelEntries fns, std::optional<std::pair<int, int>> rts_mismatch)
        : handle_(handle)
        , fns_(fns)
        , rts_mismatch_(std::move(rts_mismatch)) {}

    // See class-level docstring for the no-hs_exit / no-dlclose rationale.
    ~FfiBackend() override = default;

    FfiBackend(const FfiBackend&) = delete;
    FfiBackend& operator=(const FfiBackend&) = delete;
    FfiBackend(FfiBackend&&) = delete;
    FfiBackend& operator=(FfiBackend&&) = delete;

    [[nodiscard]] auto rts_mismatch_info() const -> std::optional<std::pair<int, int>> override {
        return rts_mismatch_;
    }

    auto init() -> Result<BackendState> override { return BackendState{*this, fns_.init()}; }

    auto process(const BackendState& state, std::string_view input)
        -> Result<std::string> override {
        if (auto refusal = detail::json_input_bound_error(input.size()))
            return std::move(refusal).value();
        auto const text = detail::ffi_text(input);
        return wrap_str_result(fns_.process(state.get(), &text), "aletheia_process returned null");
    }

    auto send_frame_binary(const BackendState& state, Timestamp ts, const CanId& id, Dlc dlc,
                           std::span<const std::byte> data, std::optional<bool> brs,
                           std::optional<bool> esi) -> Result<std::string> override {
        if (auto const err = payload_length_error(dlc, data))
            return std::unexpected(err.value());

        // Encode optional<bool> as (present, value) byte pairs — inverse
        // of the Haskell shim's mkMaybeBool.
        auto const encode = [](std::optional<bool> b) -> std::pair<std::uint8_t, std::uint8_t> {
            if (!b.has_value())
                return {0, 0};
            return {1, static_cast<std::uint8_t>(b.value() ? 1 : 0)};
        };
        auto frame = payload_frame(id, dlc, data);
        frame.timestamp = static_cast<std::uint64_t>(ts.count());
        std::tie(frame.brs_present, frame.brs_value) = encode(brs);
        std::tie(frame.esi_present, frame.esi_value) = encode(esi);

        return wrap_str_result(fns_.send_frame(state.get(), &frame),
                               "aletheia_send_frame returned null");
    }

    auto send_error_binary(const BackendState& state, Timestamp ts)
        -> Result<std::string> override {
        auto const frame = event_frame(ts, 0, 0);
        return wrap_str_result(fns_.send_error(state.get(), &frame),
                               "aletheia_send_error returned null");
    }

    auto send_remote_binary(const BackendState& state, Timestamp ts, const CanId& id)
        -> Result<std::string> override {
        auto const frame = event_frame(ts, can_id_value(id),
                                       static_cast<std::uint8_t>(can_id_is_extended(id) ? 1 : 0));
        return wrap_str_result(fns_.send_remote(state.get(), &frame),
                               "aletheia_send_remote returned null");
    }

    auto start_stream_binary(const BackendState& state) -> Result<std::string> override {
        return wrap_str_result(fns_.start_stream(state.get()),
                               "aletheia_start_stream returned null");
    }

    auto end_stream_binary(const BackendState& state) -> Result<std::string> override {
        return wrap_str_result(fns_.end_stream(state.get()), "aletheia_end_stream returned null");
    }

    auto format_dbc_binary(const BackendState& state) -> Result<std::string> override {
        return wrap_str_result(fns_.format_dbc(state.get()), "aletheia_format_dbc returned null");
    }

    auto extract_signals_binary(const BackendState& state, const CanId& id, Dlc dlc,
                                std::span<const std::byte> data) -> Result<std::string> override {
        if (auto const err = payload_length_error(dlc, data))
            return std::unexpected(err.value());
        auto const frame = payload_frame(id, dlc, data);
        return wrap_str_result(fns_.extract_signals(state.get(), &frame),
                               "aletheia_extract_signals returned null");
    }

    auto build_frame_bin(const BackendState& state, const CanId& id, Dlc dlc,
                         SignalInjection signals, std::size_t expected_bytes)
        -> std::expected<std::vector<std::byte>, AletheiaError> override {
        auto const frame = header_frame(id, dlc);
        auto const values = signal_values(signals);
        std::vector<std::byte> buf(expected_bytes);
        detail::FfiBuffer out{.data = as_u8(buf.data()),
                              .err = nullptr,
                              .size = static_cast<std::uint32_t>(buf.size())};
        auto const status = fns_.build_frame_bin(state.get(), &frame, &values, &out);
        if (auto const err = detail::ffi_error_from_status(status, out.err, fns_.free_str))
            return std::unexpected(err.value());
        buf.resize(out.size);
        return buf;
    }

    auto update_frame_bin(const BackendState& state, const CanId& id, Dlc dlc,
                          std::span<const std::byte> data, SignalInjection signals,
                          std::size_t expected_bytes)
        -> std::expected<std::vector<std::byte>, AletheiaError> override {
        if (auto const err = payload_length_error(dlc, data))
            return std::unexpected(err.value());
        auto const frame = payload_frame(id, dlc, data);
        auto const values = signal_values(signals);
        std::vector<std::byte> buf(expected_bytes);
        detail::FfiBuffer out{.data = as_u8(buf.data()),
                              .err = nullptr,
                              .size = static_cast<std::uint32_t>(buf.size())};
        auto const status = fns_.update_frame_bin(state.get(), &frame, &values, &out);
        if (auto const err = detail::ffi_error_from_status(status, out.err, fns_.free_str))
            return std::unexpected(err.value());
        buf.resize(out.size);
        return buf;
    }

    auto extract_signals_bin(const BackendState& state, const CanId& id, Dlc dlc,
                             std::span<const std::byte> data)
        -> std::expected<std::vector<std::byte>, AletheiaError> override {
        if (auto const err = payload_length_error(dlc, data))
            return std::unexpected(err.value());
        auto const frame = payload_frame(id, dlc, data);
        detail::FfiBuffer out{.data = nullptr, .err = nullptr, .size = 0};
        auto const status = fns_.extract_signals_bin(state.get(), &frame, &out);
        if (auto const err = detail::ffi_error_from_status(status, out.err, fns_.free_str))
            return std::unexpected(err.value());
        // RAII-owned so a throwing std::vector construction (e.g. bad_alloc on
        // copy) still frees the Haskell-allocated buffer. A bare free call
        // after the copy would leak on that path.
        const std::unique_ptr<std::uint8_t, AletheiaFreeBufFn> out_guard(out.data, fns_.free_buf);
        // Guard against the degenerate case where the backend signalled
        // success but produced a null buffer: constructing std::span from a
        // null pointer with non-zero size is undefined behaviour
        // ([span.cons]/3). A zero-length extraction is a legal successful
        // response — return an empty payload instead of reading through null.
        if (out.data == nullptr)
            return std::vector<std::byte>{};
        const std::span<const std::byte> out_bytes(as_byte(out.data), out.size);
        return std::vector<std::byte>(out_bytes.begin(), out_bytes.end());
    }

protected:
    // Reached only through BackendState, which is the sole owner of the state
    // this releases.
    void close(void* state) noexcept override { fns_.close(state); }
};

} // anonymous namespace

static auto kernel_entries(detail::SymbolResolver& resolver) -> KernelEntries {
    return KernelEntries{
        .init = resolver.get<AletheiaInitFn>("aletheia_init"),
        .process = resolver.get<AletheiaProcessFn>("aletheia_process"),
        .send_frame = resolver.get<AletheiaSendFrameFn>("aletheia_send_frame"),
        .free_str = resolver.get<AletheiaFreeStrFn>("aletheia_free_str"),
        .close = resolver.get<AletheiaCloseFn>("aletheia_close"),
        .send_error = resolver.get<AletheiaSendErrorFn>("aletheia_send_error"),
        .send_remote = resolver.get<AletheiaSendRemoteFn>("aletheia_send_remote"),
        .start_stream = resolver.get<AletheiaNoArgFn>("aletheia_start_stream"),
        .end_stream = resolver.get<AletheiaNoArgFn>("aletheia_end_stream"),
        .format_dbc = resolver.get<AletheiaNoArgFn>("aletheia_format_dbc"),
        .extract_signals = resolver.get<AletheiaExtractFn>("aletheia_extract_signals"),
        .build_frame_bin = resolver.get<AletheiaFrameBinFn>("aletheia_build_frame_bin"),
        .update_frame_bin = resolver.get<AletheiaFrameBinFn>("aletheia_update_frame_bin"),
        .extract_signals_bin = resolver.get<AletheiaExtractBinFn>("aletheia_extract_signals_bin"),
        .free_buf = resolver.get<AletheiaFreeBufFn>("aletheia_free_buf"),
    };
}

// A refused open loads nothing: the library is owned by a guard until the
// start has run on it, so a refusal at any step closes what was opened. The
// start's own entries are resolved first, its start entry leading, so a
// library carrying none of the kernel's is refused naming that entry; the core
// count is checked against the CPUs the opened library's runtime counts,
// `nullopt` asking for the count running. Registering the path comes last, so
// the search never points at a path this call refused.
static auto open_ffi_backend(const std::filesystem::path& lib_path, std::optional<int> rts_cores)
    -> Result<std::unique_ptr<IBackend>> {
    auto opened = detail::open_kernel(lib_path);
    if (!opened)
        return std::unexpected(detail::error_of(opened));
    detail::SymbolResolver resolver{opened.value().get()};
    auto const runtime = detail::runtime_symbols(resolver);
    auto const entries = kernel_entries(resolver);
    return resolver.resolved(runtime)
        .and_then([rts_cores](const detail::RuntimeSymbols& symbols) {
            return detail::start_runtime_on(symbols, rts_cores);
        })
        .transform([&](const detail::StartOutcome& outcome) -> std::unique_ptr<IBackend> {
            auto backend =
                std::make_unique<FfiBackend>(opened.value().release(), entries, outcome.mismatch);
            detail::register_default_lib_path(lib_path);
            return backend;
        });
}

auto make_ffi_backend(const std::filesystem::path& lib_path) -> Result<std::unique_ptr<IBackend>> {
    return open_ffi_backend(lib_path, std::nullopt);
}

auto make_ffi_backend(const std::filesystem::path& lib_path, int rts_cores)
    -> Result<std::unique_ptr<IBackend>> {
    return open_ffi_backend(lib_path, rts_cores);
}

auto make_ffi_backend_from_env() -> Result<std::unique_ptr<IBackend>> {
    return detail::env_library_path("make_ffi_backend(path)")
        .and_then([](const std::filesystem::path& lib) { return make_ffi_backend(lib); });
}

auto make_ffi_backend_from_env(int rts_cores) -> Result<std::unique_ptr<IBackend>> {
    return detail::env_library_path("make_ffi_backend(path)")
        .and_then([rts_cores](const std::filesystem::path& lib) {
            return make_ffi_backend(lib, rts_cores);
        });
}

} // namespace aletheia
