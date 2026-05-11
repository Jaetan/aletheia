// SPDX-License-Identifier: BSD-2-Clause
// FFI backend — loads libaletheia-ffi.so via dlopen.
#include <aletheia/backend.hpp>
#include <aletheia/limits.hpp>

#include <dlfcn.h>

#include <array>
#include <cstddef>
#include <cstdint>
#include <expected>
#include <filesystem>
#include <memory>
#include <mutex>
#include <optional>
#include <span>
#include <stdexcept>
#include <string>
#include <string_view>
#include <utility>
#include <variant>
#include <vector>

namespace aletheia {

namespace {

// CAN-FD's largest payload, sourced from the public limits header (SSOT).
// R19 cluster 12 — CPP-B-7.4: this anonymous-namespace constant used to
// duplicate `aletheia::max_frame_byte_count` (also 64); now it is a thin
// alias so a future bound change at the public surface automatically
// propagates here.
constexpr std::size_t max_can_fd_payload_bytes =
    static_cast<std::size_t>(aletheia::max_frame_byte_count);

using HsInitFn = void (*)(int*, char***);
using AletheiaInitFn = void* (*)();
using AletheiaProcessFn = char* (*)(void*, const char*);
using AletheiaSendFrameFn = char* (*)(void*, std::uint64_t, std::uint32_t, std::uint8_t,
                                      std::uint8_t, const std::uint8_t*, std::uint8_t);
using AletheiaFreeStrFn = void (*)(char*);
using AletheiaCloseFn = void (*)(void*);

// CAN error/remote event endpoints.
using AletheiaSendErrorFn = char* (*)(void*, std::uint64_t);
using AletheiaSendRemoteFn = char* (*)(void*, std::uint64_t, std::uint32_t, std::uint8_t);

// Binary FFI endpoints (no JSON input serialization).
using AletheiaNoArgFn = char* (*)(void*);
using AletheiaExtractFn = char* (*)(void*, std::uint32_t, std::uint8_t, std::uint8_t,
                                    const std::uint8_t*, std::uint8_t);

// Binary output endpoints (return status code, write bytes to caller buffer).
using AletheiaBuildFrameBinFn = std::int8_t (*)(void*, std::uint32_t, std::uint8_t, std::uint8_t,
                                                std::uint32_t, const std::uint32_t*,
                                                const std::int64_t*, const std::int64_t*,
                                                std::uint8_t*, char**);
using AletheiaUpdateFrameBinFn = std::int8_t (*)(void*, std::uint32_t, std::uint8_t, std::uint8_t,
                                                 const std::uint8_t*, std::uint8_t, std::uint32_t,
                                                 const std::uint32_t*, const std::int64_t*,
                                                 const std::int64_t*, std::uint8_t*, char**);
using AletheiaExtractBinFn = std::int8_t (*)(void*, std::uint32_t, std::uint8_t, std::uint8_t,
                                             const std::uint8_t*, std::uint8_t, std::uint8_t**,
                                             std::uint32_t*, char**);
using AletheiaFreeBufFn = void (*)(std::uint8_t*);

// ---------------------------------------------------------------------------
// Byte ↔ uint8_t pointer aliasing at the FFI boundary.
//
// The C++ surface holds payloads as std::span<const std::byte> / std::vector<
// std::byte>, while the Haskell FFI signatures expect const std::uint8_t* and
// std::uint8_t*. The reinterpret_cast here is well-defined: [basic.types]
// guarantees std::byte is layout-compatible with unsigned char, and std::
// uint8_t is unsigned char on every platform we target (g++>=14, clang>=21
// on Linux x86_64/ARM64). The NOLINTs below are centralised so the FFI call
// sites stay free of noise; every byte-cast flows through these three fns.
auto as_u8(const std::byte* p) -> const std::uint8_t* {
    // NOLINTNEXTLINE(cppcoreguidelines-pro-type-reinterpret-cast)
    return reinterpret_cast<const std::uint8_t*>(p);
}

auto as_u8(std::byte* p) -> std::uint8_t* {
    // NOLINTNEXTLINE(cppcoreguidelines-pro-type-reinterpret-cast)
    return reinterpret_cast<std::uint8_t*>(p);
}

auto as_byte(const std::uint8_t* p) -> const std::byte* {
    // NOLINTNEXTLINE(cppcoreguidelines-pro-type-reinterpret-cast)
    return reinterpret_cast<const std::byte*>(p);
}

struct RTSState {
    std::mutex mu;
    bool initialized = false;
    int cores = 0;
};

auto rts_state() -> RTSState& {
    static RTSState s;
    return s;
}

class FfiBackend : public IBackend {
    void* handle_ = nullptr;
    AletheiaInitFn init_fn_ = nullptr;
    AletheiaProcessFn process_fn_ = nullptr;
    AletheiaSendFrameFn send_frame_fn_ = nullptr;
    AletheiaFreeStrFn free_str_fn_ = nullptr;
    AletheiaCloseFn close_fn_ = nullptr;
    AletheiaSendErrorFn send_error_fn_ = nullptr;
    AletheiaSendRemoteFn send_remote_fn_ = nullptr;
    AletheiaNoArgFn start_stream_fn_ = nullptr;
    AletheiaNoArgFn end_stream_fn_ = nullptr;
    AletheiaNoArgFn format_dbc_fn_ = nullptr;
    AletheiaExtractFn extract_signals_fn_ = nullptr;
    AletheiaBuildFrameBinFn build_frame_bin_fn_ = nullptr;
    AletheiaUpdateFrameBinFn update_frame_bin_fn_ = nullptr;
    AletheiaExtractBinFn extract_signals_bin_fn_ = nullptr;
    AletheiaFreeBufFn free_buf_fn_ = nullptr;
    // Populated when the backend detects that the GHC RTS was already
    // initialised with a different -N value than the caller requested.
    // Emitted by Client as the `rts.cores_mismatch` structured log event
    // with `active_cores` / `requested_cores` fields (Go + Python parity).
    std::optional<std::pair<int, int>> rts_mismatch_;

    template<typename Fn>
    static auto load_sym(void* handle, const char* name) -> Fn {
        auto* sym = dlsym(handle, name);
        if (sym == nullptr)
            throw std::runtime_error(std::string("dlsym failed for ") + name + ": " + dlerror());
        // dlsym returns void*; POSIX guarantees round-tripping through void*
        // preserves function pointers on all platforms with dlopen support.
        // NOLINTNEXTLINE(cppcoreguidelines-pro-type-reinterpret-cast)
        return reinterpret_cast<Fn>(sym);
    }

    // Wrap an FFI char* result with the standard null-check + RAII deleter
    // + std::string conversion pattern.  Throws std::runtime_error with
    // `error_msg` when result is null; otherwise materializes the C string
    // into a std::string and frees the FFI buffer via free_str_fn_.
    // R19 cluster 14 / CPP-A-1.1 — replaces 8 hand-rolled copies of this
    // pattern across process / send_frame_binary / send_error_binary /
    // send_remote_binary / start_stream_binary / end_stream_binary /
    // format_dbc_binary / extract_signals_binary.
    [[nodiscard]] auto wrap_str_result(char* result, std::string_view error_msg) -> std::string {
        if (result == nullptr)
            throw std::runtime_error(std::string{error_msg});
        auto deleter = [this](char* p) { free_str_fn_(p); };
        const std::unique_ptr<char, decltype(deleter)> guard{result, deleter};
        return std::string{result};
    }

public:
    explicit FfiBackend(const std::filesystem::path& lib_path, int rts_cores)
        : handle_(dlopen(lib_path.c_str(), RTLD_NOW | RTLD_LOCAL)) {
        if (rts_cores < 1)
            throw std::invalid_argument("rts_cores must be >= 1, got " + std::to_string(rts_cores));
        if (handle_ == nullptr)
            throw std::runtime_error(std::string("dlopen failed: ") + dlerror());

        try {
            auto hs_init = load_sym<HsInitFn>(handle_, "hs_init");
            init_fn_ = load_sym<AletheiaInitFn>(handle_, "aletheia_init");
            process_fn_ = load_sym<AletheiaProcessFn>(handle_, "aletheia_process");
            send_frame_fn_ = load_sym<AletheiaSendFrameFn>(handle_, "aletheia_send_frame");
            free_str_fn_ = load_sym<AletheiaFreeStrFn>(handle_, "aletheia_free_str");
            close_fn_ = load_sym<AletheiaCloseFn>(handle_, "aletheia_close");
            send_error_fn_ = load_sym<AletheiaSendErrorFn>(handle_, "aletheia_send_error");
            send_remote_fn_ = load_sym<AletheiaSendRemoteFn>(handle_, "aletheia_send_remote");
            start_stream_fn_ = load_sym<AletheiaNoArgFn>(handle_, "aletheia_start_stream");
            end_stream_fn_ = load_sym<AletheiaNoArgFn>(handle_, "aletheia_end_stream");
            format_dbc_fn_ = load_sym<AletheiaNoArgFn>(handle_, "aletheia_format_dbc");
            extract_signals_fn_ = load_sym<AletheiaExtractFn>(handle_, "aletheia_extract_signals");
            build_frame_bin_fn_ =
                load_sym<AletheiaBuildFrameBinFn>(handle_, "aletheia_build_frame_bin");
            update_frame_bin_fn_ =
                load_sym<AletheiaUpdateFrameBinFn>(handle_, "aletheia_update_frame_bin");
            extract_signals_bin_fn_ =
                load_sym<AletheiaExtractBinFn>(handle_, "aletheia_extract_signals_bin");
            free_buf_fn_ = load_sym<AletheiaFreeBufFn>(handle_, "aletheia_free_buf");

            // Initialize GHC RTS (once per process, never finalized).
            auto& rts = rts_state();
            const std::lock_guard lock(rts.mu);
            if (!rts.initialized) {
                if (rts_cores > 1) {
                    // hs_init requires char** (non-const) for argv. We hold the backing
                    // storage as std::string so .data() returns char* without const_cast.
                    std::string arg0 = "aletheia";
                    std::string arg1 = "+RTS";
                    std::string arg2 = "-N" + std::to_string(rts_cores);
                    std::string arg3 = "-RTS";
                    std::array<char*, 4> args = {arg0.data(), arg1.data(), arg2.data(),
                                                 arg3.data()};
                    auto argc = static_cast<int>(args.size());
                    auto* argv = args.data();
                    hs_init(&argc, &argv);
                } else {
                    hs_init(nullptr, nullptr);
                }
                rts.cores = rts_cores;
                rts.initialized = true;
            } else if (rts_cores != rts.cores) {
                rts_mismatch_ = std::make_pair(rts.cores, rts_cores);
            }
        } catch (...) {
            // RTS was never started — safe to release the library handle.
            dlclose(handle_);
            throw;
        }
    }

    // Do NOT call hs_exit() — GHC RTS does not support reinitialization.
    // Do NOT dlclose() — the RTS owns threads that reference the library.
    ~FfiBackend() override = default;

    FfiBackend(const FfiBackend&) = delete;
    FfiBackend& operator=(const FfiBackend&) = delete;
    FfiBackend(FfiBackend&&) = delete;
    FfiBackend& operator=(FfiBackend&&) = delete;

    [[nodiscard]] auto rts_mismatch_info() const -> std::optional<std::pair<int, int>> override {
        return rts_mismatch_;
    }

    auto init() -> void* override { return init_fn_(); }

    auto process(void* state, std::string_view input) -> std::string override {
        // Adversarial-input bound: synthesize an error response before
        // marshaling oversize inputs into Haskell, per AGENTS.md universal
        // rule "Adversarial-input bounds at parser surfaces".  The Agda
        // kernel enforces the same bound; this is the C++ binding's
        // short-circuit so we do not allocate an N-byte std::string + a
        // C-side null-terminated copy only to be rejected on the other
        // side.  Returns the wire-format error JSON so the existing
        // `detail::parse_*` paths translate to AletheiaError with
        // code == ErrorCode::ParseInputBoundExceeded uniformly.
        if (input.size() > aletheia::max_json_bytes) {
            // R19 cluster 8 — CPP-D-21.5: emit structured bound_kind /
            // observed / limit fields alongside `code` and `message` so
            // downstream `parse_*` paths can lift them into the
            // AletheiaError's optional InputBoundExceededError, matching
            // Python's typed `InputBoundExceededError(...)` shape and Go's
            // `*InputBoundExceededError{Kind/Observed/Limit/Code}`.
            std::string out;
            out.reserve(256);
            out.append(
                R"({"status":"error","code":"parse_input_bound_exceeded","message":"input length (bytes) )");
            out.append(std::to_string(input.size()));
            out.append(R"( exceeds limit )");
            out.append(std::to_string(aletheia::max_json_bytes));
            out.append(R"(","bound_kind":")");
            out.append(aletheia::bound_kind_input_length_bytes);
            out.append(R"(","observed":)");
            out.append(std::to_string(input.size()));
            out.append(R"(,"limit":)");
            out.append(std::to_string(aletheia::max_json_bytes));
            out.append(R"(})");
            return out;
        }
        // The Agda core expects a null-terminated string.
        const std::string input_str{input};
        return wrap_str_result(process_fn_(state, input_str.c_str()),
                               "aletheia_process returned null");
    }

    auto send_frame_binary(void* state, Timestamp ts, const CanId& id, Dlc dlc,
                           std::span<const std::byte> data) -> std::string override {
        const auto timestamp = static_cast<std::uint64_t>(ts.count());
        const auto can_id =
            std::visit([](const auto& v) -> std::uint32_t { return v.value(); }, id);
        const auto extended =
            static_cast<std::uint8_t>(std::holds_alternative<ExtendedId>(id) ? 1 : 0);
        const auto dlc_val = dlc.value();
        // CAN-FD's largest payload is 64 bytes; tighten the FFI bound so a
        // malformed caller cannot smuggle 65–255 byte payloads into the
        // Haskell core before it does its own length check.
        if (data.size() > max_can_fd_payload_bytes)
            throw std::runtime_error("data length exceeds " +
                                     std::to_string(max_can_fd_payload_bytes) +
                                     " bytes (CAN-FD max)");
        const auto data_len = static_cast<std::uint8_t>(data.size());

        return wrap_str_result(send_frame_fn_(state, timestamp, can_id, extended, dlc_val,
                                              as_u8(data.data()), data_len),
                               "aletheia_send_frame returned null");
    }

    auto send_error_binary(void* state, Timestamp ts) -> std::string override {
        const auto timestamp = static_cast<std::uint64_t>(ts.count());
        return wrap_str_result(send_error_fn_(state, timestamp),
                               "aletheia_send_error returned null");
    }

    auto send_remote_binary(void* state, Timestamp ts, const CanId& id) -> std::string override {
        const auto timestamp = static_cast<std::uint64_t>(ts.count());
        const auto can_id =
            std::visit([](const auto& v) -> std::uint32_t { return v.value(); }, id);
        const auto extended =
            static_cast<std::uint8_t>(std::holds_alternative<ExtendedId>(id) ? 1 : 0);
        return wrap_str_result(send_remote_fn_(state, timestamp, can_id, extended),
                               "aletheia_send_remote returned null");
    }

    void close(void* state) override { close_fn_(state); }

    auto start_stream_binary(void* state) -> std::string override {
        return wrap_str_result(start_stream_fn_(state), "aletheia_start_stream returned null");
    }

    auto end_stream_binary(void* state) -> std::string override {
        return wrap_str_result(end_stream_fn_(state), "aletheia_end_stream returned null");
    }

    auto format_dbc_binary(void* state) -> std::string override {
        return wrap_str_result(format_dbc_fn_(state), "aletheia_format_dbc returned null");
    }

    auto extract_signals_binary(void* state, const CanId& id, Dlc dlc,
                                std::span<const std::byte> data) -> std::string override {
        const auto can_id =
            std::visit([](const auto& v) -> std::uint32_t { return v.value(); }, id);
        const auto extended =
            static_cast<std::uint8_t>(std::holds_alternative<ExtendedId>(id) ? 1 : 0);
        const auto dlc_val = dlc.value();
        // CAN-FD's largest payload is 64 bytes; tighten the FFI bound so a
        // malformed caller cannot smuggle 65–255 byte payloads into the
        // Haskell core before it does its own length check.
        if (data.size() > max_can_fd_payload_bytes)
            throw std::runtime_error("data length exceeds " +
                                     std::to_string(max_can_fd_payload_bytes) +
                                     " bytes (CAN-FD max)");
        const auto data_len = static_cast<std::uint8_t>(data.size());

        return wrap_str_result(
            extract_signals_fn_(state, can_id, extended, dlc_val, as_u8(data.data()), data_len),
            "aletheia_extract_signals returned null");
    }

    auto build_frame_bin(void* state, const CanId& id, Dlc dlc, SignalInjection signals,
                         std::size_t expected_bytes)
        -> std::expected<std::vector<std::byte>, AletheiaError> override {
        const auto can_id =
            std::visit([](const auto& v) -> std::uint32_t { return v.value(); }, id);
        const auto extended =
            static_cast<std::uint8_t>(std::holds_alternative<ExtendedId>(id) ? 1 : 0);

        std::vector<std::byte> buf(expected_bytes);
        char* err_str = nullptr;
        const auto status = build_frame_bin_fn_(state, can_id, extended, dlc.value(), signals.count,
                                                signals.indices, signals.numerators,
                                                signals.denominators, as_u8(buf.data()), &err_str);
        if (status != 0) {
            const std::string msg = err_str != nullptr ? err_str : "Unknown error";
            if (err_str != nullptr)
                free_str_fn_(err_str);
            return std::unexpected(AletheiaError{ErrorKind::Protocol, msg});
        }
        return buf;
    }

    auto update_frame_bin(void* state, const CanId& id, Dlc dlc, std::span<const std::byte> data,
                          SignalInjection signals, std::size_t expected_bytes)
        -> std::expected<std::vector<std::byte>, AletheiaError> override {
        if (data.size() > max_can_fd_payload_bytes)
            return std::unexpected(
                AletheiaError{ErrorKind::Validation, "data length exceeds " +
                                                         std::to_string(max_can_fd_payload_bytes) +
                                                         " bytes (CAN-FD max)"});
        const auto can_id =
            std::visit([](const auto& v) -> std::uint32_t { return v.value(); }, id);
        const auto extended =
            static_cast<std::uint8_t>(std::holds_alternative<ExtendedId>(id) ? 1 : 0);
        const auto data_len = static_cast<std::uint8_t>(data.size());

        std::vector<std::byte> buf(expected_bytes);
        char* err_str = nullptr;
        const auto status = update_frame_bin_fn_(
            state, can_id, extended, dlc.value(), as_u8(data.data()), data_len, signals.count,
            signals.indices, signals.numerators, signals.denominators, as_u8(buf.data()), &err_str);
        if (status != 0) {
            const std::string msg = err_str != nullptr ? err_str : "Unknown error";
            if (err_str != nullptr)
                free_str_fn_(err_str);
            return std::unexpected(AletheiaError{ErrorKind::Protocol, msg});
        }
        return buf;
    }

    auto extract_signals_bin(void* state, const CanId& id, Dlc dlc, std::span<const std::byte> data)
        -> std::expected<std::vector<std::byte>, AletheiaError> override {
        if (data.size() > max_can_fd_payload_bytes)
            return std::unexpected(
                AletheiaError{ErrorKind::Validation, "data length exceeds " +
                                                         std::to_string(max_can_fd_payload_bytes) +
                                                         " bytes (CAN-FD max)"});
        const auto can_id =
            std::visit([](const auto& v) -> std::uint32_t { return v.value(); }, id);
        const auto extended =
            static_cast<std::uint8_t>(std::holds_alternative<ExtendedId>(id) ? 1 : 0);
        const auto data_len = static_cast<std::uint8_t>(data.size());

        std::uint8_t* out_buf = nullptr;
        std::uint32_t out_size = 0;
        char* err_str = nullptr;
        const auto status =
            extract_signals_bin_fn_(state, can_id, extended, dlc.value(), as_u8(data.data()),
                                    data_len, &out_buf, &out_size, &err_str);
        if (status != 0) {
            const std::string msg = err_str != nullptr ? err_str : "Unknown error";
            if (err_str != nullptr)
                free_str_fn_(err_str);
            return std::unexpected(AletheiaError{ErrorKind::Protocol, msg});
        }
        // RAII-owned so a throwing std::vector construction (e.g. bad_alloc on
        // copy) still frees the Haskell-allocated buffer. A bare free call
        // after the copy would leak on that path.
        const std::unique_ptr<std::uint8_t, AletheiaFreeBufFn> out_guard(out_buf, free_buf_fn_);
        // Guard against the degenerate case where the backend signalled
        // success but produced a null buffer: constructing std::span from a
        // null pointer with non-zero size is undefined behaviour
        // ([span.cons]/3). A zero-length extraction is a legal successful
        // response — return an empty payload instead of reading through null.
        if (out_buf == nullptr)
            return std::vector<std::byte>{};
        const std::span<const std::byte> out_bytes(as_byte(out_buf), out_size);
        return std::vector<std::byte>(out_bytes.begin(), out_bytes.end());
    }
};

} // anonymous namespace

auto make_ffi_backend(const std::filesystem::path& lib_path, int rts_cores)
    -> std::unique_ptr<IBackend> {
    return std::make_unique<FfiBackend>(lib_path, rts_cores);
}

} // namespace aletheia
