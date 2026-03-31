// FFI backend — loads libaletheia-ffi.so via dlopen.
#include <aletheia/backend.hpp>

#include <dlfcn.h>

#include <array>
#include <cstdint>
#include <iostream>
#include <memory>
#include <mutex>
#include <stdexcept>
#include <string>
#include <variant>

namespace aletheia {

namespace {

using HsInitFn = void (*)(int*, char***);
using AletheiaInitFn = void* (*)();
using AletheiaProcessFn = char* (*)(void*, const char*);
using AletheiaSendFrameFn = char* (*)(void*, std::uint64_t, std::uint32_t, std::uint8_t,
                                      std::uint8_t, const std::uint8_t*, std::uint8_t);
using AletheiaFreeStrFn = void (*)(char*);
using AletheiaCloseFn = void (*)(void*);

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

    template<typename Fn>
    static auto load_sym(void* handle, const char* name) -> Fn {
        auto* sym = dlsym(handle, name);
        if (sym == nullptr)
            throw std::runtime_error(std::string("dlsym failed for ") + name + ": " + dlerror());
        return reinterpret_cast<Fn>(sym);
    }

public:
    explicit FfiBackend(const std::filesystem::path& lib_path, int rts_cores)
        : handle_(dlopen(lib_path.c_str(), RTLD_NOW | RTLD_LOCAL)) {
        if (handle_ == nullptr)
            throw std::runtime_error(std::string("dlopen failed: ") + dlerror());

        try {
            auto hs_init = load_sym<HsInitFn>(handle_, "hs_init");
            init_fn_ = load_sym<AletheiaInitFn>(handle_, "aletheia_init");
            process_fn_ = load_sym<AletheiaProcessFn>(handle_, "aletheia_process");
            send_frame_fn_ = load_sym<AletheiaSendFrameFn>(handle_, "aletheia_send_frame");
            free_str_fn_ = load_sym<AletheiaFreeStrFn>(handle_, "aletheia_free_str");
            close_fn_ = load_sym<AletheiaCloseFn>(handle_, "aletheia_close");

            // Initialize GHC RTS (once per process, never finalized).
            auto& rts = rts_state();
            const std::lock_guard lock(rts.mu);
            if (!rts.initialized) {
                if (rts_cores > 1) {
                    auto n_arg = "-N" + std::to_string(rts_cores);
                    std::array<const char*, 4> args = {"aletheia", "+RTS", n_arg.c_str(), "-RTS"};
                    auto argc = static_cast<int>(args.size());
                    // NOLINTNEXTLINE(cppcoreguidelines-pro-type-const-cast)
                    auto* argv = const_cast<char**>(args.data());
                    hs_init(&argc, &argv);
                } else {
                    hs_init(nullptr, nullptr);
                }
                rts.cores = rts_cores;
                rts.initialized = true;
            } else if (rts_cores != rts.cores) {
                std::cerr << "Warning: GHC RTS already initialized with " << rts.cores
                          << " core(s); ignoring rts_cores=" << rts_cores
                          << ". Set rts_cores on the first "
                          << "make_ffi_backend() call in the process.\n";
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

    auto init() -> void* override { return init_fn_(); }

    auto process(void* state, std::string_view input) -> std::string override {
        // The Agda core expects a null-terminated string.
        const std::string input_str{input};
        char* result = process_fn_(state, input_str.c_str());
        if (result == nullptr)
            throw std::runtime_error("aletheia_process returned null");
        // RAII guard ensures free_str_fn_ runs even if string construction throws.
        auto deleter = [this](char* p) { free_str_fn_(p); };
        const std::unique_ptr<char, decltype(deleter)> guard{result, deleter};
        return std::string{result};
    }

    auto send_frame_binary(void* state, Timestamp ts, const CanId& id, Dlc dlc,
                           std::span<const std::byte> data) -> std::string override {
        const auto timestamp = static_cast<std::uint64_t>(ts.count());
        const auto can_id =
            std::visit([](const auto& v) -> std::uint32_t { return v.value(); }, id);
        const auto extended =
            static_cast<std::uint8_t>(std::holds_alternative<ExtendedId>(id) ? 1 : 0);
        const auto dlc_val = dlc.value();
        const auto data_len = static_cast<std::uint8_t>(data.size());

        char* result = send_frame_fn_(state, timestamp, can_id, extended, dlc_val,
                                      // NOLINTNEXTLINE(cppcoreguidelines-pro-type-reinterpret-cast)
                                      reinterpret_cast<const std::uint8_t*>(data.data()), data_len);
        if (result == nullptr)
            throw std::runtime_error("aletheia_send_frame returned null");
        auto deleter = [this](char* p) { free_str_fn_(p); };
        const std::unique_ptr<char, decltype(deleter)> guard{result, deleter};
        return std::string{result};
    }

    void close(void* state) override { close_fn_(state); }
};

} // anonymous namespace

auto make_ffi_backend(const std::filesystem::path& lib_path, int rts_cores)
    -> std::unique_ptr<IBackend> {
    return std::make_unique<FfiBackend>(lib_path, rts_cores);
}

} // namespace aletheia
