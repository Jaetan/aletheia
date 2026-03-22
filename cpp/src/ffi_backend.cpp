// FFI backend — loads libaletheia-ffi.so via dlopen.
#include <aletheia/backend.hpp>

#include <dlfcn.h>

#include <memory>
#include <stdexcept>
#include <string>

namespace aletheia {

namespace {

using HsInitFn = void (*)(int*, char***);
using AletheiaInitFn = void* (*)();
using AletheiaProcessFn = char* (*)(void*, const char*);
using AletheiaFreeStrFn = void (*)(char*);
using AletheiaCloseFn = void (*)(void*);

class FfiBackend : public IBackend {
    void* handle_ = nullptr;
    AletheiaInitFn init_fn_ = nullptr;
    AletheiaProcessFn process_fn_ = nullptr;
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
    explicit FfiBackend(const std::filesystem::path& lib_path)
        : handle_(dlopen(lib_path.c_str(), RTLD_NOW | RTLD_LOCAL)) {
        if (handle_ == nullptr)
            throw std::runtime_error(std::string("dlopen failed: ") + dlerror());

        try {
            auto hs_init = load_sym<HsInitFn>(handle_, "hs_init");
            init_fn_ = load_sym<AletheiaInitFn>(handle_, "aletheia_init");
            process_fn_ = load_sym<AletheiaProcessFn>(handle_, "aletheia_process");
            free_str_fn_ = load_sym<AletheiaFreeStrFn>(handle_, "aletheia_free_str");
            close_fn_ = load_sym<AletheiaCloseFn>(handle_, "aletheia_close");

            // Initialize GHC RTS (ref-counted internally, safe to call multiple times)
            hs_init(nullptr, nullptr);
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

    void close(void* state) override { close_fn_(state); }
};

} // anonymous namespace

auto make_ffi_backend(const std::filesystem::path& lib_path) -> std::unique_ptr<IBackend> {
    return std::make_unique<FfiBackend>(lib_path);
}

} // namespace aletheia
