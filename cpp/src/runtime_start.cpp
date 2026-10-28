// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// The GHC runtime's start, once per process, which `aletheia::start_runtime`
// and every FfiBackend share. The runtime is never finalised (`hs_exit` does
// not allow a second start), and the start records the entries of the library
// it started on that the renderer, the decimal parser and `allocated_bytes`
// call, so those reach the kernel through that library and open none of their
// own.

#include <aletheia/backend.hpp>
#include <aletheia/detail/checked.hpp>
#include <aletheia/detail/rational_renderer.hpp>
#include <aletheia/error.hpp>

#include "detail/dl_symbol.hpp"
#include "detail/ffi_abi.hpp"
#include "detail/ffi_logic.hpp"
#include "detail/kernel_library.hpp"
#include "detail/rts_init.hpp"
#include "detail/rts_params.hpp"

#include <dlfcn.h>

#include <algorithm>
#include <cstdint>
#include <cstdlib>
#include <expected>
#include <filesystem>
#include <mutex>
#include <optional>
#include <string>
#include <string_view>
#include <tuple>
#include <utility>
#include <vector>

namespace aletheia::detail {

void LibraryCloser::operator()(void* handle) const noexcept {
    dlclose(handle);
}

auto open_kernel(std::filesystem::path const& lib_path) -> Result<KernelLibrary> {
    if (lib_path.empty())
        return validation_refusal("library path is empty: pass the path of libaletheia-ffi.so");
    KernelLibrary opened{dlopen(lib_path.c_str(), RTLD_NOW | RTLD_LOCAL)};
    if (opened == nullptr)
        return std::unexpected(AletheiaError{ErrorKind::Ffi, "dlopen failed: " + dl_error_text()});
    // The version first: a library laid out for another ABI is refused
    // before any other entry is resolved or its runtime is started.
    SymbolResolver resolver{opened.get()};
    auto const abi_version = resolver.get<std::uint32_t (*)()>("aletheia_abi_version");
    return resolver.resolved(abi_version)
        .and_then([&opened](auto const version) -> Result<KernelLibrary> {
            if (auto refusal = abi_version_refusal(version()))
                return std::unexpected(AletheiaError{ErrorKind::Ffi, std::move(refusal).value()});
            return std::move(opened);
        });
}

auto SymbolResolver::entry(char const* name) -> void* {
    auto const found = dl_symbol(handle_, name);
    if (!found) {
        // The first entry missing is the one the refusal names.
        if (!missing_)
            missing_ = AletheiaError{ErrorKind::Ffi, "dlsym failed for " + error_of(found)};
        return nullptr;
    }
    return found.value();
}

auto runtime_symbols(SymbolResolver& resolver) -> RuntimeSymbols {
    return RuntimeSymbols{
        .hs_init = resolver.get<void (*)(int*, char***)>(std::string{rts_init_symbol}.c_str()),
        .processors = resolver.get<std::uint32_t (*)()>(std::string{rts_processors_symbol}.c_str()),
        .entries = RuntimeEntries{
            .allocated_bytes = resolver.get<std::uint64_t (*)()>("aletheia_allocated_bytes"),
            .format_rational =
                resolver.get<char* (*)(FfiRational const*)>("aletheia_format_rational"),
            .free_str = resolver.get<void (*)(char*)>("aletheia_free_str"),
            .parse_decimal = resolver.get<std::int8_t (*)(FfiText const*, FfiDecimal*)>(
                "aletheia_parse_decimal"),
        }};
}

// The runtime symbols of an opened library, or the refusal naming the first
// one missing.
static auto resolved_runtime_symbols(void* handle) -> Result<RuntimeSymbols> {
    SymbolResolver resolver{handle};
    auto const symbols = runtime_symbols(resolver);
    return resolver.resolved(symbols);
}

auto start_runtime_on(RuntimeSymbols const& symbols, std::optional<int> cores)
    -> Result<StartOutcome> {
    auto& rts = rts_init_state();
    std::scoped_lock const lock(rts.mu);
    auto const asked = cores.value_or(rts.initialized ? rts.cores : rts_default_cores);
    if (auto refusal = core_count_refusal(asked, static_cast<int>(symbols.processors())))
        return validation_refusal(std::move(refusal).value());
    if (rts.initialized)
        return StartOutcome{.started = false, .mismatch = rts_cores_mismatch(asked, rts.cores)};
    // The argv always carries the containment heap cap.
    // hs_init_with_rtsopts may retain argv for the whole process
    // lifetime, so the backing storage must outlive this call:
    // function-local statics give process-lifetime storage without
    // a raw owning `new`, and the lines below run exactly once
    // (guarded by rts.initialized under rts.mu), so their
    // runtime-valued initialisers evaluate once.
    char const* const override_env = std::getenv(std::string{rts_override_env}.c_str());
    static auto rts_argv = rts_init_args(asked, override_env != nullptr ? override_env : "");
    static auto rts_argv_ptrs = [] {
        std::vector<char*> ptrs(rts_argv.size());
        std::ranges::transform(rts_argv, ptrs.begin(), [](std::string& arg) { return arg.data(); });
        return ptrs;
    }();
    auto argc = static_cast<int>(rts_argv_ptrs.size());
    auto** argv = rts_argv_ptrs.data();
    symbols.hs_init(&argc, &argv);
    rts.cores = asked;
    rts.entries = symbols.entries;
    rts.initialized = true;
    return StartOutcome{.started = true, .mismatch = std::nullopt};
}

auto env_library_path(std::string_view counted_twin) -> Result<std::filesystem::path> {
    // std::getenv answers null when the variable is unset and "" when it is
    // set empty; both are refused here, naming the variable.
    char const* env = std::getenv("ALETHEIA_LIB");
    if (env == nullptr || *env == '\0')
        return validation_refusal(
            "ALETHEIA_LIB is not set: set it to the path of libaletheia-ffi.so, or call " +
            std::string{counted_twin});
    return std::filesystem::path{env};
}

} // namespace aletheia::detail

namespace aletheia {

auto start_runtime(std::filesystem::path const& lib, int cores)
    -> Result<std::optional<std::pair<int, int>>> {
    auto opened = detail::open_kernel(lib);
    return opened
        .and_then([](detail::KernelLibrary const& library) {
            return detail::resolved_runtime_symbols(library.get());
        })
        .and_then([cores](detail::RuntimeSymbols const& symbols) {
            return detail::start_runtime_on(symbols, cores);
        })
        .transform([&lib, &opened](detail::StartOutcome const& outcome) {
            detail::register_default_lib_path(lib);
            // The library the runtime started on stays open, since the runtime
            // owns threads that reference it; any other was opened only to be read.
            if (outcome.started)
                std::ignore = opened.value().release();
            return outcome.mismatch;
        });
}

auto start_runtime_from_env(int cores) -> Result<std::optional<std::pair<int, int>>> {
    return detail::env_library_path("start_runtime(path, cores)")
        .and_then([cores](std::filesystem::path const& lib) { return start_runtime(lib, cores); });
}

auto allocated_bytes() -> std::optional<std::uint64_t> {
    auto& rts = detail::rts_init_state();
    auto const entry = [&rts] {
        std::scoped_lock const lock(rts.mu);
        return rts.entries.allocated_bytes;
    }();
    if (entry == nullptr)
        return std::nullopt;
    return entry();
}

} // namespace aletheia
