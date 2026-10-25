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

auto open_kernel(const std::filesystem::path& lib_path) -> KernelLibrary {
    if (lib_path.empty())
        throw AletheiaException(AletheiaError{
            ErrorKind::Validation, "library path is empty: pass the path of libaletheia-ffi.so"});
    KernelLibrary opened{dlopen(lib_path.c_str(), RTLD_NOW | RTLD_LOCAL)};
    if (opened == nullptr)
        throw AletheiaException(AletheiaError{ErrorKind::Ffi, "dlopen failed: " + dl_error_text()});
    // The version first: a library laid out for another ABI is refused
    // before any other entry is resolved or its runtime is started.
    if (auto refusal = abi_version_refusal(symbol_as<std::uint32_t (*)()>(
            required_symbol(opened.get(), "aletheia_abi_version"))()))
        throw AletheiaException(AletheiaError{ErrorKind::Ffi, std::move(refusal).value()});
    return opened;
}

// The refusal is raised from the error branch alone, so the one place a missing
// symbol is told from a found one is dl_symbol, not a test of its answer
// repeated once per entry type.
auto required_symbol(void* handle, const char* name) -> void* {
    return dl_symbol(handle, name)
        .or_else([](std::string detail) -> std::expected<void*, std::string> {
            throw AletheiaException(
                AletheiaError{ErrorKind::Ffi, "dlsym failed for " + std::move(detail)});
        })
        .value();
}

auto runtime_symbols(void* handle) -> RuntimeSymbols {
    auto const sym = [handle](std::string_view name) {
        return required_symbol(handle, std::string{name}.c_str());
    };
    return RuntimeSymbols{
        .hs_init = symbol_as<void (*)(int*, char***)>(sym(rts_init_symbol)),
        .processors = symbol_as<std::uint32_t (*)()>(sym(rts_processors_symbol)),
        .entries = RuntimeEntries{
            .allocated_bytes = symbol_as<std::uint64_t (*)()>(sym("aletheia_allocated_bytes")),
            .format_rational =
                symbol_as<char* (*)(const FfiRational*)>(sym("aletheia_format_rational")),
            .free_str = symbol_as<void (*)(char*)>(sym("aletheia_free_str")),
            .parse_decimal = symbol_as<std::int8_t (*)(const FfiText*, FfiDecimal*)>(
                sym("aletheia_parse_decimal")),
        }};
}

auto start_runtime_on(const RuntimeSymbols& symbols, std::optional<int> cores) -> StartOutcome {
    auto& rts = rts_init_state();
    const std::scoped_lock lock(rts.mu);
    auto const asked = cores.value_or(rts.initialized ? rts.cores : rts_default_cores);
    if (auto refusal = core_count_refusal(asked, static_cast<int>(symbols.processors())))
        throw AletheiaException(AletheiaError{ErrorKind::Validation, std::move(refusal).value()});
    if (rts.initialized)
        return StartOutcome{.started = false, .mismatch = rts_cores_mismatch(asked, rts.cores)};
    // The argv always carries the containment heap cap.
    // hs_init_with_rtsopts may retain argv for the whole process
    // lifetime, so the backing storage must outlive this call:
    // function-local statics give process-lifetime storage without
    // a raw owning `new`, and the lines below run exactly once
    // (guarded by rts.initialized under rts.mu), so their
    // runtime-valued initialisers evaluate once.
    const char* const override_env = std::getenv(std::string{rts_override_env}.c_str());
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

auto env_library_path(std::string_view counted_twin) -> std::filesystem::path {
    // std::getenv answers null when the variable is unset and "" when it is
    // set empty; both are refused here, naming the variable.
    const char* env = std::getenv("ALETHEIA_LIB");
    if (env == nullptr || *env == '\0')
        throw AletheiaException(AletheiaError{
            ErrorKind::Validation,
            "ALETHEIA_LIB is not set: set it to the path of libaletheia-ffi.so, or call " +
                std::string{counted_twin}});
    return std::filesystem::path{env};
}

} // namespace aletheia::detail

namespace aletheia {

auto start_runtime(const std::filesystem::path& lib, int cores)
    -> std::optional<std::pair<int, int>> {
    auto opened = detail::open_kernel(lib);
    auto const outcome = detail::start_runtime_on(detail::runtime_symbols(opened.get()), cores);
    detail::register_default_lib_path(lib);
    // The library the runtime started on stays open, since the runtime owns
    // threads that reference it; any other was opened only to be read.
    if (outcome.started)
        std::ignore = opened.release();
    return outcome.mismatch;
}

auto start_runtime_from_env(int cores) -> std::optional<std::pair<int, int>> {
    return start_runtime(detail::env_library_path("start_runtime(path, cores)"), cores);
}

auto allocated_bytes() -> std::optional<std::uint64_t> {
    auto& rts = detail::rts_init_state();
    auto const entry = [&rts] {
        const std::scoped_lock lock(rts.mu);
        return rts.entries.allocated_bytes;
    }();
    if (entry == nullptr)
        return std::nullopt;
    return entry();
}

} // namespace aletheia
