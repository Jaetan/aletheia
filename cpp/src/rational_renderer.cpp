// SPDX-License-Identifier: BSD-2-Clause
//
// Namespace-level registration for the cross-binding-identical Rational
// pretty-printer (R20 cluster Y stage 2).
//
// Production code paths flow through `FfiBackend`, which registers the
// loaded library's `aletheia_format_rational` and `aletheia_free_str`
// function pointers via `set_renderer_fns`.  The free function
// `format_value(const Rational&)` (in `enrich.cpp`) consults these on
// every call: when registered, the FFI is used; otherwise it falls
// back to the local C++ algorithm — same byte output, but kept in
// lockstep by the test corpus rather than by the kernel.  The fallback
// path keeps tests that don't instantiate an `FfiBackend` (e.g. the
// `[enrich][rational]` Catch2 cases) usable.

#include <aletheia/detail/rational_renderer.hpp>

#include <atomic>
#include <cstdint>
#include <optional>
#include <string>

namespace aletheia::detail {

using FormatRationalFn = char* (*)(std::int64_t, std::int64_t);
using FreeStrFn = void (*)(char*);

namespace {

// Function-local static atomics for the lock-free fast path read in
// `try_format_rational_ffi`.  Wrapped in accessors so they aren't
// flagged as non-const globals (cppcoreguidelines-avoid-non-const-
// global-variables); function-static initialisation is thread-safe
// per [stmt.dcl]/4 (C++11+ "magic statics").  Writes happen at most
// once per FfiBackend construction (rare); reads happen on every
// predicate render.
auto format_fn_ref() noexcept -> std::atomic<FormatRationalFn>& {
    static std::atomic<FormatRationalFn> fn{nullptr};
    return fn;
}

auto free_fn_ref() noexcept -> std::atomic<FreeStrFn>& {
    static std::atomic<FreeStrFn> fn{nullptr};
    return fn;
}

} // namespace

void set_renderer_fns(void* format_fn, void* free_fn) noexcept {
    // NOLINTNEXTLINE(cppcoreguidelines-pro-type-reinterpret-cast)
    format_fn_ref().store(reinterpret_cast<FormatRationalFn>(format_fn), std::memory_order_release);
    // NOLINTNEXTLINE(cppcoreguidelines-pro-type-reinterpret-cast)
    free_fn_ref().store(reinterpret_cast<FreeStrFn>(free_fn), std::memory_order_release);
}

auto try_format_rational_ffi(std::int64_t num, std::int64_t denom) -> std::optional<std::string> {
    auto* fmt = format_fn_ref().load(std::memory_order_acquire);
    auto* free = free_fn_ref().load(std::memory_order_acquire);
    if (fmt == nullptr || free == nullptr) {
        return std::nullopt;
    }
    char* raw = fmt(num, denom);
    if (raw == nullptr) {
        // Defensive: the Agda function always returns a non-null
        // CString (denom = 0 returns the literal "0").  Reach here
        // only on a catastrophic Haskell-side allocation failure.
        return std::string{"0"};
    }
    std::string out{raw};
    free(raw);
    return out;
}

} // namespace aletheia::detail
