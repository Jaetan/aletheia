// SPDX-License-Identifier: BSD-2-Clause
#pragma once

// Internal registration surface for the cross-binding-identical
// Rational pretty-printer (R20 cluster Y stage 2).
//
// `FfiBackend` calls `set_renderer_fns` after symbol loading;
// `format_value(const Rational&)` (in `enrich.cpp`) calls
// `try_format_rational_ffi` on every render.  Returns std::nullopt
// when no FFI library has been registered (callers fall back to
// the local algorithm).

#include <cstdint>
#include <optional>
#include <string>

namespace aletheia::detail {

// Register the FFI fn pointer pair.  `format_fn` is
// ``aletheia_format_rational``; `free_fn` is ``aletheia_free_str``
// (shared with other CString-returning calls).  Both arguments are
// `void*` to keep the header free of C-FFI signature noise; the
// implementation reinterprets to the proper function pointer types.
// Thread-safe via std::atomic.
void set_renderer_fns(void* format_fn, void* free_fn) noexcept;

// Render `(num, denom)` via the registered FFI; returns
// ``std::nullopt`` if no library has been registered.
auto try_format_rational_ffi(std::int64_t num, std::int64_t denom) -> std::optional<std::string>;

} // namespace aletheia::detail
