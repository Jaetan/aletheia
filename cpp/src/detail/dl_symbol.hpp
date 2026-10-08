// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// The dynamic loader's answers, read one way by both loaders: the backend
// resolving the kernel's entries and the renderer resolving its three. dlsym
// answers null for a symbol the library lacks, and dlerror holds the loader's
// text for the failure just made; POSIX lets dlerror answer null once that
// text has been read, and when the loader set none, so a refusal built from
// it never reads a null.
#pragma once

#include <expected>
#include <string>

namespace aletheia::detail {

// The text dlerror holds, or a fixed phrase where it holds none.
[[nodiscard]] auto dl_error_text() -> std::string;

// The symbol `name` of the library `handle` opened, or `name` with what the
// loader says of its absence.
[[nodiscard]] auto dl_symbol(void* handle, const char* name) -> std::expected<void*, std::string>;

} // namespace aletheia::detail
