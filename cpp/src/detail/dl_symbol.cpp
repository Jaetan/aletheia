// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

#include "dl_symbol.hpp"

#include <dlfcn.h>

#include <expected>
#include <string>

namespace aletheia::detail {

auto dl_error_text() -> std::string {
    char const* text = dlerror();
    return text != nullptr ? std::string{text} : std::string{"the loader reported no detail"};
}

auto dl_symbol(void* handle, char const* name) -> std::expected<void*, std::string> {
    auto* sym = dlsym(handle, name);
    if (sym == nullptr)
        return std::unexpected(std::string{name} + ": " + dl_error_text());
    return sym;
}

} // namespace aletheia::detail
