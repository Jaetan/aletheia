// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// The binding answers every error through Result but one: std::bad_alloc is
// thrown. A handler that turns what it caught into an error calls this first,
// so the exhaustion it caught leaves as it came.
#pragma once

#include <exception>
#include <new>

namespace aletheia::detail {

// Rethrows the exception being handled when `caught` is std::bad_alloc.
inline void rethrow_if_bad_alloc(std::exception const& caught) {
    if (dynamic_cast<std::bad_alloc const*>(&caught) != nullptr)
        throw;
}

} // namespace aletheia::detail
