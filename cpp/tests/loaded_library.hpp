// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// A handle the dynamic loader returned, owned. A test that asks the loader
// whether a library is mapped, or reaches a symbol the typed API cannot
// express, takes one of these rather than pairing a call with a close.
#pragma once

#include <dlfcn.h>
#include <memory>

namespace aletheia::test {

// Closes what the loader opened. Handed to unique_ptr as its deleter, so the
// close is the destructor's and never a caller's.
struct CloseLibrary {
    void operator()(void* handle) const noexcept { dlclose(handle); }
};

// Owns a loader handle, or nothing when the call returned none.
using LoadedLibrary = std::unique_ptr<void, CloseLibrary>;

} // namespace aletheia::test
