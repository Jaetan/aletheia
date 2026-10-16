// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// A library the stability harness's process tests preload into the harness,
// so a test fails a snapshot, leaks a descriptor or fails a measured cycle
// without privilege. It lets as many opens of /proc/self/status through as
// ALETHEIA_TEST_STATUS_OPENS says and refuses every later one as access
// denied; with the variable unset it refuses none. The open
// ALETHEIA_TEST_STATUS_LEAK numbers, counting from zero, first opens /dev/null
// and never closes it. With ALETHEIA_TEST_REFUSE_LATE_LOADS set, every dlopen
// made after the first open of the file, the opening snapshot's, is refused,
// so the warm-up loads the kernel and the first measured cycle cannot. The
// harness reads the file through an ifstream, which the standard library opens
// with fopen. Only the snapshots open the file, on the harness's one thread
// that takes them and loads the kernel, so the count needs no lock.

#include "detail/ffi_abi.hpp"
#include "stability_snapshot.hpp"

#include <dlfcn.h>

#include <cerrno>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <optional>
#include <string_view>

using OpenFn = std::FILE* (*)(const char*, const char*);
using LoadFn = void* (*)(const char*, int);

// The count the variable `name` holds, read as the harness reads a whole
// number, or none when it is unset. A value that is not a whole number ends the
// process, so a test that set it wrongly fails rather than running a harness
// nothing was done to.
static auto count_from(const char* name) -> std::optional<std::int64_t> {
    const char* const env = std::getenv(name);
    if (env == nullptr)
        return std::nullopt;
    auto const value = aletheia::bench::whole_number(env);
    if (!value)
        std::abort();
    return value;
}

// The opens of /proc/self/status made so far.
static auto status_opens() -> std::int64_t& {
    static std::int64_t made = 0;
    return made;
}

// Opens `path` through the next library's fopen, the C library's, unless
// `path` is the status file and the opens it allows are spent.
static auto open_through(const char* path, const char* mode) -> std::FILE* {
    auto const real = aletheia::detail::symbol_as<OpenFn>(dlsym(RTLD_NEXT, "fopen"));
    if (path == nullptr || std::string_view{path} != "/proc/self/status")
        return real(path, mode);
    auto const made = status_opens()++;
    if (auto const leak = count_from("ALETHEIA_TEST_STATUS_LEAK"); leak == made)
        static_cast<void>(real("/dev/null", "re"));
    if (auto const allowed = count_from("ALETHEIA_TEST_STATUS_OPENS");
        allowed && made >= *allowed) {
        errno = EACCES;
        return nullptr;
    }
    return real(path, mode);
}

// The replacement, exported under the name of the function it replaces. The
// alias declares that name with the parameters' names commented out, since a
// definition would have to name them as the C library's declaration does.
extern "C" auto aletheia_test_fopen(const char* path, const char* mode) -> std::FILE* {
    return open_through(path, mode);
}

extern "C" [[gnu::alias("aletheia_test_fopen")]] auto fopen(const char* /*path*/,
                                                            const char* /*mode*/) -> std::FILE*;

// Loads `path` through the next library's dlopen, the C library's, unless late
// loads are refused and the status file has been opened.
static auto load_through(const char* path, int flags) -> void* {
    if (std::getenv("ALETHEIA_TEST_REFUSE_LATE_LOADS") != nullptr && status_opens() > 0)
        return nullptr;
    auto const real = aletheia::detail::symbol_as<LoadFn>(dlsym(RTLD_NEXT, "dlopen"));
    return real(path, flags);
}

// The replacement for dlopen, exported as fopen's is.
extern "C" auto aletheia_test_dlopen(const char* path, int flags) -> void* {
    return load_through(path, flags);
}

extern "C" [[gnu::alias("aletheia_test_dlopen")]] auto dlopen(const char* /*file*/,
                                                              int /*mode*/) noexcept -> void*;
