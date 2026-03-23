// SPDX-License-Identifier: BSD-2-Clause
#pragma once

#include <filesystem>
#include <memory>
#include <string>
#include <string_view>

namespace aletheia {

// ---------------------------------------------------------------------------
// Backend interface (dependency injection for testability)
// ---------------------------------------------------------------------------

class IBackend {
public:
    virtual ~IBackend() = default;

    IBackend(const IBackend&) = delete;
    IBackend& operator=(const IBackend&) = delete;
    IBackend(IBackend&&) = delete;
    IBackend& operator=(IBackend&&) = delete;

    virtual auto init() -> void* = 0;
    virtual auto process(void* state, std::string_view input) -> std::string = 0;
    virtual auto close(void* state) -> void = 0;

protected:
    IBackend() = default;
};

// Production: loads libaletheia-ffi.so via dlopen
auto make_ffi_backend(const std::filesystem::path& lib_path) -> std::unique_ptr<IBackend>;

// Test: returns canned responses
auto make_mock_backend() -> std::unique_ptr<IBackend>;

} // namespace aletheia
