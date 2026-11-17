// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
#pragma once

// One session of the real kernel driven through its backend, as a client
// drives it: a test sends the commands and reads each reply with the reader
// it chooses, where a client applies the one each command's answer takes.

#include <aletheia/backend.hpp>

#include <memory>
#include <string>
#include <string_view>

#include "find_lib.hpp"
#include "required.hpp"

namespace aletheia::test {

// The backend over the real library and one state of it, closed before the
// backend that handed it out.
class KernelSession {
public:
    KernelSession()
        : backend_(required(make_ffi_backend(find_lib())))
        , state_(required(backend_->init())) {}

    [[nodiscard]] auto backend() const -> IBackend& { return *backend_; }
    [[nodiscard]] auto state() const -> BackendState const& { return state_; }

    // The kernel's reply to the JSON command `command`.
    [[nodiscard]] auto process(std::string_view command) const -> std::string {
        return required(backend_->process(state_, command));
    }

private:
    std::unique_ptr<IBackend> backend_;
    BackendState state_;
};

} // namespace aletheia::test
