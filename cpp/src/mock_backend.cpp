// SPDX-License-Identifier: BSD-2-Clause
// make_mock_backend() — creates a MockBackend for testing.
#include <aletheia/backend.hpp>

#include "detail/mock_backend.hpp"

#include <memory>

namespace aletheia {

auto make_mock_backend() -> std::unique_ptr<IBackend> {
    return std::make_unique<MockBackend>();
}

} // namespace aletheia
