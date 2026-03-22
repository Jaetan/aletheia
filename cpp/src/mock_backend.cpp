// make_mock_backend() — creates a MockBackend for testing.
#include <aletheia/backend.hpp>

#include "detail/mock_backend.hpp"

namespace aletheia {

auto make_mock_backend() -> std::unique_ptr<IBackend> {
    return std::make_unique<MockBackend>();
}

} // namespace aletheia
