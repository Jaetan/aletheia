// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
// parse_dbc_text passes text at its cap to the backend: the bound refuses what
// is past it and nothing at it. The text is the cap's worth of bytes, which the
// client copies into a command, so the mutation binary runs this test after
// every other ([costly], tools/mutation_cpp_order.py).

#include <aletheia/client.hpp>
#include <aletheia/error.hpp>
#include <aletheia/limits.hpp>

#include "detail/mock_backend.hpp"
#include "required.hpp"

#include <catch2/catch_test_macros.hpp>

#include <memory>
#include <stop_token>
#include <string>
#include <utility>

using aletheia::test::required;

TEST_CASE("parse_dbc_text passes text at the cap to the backend", "[input_bounds][costly]") {
    auto mock = std::make_unique<aletheia::MockBackend>();
    auto const* mock_ptr = mock.get();
    mock->queue_response(R"({"status": "error", "message": "unparsed"})");
    auto client = required(aletheia::AletheiaClient::create(std::move(mock)));

    std::string const at_cap(aletheia::max_dbc_text_bytes, 'x');
    auto const result = client.parse_dbc_text(std::stop_token{}, at_cap);
    // The backend, not the bound, answered.
    REQUIRE(mock_ptr->captured().size() == 1);
    REQUIRE_FALSE(result.has_value());
    CHECK(result.error().kind() != aletheia::ErrorKind::InputBoundExceeded);
}
