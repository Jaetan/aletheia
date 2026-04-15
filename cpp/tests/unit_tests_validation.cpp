// SPDX-License-Identifier: BSD-2-Clause
// Unit tests: payload length / timestamp / bytes_to_dlc / Rational validation.
//
// Payload-length mismatches, negative-timestamp rejection (send_frame,
// send_error, send_remote), bytes_to_dlc CAN 2.0B / CAN-FD coverage, and
// Rational comparison operators.
#include <catch2/catch_test_macros.hpp>
#include <catch2/matchers/catch_matchers.hpp>
#include <catch2/matchers/catch_matchers_string.hpp>

#include "detail/mock_backend.hpp"
#include <aletheia/aletheia.hpp>

#include <cstddef>
#include <memory>
#include <string>
#include <utility>
#include <variant>
#include <vector>

using namespace aletheia;
using Catch::Matchers::ContainsSubstring;

// ===========================================================================
// Payload validation tests
// ===========================================================================

TEST_CASE("send_frame rejects payload length mismatch", "[client][validation]") {
    auto mock = std::make_unique<MockBackend>();
    AletheiaClient client(std::move(mock));

    auto id = CanId{StandardId::create(0x100).value()};
    auto dlc = Dlc::create(8).value(); // expects 8 bytes
    FramePayload short_data(3, std::byte{0});
    auto result = client.send_frame(Timestamp{1'000'000}, id, dlc, short_data);

    CHECK_FALSE(result.has_value());
    CHECK(result.error().kind() == ErrorKind::Validation);
    CHECK_THAT(std::string{result.error().message()}, ContainsSubstring("payload length 3"));
    CHECK_THAT(std::string{result.error().message()}, ContainsSubstring("expected 8 bytes"));
}

TEST_CASE("extract_signals rejects payload length mismatch", "[client][validation]") {
    auto mock = std::make_unique<MockBackend>();
    AletheiaClient client(std::move(mock));

    auto id = CanId{StandardId::create(0x100).value()};
    auto dlc = Dlc::create(8).value();
    FramePayload long_data(16, std::byte{0}); // 16 bytes but DLC 8 expects 8
    auto result = client.extract_signals(id, dlc, long_data);

    CHECK_FALSE(result.has_value());
    CHECK(result.error().kind() == ErrorKind::Validation);
}

TEST_CASE("update_frame rejects payload length mismatch", "[client][validation]") {
    auto mock = std::make_unique<MockBackend>();
    AletheiaClient client(std::move(mock));

    auto id = CanId{StandardId::create(0x100).value()};
    auto dlc = Dlc::create(8).value();
    FramePayload bad_data(5, std::byte{0});
    std::vector<SignalValue> signals{{SignalName{"S"}, PhysicalValue{1.0}}};
    auto result = client.update_frame(id, dlc, bad_data, signals);

    CHECK_FALSE(result.has_value());
    CHECK(result.error().kind() == ErrorKind::Validation);
}

TEST_CASE("send_frame accepts correct payload length", "[client][validation]") {
    auto mock = std::make_unique<MockBackend>();
    mock->queue_response(R"({"status": "ack"})");
    AletheiaClient client(std::move(mock));

    auto id = CanId{StandardId::create(0x100).value()};
    auto dlc = Dlc::create(8).value();
    FramePayload data(8, std::byte{0}); // exactly 8 bytes for DLC 8
    auto result = client.send_frame(Timestamp{1'000'000}, id, dlc, data);

    REQUIRE(result.has_value());
    CHECK(std::holds_alternative<Ack>(*result));
}

TEST_CASE("send_frame accepts CAN-FD payload", "[client][validation]") {
    auto mock = std::make_unique<MockBackend>();
    mock->queue_response(R"({"status": "ack"})");
    AletheiaClient client(std::move(mock));

    auto id = CanId{StandardId::create(0x100).value()};
    auto dlc = Dlc::create(15).value(); // DLC 15 = 64 bytes
    FramePayload data(64, std::byte{0});
    auto result = client.send_frame(Timestamp{1'000'000}, id, dlc, data);

    REQUIRE(result.has_value());
    CHECK(std::holds_alternative<Ack>(*result));
}

// ===========================================================================
// Negative timestamp validation test
// ===========================================================================

TEST_CASE("send_frame rejects negative timestamp", "[client][validation]") {
    auto mock = std::make_unique<MockBackend>();
    AletheiaClient client(std::move(mock));

    auto id = CanId{StandardId::create(0x100).value()};
    auto dlc = Dlc::create(8).value();
    FramePayload data(8, std::byte{0});
    auto result = client.send_frame(Timestamp{-1000}, id, dlc, data);

    CHECK_FALSE(result.has_value());
    CHECK(result.error().kind() == ErrorKind::Validation);
    CHECK_THAT(std::string{result.error().message()}, ContainsSubstring("non-negative"));
}

TEST_CASE("send_error succeeds with mock backend", "[client][validation]") {
    auto mock = std::make_unique<MockBackend>();
    AletheiaClient client(std::move(mock));
    auto result = client.send_error(Timestamp{1'000'000});
    CHECK(result.has_value());
}

TEST_CASE("send_error rejects negative timestamp", "[client][validation]") {
    auto mock = std::make_unique<MockBackend>();
    AletheiaClient client(std::move(mock));
    auto result = client.send_error(Timestamp{-1000});
    CHECK_FALSE(result.has_value());
    CHECK(result.error().kind() == ErrorKind::Validation);
    CHECK_THAT(std::string{result.error().message()}, ContainsSubstring("non-negative"));
}

TEST_CASE("send_remote succeeds with mock backend", "[client][validation]") {
    auto mock = std::make_unique<MockBackend>();
    AletheiaClient client(std::move(mock));
    auto id = CanId{StandardId::create(0x100).value()};
    auto result = client.send_remote(Timestamp{1'000'000}, id);
    CHECK(result.has_value());
}

TEST_CASE("send_remote rejects negative timestamp", "[client][validation]") {
    auto mock = std::make_unique<MockBackend>();
    AletheiaClient client(std::move(mock));
    auto id = CanId{StandardId::create(0x100).value()};
    auto result = client.send_remote(Timestamp{-1000}, id);
    CHECK_FALSE(result.has_value());
    CHECK(result.error().kind() == ErrorKind::Validation);
    CHECK_THAT(std::string{result.error().message()}, ContainsSubstring("non-negative"));
}

// ===========================================================================
// bytes_to_dlc error paths
// ===========================================================================

TEST_CASE("bytes_to_dlc valid CAN 2.0B sizes", "[types]") {
    auto r7 = bytes_to_dlc(7);
    REQUIRE(r7.has_value());
    CHECK(r7->value() == 7);

    auto r8 = bytes_to_dlc(8);
    REQUIRE(r8.has_value());
    CHECK(r8->value() == 8);
}

TEST_CASE("bytes_to_dlc valid CAN-FD sizes", "[types]") {
    auto r12 = bytes_to_dlc(12);
    REQUIRE(r12.has_value());
    CHECK(r12->value() == 9);

    auto r64 = bytes_to_dlc(64);
    REQUIRE(r64.has_value());
    CHECK(r64->value() == 15);
}

TEST_CASE("bytes_to_dlc invalid sizes return error", "[types]") {
    auto r9 = bytes_to_dlc(9);
    REQUIRE_FALSE(r9.has_value());
    CHECK_THAT(r9.error(), ContainsSubstring("invalid DLC"));

    auto r65 = bytes_to_dlc(65);
    REQUIRE_FALSE(r65.has_value());
    CHECK_THAT(r65.error(), ContainsSubstring("invalid DLC"));
}

// ===========================================================================
// Rational comparison
// ===========================================================================

TEST_CASE("Rational operator<=> and operator==", "[types]") {
    Rational a{1, 2};  // 0.5
    Rational b{2, 4};  // 0.5
    Rational c{3, 4};  // 0.75
    Rational d{-1, 2}; // -0.5

    SECTION("equality") {
        CHECK(a == b);
        CHECK_FALSE(a == c);
    }

    SECTION("less than") {
        CHECK(a < c);
        CHECK(d < a);
        CHECK_FALSE(c < a);
    }

    SECTION("greater than") {
        CHECK(c > a);
        CHECK_FALSE(a > c);
    }

    SECTION("less than or equal") {
        CHECK(a <= b);
        CHECK(a <= c);
        CHECK_FALSE(c <= a);
    }

    SECTION("negative values") {
        Rational neg{-3, 4};
        CHECK(neg < a);
        CHECK(d == Rational{-1, 2});
    }
}
