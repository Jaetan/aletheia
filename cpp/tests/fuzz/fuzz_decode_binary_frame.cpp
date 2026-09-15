// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// libFuzzer harness for the binary extraction decoder.
// Counterpart of go FuzzDecodeBinaryFrame.
//
// The decoder is `parse_extraction_bin`, a static helper inside the client's
// translation unit, so the harness reaches it the way the rational-number
// harness reaches its own static helper: transitively, through the public
// surface. A backend derived from the test mock hands the fuzzer's bytes back
// from `extract_signals_bin`, and a DBC parsed through the same mock fills the
// signal-name lookup the client needs to take the binary path at all. The
// decoder must refuse a truncated or malformed buffer without undefined
// behaviour.
//
// Build/run: see fuzz_parse_response.cpp comment header.

#include "../../src/detail/json.hpp"
#include "../../src/detail/mock_backend.hpp"

#include <aletheia/client.hpp>
#include <aletheia/dbc.hpp>
#include <aletheia/types.hpp>

#include <cstddef>
#include <cstdint>
#include <memory>
#include <span>
#include <stop_token>
#include <string>
#include <utility>
#include <vector>

namespace {

using namespace aletheia;

// The one override the decoder needs: the mock's base returns
// BinaryUnsupported here, which would send the client down the JSON path and
// past the decoder this harness exists for.
class BinaryMock : public MockBackend {
public:
    std::vector<std::byte> bytes;

    auto extract_signals_bin(const BackendState& /*state*/, const CanId& /*id*/, Dlc /*dlc*/,
                             std::span<const std::byte> /*data*/)
        -> std::expected<std::vector<std::byte>, AletheiaError> override {
        return bytes;
    }
};

auto one_message_dbc() -> DbcDefinition {
    auto signal = [](const char* name, std::uint16_t start_bit) {
        return DbcSignal{
            .name = SignalName{name},
            .start_bit = BitPosition{start_bit},
            .bit_length = BitLength{16},
            .byte_order = ByteOrder::LittleEndian,
            .is_signed = false,
            .factor = RationalFactor{Rational{1, 1}},
            .offset = RationalOffset{Rational{0, 1}},
            .minimum = RationalBound{Rational{0, 1}},
            .maximum = RationalBound{Rational{65535, 1}},
            .unit = Unit{""},
            .presence = AlwaysPresent{},
            .receivers = {},
        };
    };
    DbcMessage message{
        .id = StandardId::create(0x100).value(),
        .name = MessageName{"Frame"},
        .dlc = Dlc::create(8).value(),
        .sender = NodeName{"ECU"},
        .senders = {},
        .signals = {signal("First", 0), signal("Second", 16)},
    };
    return DbcDefinition{.version = "1.0", .messages = {std::move(message)}};
}

// Built once: the client, its DBC lookup and the eight payload bytes are the
// same for every input, and only the decoder's buffer varies.
struct Harness {
    BinaryMock* mock;
    std::unique_ptr<AletheiaClient> client;
};

auto harness() -> Harness& {
    static Harness built = [] {
        auto owned = std::make_unique<BinaryMock>();
        auto* mock = owned.get();
        const auto dbc = one_message_dbc();
        mock->queue_response(detail::serialize_parsed_dbc_response(dbc));
        auto client = std::make_unique<AletheiaClient>(std::move(owned));
        [[maybe_unused]] auto parsed = client->parse_dbc(std::stop_token{}, dbc);
        return Harness{.mock = mock, .client = std::move(client)};
    }();
    return built;
}

} // namespace

extern "C" auto LLVMFuzzerTestOneInput(const uint8_t* data, size_t size) -> int {
    // The decoder reads a length-prefixed value table; a buffer longer than a
    // CAN FD frame's own maximum only lengthens the corpus without reaching a
    // new shape.
    if (size > 64)
        return 0;

    auto& h = harness();
    h.mock->bytes.assign(reinterpret_cast<const std::byte*>(data),
                         reinterpret_cast<const std::byte*>(data) + size);

    const auto id = CanId{StandardId::create(0x100).value()};
    const auto dlc = Dlc::create(8).value();
    const std::vector<std::byte> payload(8, std::byte{0});
    [[maybe_unused]] auto result =
        h.client->extract_signals(std::stop_token{}, id, dlc, std::span{payload});
    return 0;
}
