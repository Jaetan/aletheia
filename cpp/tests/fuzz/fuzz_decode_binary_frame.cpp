// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// libFuzzer harness for the binary extraction decoder.
// Counterpart of go FuzzDecodeBinaryFrame.
//
// The decoder is `parse_extraction_bin`, a static helper inside the client's
// translation unit, so the harness reaches it the way the rational-number
// harness reaches the reply readers' rational reader: transitively, through
// the client's surface. A backend derived from the test mock hands the
// fuzzer's bytes back from `extract_signals_bin`, and a DBC parsed through the
// same mock fills the signal-name lookup the client needs to take the binary
// path at all. The kernel proves every index of the wire names a signal of its
// message, so the DBC's one message carries a signal for every index the
// two-byte field holds. The decoder must answer or refuse any buffer without
// undefined behaviour.
//
// Build/run: see fuzz_parse_response.cpp comment header.

#include "../../src/detail/json.hpp"
#include "../../src/detail/mock_backend.hpp"

#include <aletheia/client.hpp>
#include <aletheia/dbc.hpp>
#include <aletheia/types.hpp>

#include <cstddef>
#include <cstdint>
#include <expected>
#include <memory>
#include <span>
#include <stop_token>
#include <string>
#include <utility>
#include <vector>

using namespace aletheia;

// The one override the decoder needs: the mock's base returns
// BinaryUnsupported here, which would send the client down the JSON path and
// past the decoder this harness exists for.
namespace {
class BinaryMock : public MockBackend {
public:
    std::vector<std::byte> bytes;

    auto extract_signals_bin(BackendState const& /*state*/, CanId const& /*id*/, Dlc /*dlc*/,
                             std::span<std::byte const> /*data*/)
        -> std::expected<std::vector<std::byte>, AletheiaError> override {
        return bytes;
    }
};
} // namespace

// One message whose 2^16 signals, all alike, give every wire index a name.
static auto one_message_dbc() -> DbcDefinition {
    DbcSignal const signal{
        .name = SignalName{"S"},
        .start_bit = BitPosition{0},
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
    DbcMessage message{
        .id = StandardId::create(0x100).value(),
        .name = MessageName{"Frame"},
        .dlc = Dlc::create(8).value(),
        .sender = NodeName{"ECU"},
        .senders = {},
        .signals = std::vector<DbcSignal>(std::size_t{1} << 16U, signal),
    };
    return DbcDefinition{.version = "1.0", .messages = {std::move(message)}};
}
namespace {

// Built once: the client, its DBC lookup and the eight payload bytes are the
// same for every input, and only the decoder's buffer varies.
struct Harness {
    BinaryMock* mock;
    std::unique_ptr<AletheiaClient> client;
};
} // namespace

static auto harness() -> Harness& {
    static Harness built = [] {
        auto owned = std::make_unique<BinaryMock>();
        auto* mock = owned.get();
        auto const dbc = one_message_dbc();
        mock->queue_response(detail::serialize_parsed_dbc_response(dbc));
        auto client =
            std::make_unique<AletheiaClient>(AletheiaClient::create(std::move(owned)).value());
        [[maybe_unused]] auto const parsed = client->parse_dbc(std::stop_token{}, dbc);
        return Harness{.mock = mock, .client = std::move(client)};
    }();
    return built;
}

extern "C" auto LLVMFuzzerTestOneInput(uint8_t const* data, size_t size) -> int {
    // The decoder reads a length-prefixed value table; a buffer longer than a
    // CAN FD frame's own maximum only lengthens the corpus without reaching a
    // new shape.
    if (size > 64)
        return 0;

    auto& h = harness();
    h.mock->bytes.assign(reinterpret_cast<std::byte const*>(data),
                         reinterpret_cast<std::byte const*>(data) + size);

    auto const id = CanId{StandardId::create(0x100).value()};
    auto const dlc = Dlc::create(8).value();
    std::vector<std::byte> const payload(8, std::byte{0});
    [[maybe_unused]] auto const result =
        h.client->extract_signals(std::stop_token{}, id, dlc, std::span{payload});
    return 0;
}
