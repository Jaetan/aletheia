// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
// The FFI backend's guards, DLC refusals and result buffer, exact rational
// rendering, the library lookup, and frames built and updated, through the
// real libaletheia-ffi.so.

#include <catch2/catch_message.hpp>
#include <catch2/catch_test_macros.hpp>
#include <catch2/matchers/catch_matchers.hpp>
#include <catch2/matchers/catch_matchers_string.hpp>

#include <aletheia/aletheia.hpp>
#include <aletheia/detail/rational_renderer.hpp>

#include "aletheia.h"

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <dlfcn.h>
#include <expected>
#include <filesystem>
#include <format>
#include <memory>
#include <optional>
#include <span>
#include <string>
#include <string_view>
#include <system_error>
#include <utility>
#include <vector>

#include "find_lib.hpp"
#include "integration_fixtures.hpp"
#include "loaded_library.hpp"
#include "temp_path.hpp"

using aletheia::test::find_lib;
using aletheia::test::make_integration_dbc;

using namespace aletheia;
namespace fs = std::filesystem;

TEST_CASE("the FFI backend is refused a library path that is empty", "[integration]") {
    REQUIRE_THROWS_WITH(make_ffi_backend(std::filesystem::path{}),
                        Catch::Matchers::ContainsSubstring("library path is empty"));
}

// A payload whose length is not its DLC's is refused on the backend's own
// interface, before the kernel sees it; both lengths are within the largest
// payload, so only the exact rule refuses them, one from below and one from
// above.
TEST_CASE("the FFI backend refuses a payload that is not its DLC's byte count", "[integration]") {
    auto const backend = make_ffi_backend(find_lib());
    auto const state = backend->init();
    auto const id = CanId{StandardId::create(0x100).value()};
    const std::vector<std::uint32_t> indices{0};
    const std::vector<std::int64_t> ones{1};
    auto const injection = SignalInjection::create(indices, ones, ones).value();
    auto const dlc8 = Dlc::create(8).value();
    auto const refused = [](const AletheiaError& error, std::size_t length) {
        CHECK(error.kind() == ErrorKind::Validation);
        CHECK(error.message() ==
              std::format("payload length {} does not match DLC 8 (expected 8 bytes)", length));
    };
    auto const thrown = [](auto&& call) -> std::optional<AletheiaError> {
        try {
            static_cast<void>(call());
        } catch (const AletheiaException& e) {
            return e.error();
        }
        return std::nullopt;
    };
    for (auto const length : {std::size_t{7}, std::size_t{20}}) {
        INFO("a payload of " << length << " bytes");
        const std::vector<std::byte> data(length, std::byte{0});
        auto const sent = thrown([&] {
            return backend->send_frame_binary(state, Timestamp{0}, id, dlc8, data, std::nullopt,
                                              std::nullopt);
        });
        REQUIRE(sent.has_value());
        refused(*sent, length);
        auto const extracted_json =
            thrown([&] { return backend->extract_signals_binary(state, id, dlc8, data); });
        REQUIRE(extracted_json.has_value());
        refused(*extracted_json, length);
        auto const updated = backend->update_frame_bin(state, id, dlc8, data, injection, 8);
        REQUIRE_FALSE(updated.has_value());
        refused(updated.error(), length);
        auto const extracted = backend->extract_signals_bin(state, id, dlc8, data);
        REQUIRE_FALSE(extracted.has_value());
        refused(extracted.error(), length);
    }
    // The exact length passes the guard to the kernel, which answers.
    const std::vector<std::byte> data8(8, std::byte{0});
    CHECK_FALSE(thrown([&] {
                    return backend->send_frame_binary(state, Timestamp{0}, id, dlc8, data8,
                                                      std::nullopt, std::nullopt);
                }).has_value());
    CHECK_FALSE(thrown([&] {
                    return backend->extract_signals_binary(state, id, dlc8, data8);
                }).has_value());
    auto const updated = backend->update_frame_bin(state, id, dlc8, data8, injection, 8);
    REQUIRE_FALSE(updated.has_value());
    CHECK(updated.error().code() == ErrorCode::HandlerNoDbc);
    auto const extracted = backend->extract_signals_bin(state, id, dlc8, data8);
    REQUIRE_FALSE(extracted.has_value());
    CHECK(extracted.error().code() == ErrorCode::HandlerNoDbc);
}

// The backend's endpoints are the public IBackend interface, so a call the
// client would never make, a command past the JSON cap or a message the DBC
// lacks, is a legitimate call on that interface and not a fabricated state.
TEST_CASE("the FFI backend's own guards answer on its interface", "[integration]") {
    auto const backend = make_ffi_backend(find_lib());
    auto const state = backend->init();
    // No DBC is loaded, so every binary endpoint the kernel reaches refuses.
    auto const id = CanId{StandardId::create(0x100).value()};
    auto const dlc = Dlc::create(15).value();
    const std::vector<std::byte> data64(64, std::byte{0});
    const std::vector<std::uint32_t> indices{0};
    const std::vector<std::int64_t> ones{1};
    auto const injection = SignalInjection::create(indices, ones, ones).value();

    SECTION("a command past the JSON cap is refused before the kernel sees it") {
        const std::string past_cap(max_json_bytes + 1, 'x');
        auto const answer = backend->process(state, past_cap);
        CHECK(answer.contains(R"("code":"input_bound_exceeded")"));
        CHECK(answer.contains(R"("observed":67108865)"));
    }
    SECTION("a kernel refusal on a binary endpoint is surfaced with its code, not swallowed") {
        // The entry hands back the kernel's error envelope; the error carries
        // the envelope's code and message, as a JSON response's would.
        auto const no_dbc = [](const AletheiaError& error) {
            CHECK(error.kind() == ErrorKind::Protocol);
            CHECK(error.code() == ErrorCode::HandlerNoDbc);
            CHECK(error.message() == "DBC not loaded");
        };
        auto const built = backend->build_frame_bin(state, id, dlc, injection, 64);
        REQUIRE_FALSE(built.has_value());
        no_dbc(built.error());
        auto const updated = backend->update_frame_bin(state, id, dlc, data64, injection, 64);
        REQUIRE_FALSE(updated.has_value());
        no_dbc(updated.error());
        auto const extracted = backend->extract_signals_bin(state, id, dlc, data64);
        REQUIRE_FALSE(extracted.has_value());
        no_dbc(extracted.error());
    }
}

// The wire carries the DLC as one byte and the kernel sizes the frame it
// builds from it, so a code past 15 is refused at the entry, before any
// signal is placed. The typed API cannot send one, so the test reaches the
// entry the way the backend does, through the library's own symbol.
TEST_CASE("the kernel refuses a DLC code past 15 on the binary build entry", "[integration]") {
    auto const lib = find_lib();
    auto const backend = make_ffi_backend(lib);
    auto const state = backend->init();
    const aletheia::test::LoadedLibrary handle{dlopen(lib.c_str(), RTLD_NOW | RTLD_NOLOAD)};
    REQUIRE(handle != nullptr);
    using BuildFn = decltype(&aletheia_build_frame_bin);
    using FreeFn = decltype(&aletheia_free_str);
    // dlsym returns void*; POSIX guarantees the round trip through void*
    // preserves function pointers wherever dlopen exists.
    // NOLINTNEXTLINE(cppcoreguidelines-pro-type-reinterpret-cast)
    auto const build = reinterpret_cast<BuildFn>(dlsym(handle.get(), "aletheia_build_frame_bin"));
    // NOLINTNEXTLINE(cppcoreguidelines-pro-type-reinterpret-cast)
    auto const free_str = reinterpret_cast<FreeFn>(dlsym(handle.get(), "aletheia_free_str"));
    REQUIRE(build != nullptr);
    REQUIRE(free_str != nullptr);

    aletheia_frame frame{};
    frame.can_id = 0x100;
    frame.dlc = 42;
    const aletheia_signal_values values{};
    std::array<std::uint8_t, 64> out_bytes{};
    aletheia_buffer out{.data = out_bytes.data(),
                        .err = nullptr,
                        .size = static_cast<std::uint32_t>(out_bytes.size())};
    auto const status = build(state.get(), &frame, &values, &out);
    // The kernel allocated the message; it is released by the kernel's own
    // free, from a destructor rather than from a line this test must reach.
    auto const release = [free_str](char* message) { free_str(message); };
    const std::unique_ptr<char, decltype(release)> error{out.err, release};
    CHECK(status == 1);
    REQUIRE(error != nullptr);
    // The error is the kernel's envelope, naming the refusal by its code.
    CHECK(std::string_view{error.get()}.contains("parse_dlc_code_out_of_range"));
    CHECK(std::string_view{error.get()}.contains("DLC 42 exceeds limit 15"));
}

namespace {
// Hides two of the library search's three routes, the environment and the
// working directory, and restores both when the test ends.
class HiddenSearchRoutes {
public:
    HiddenSearchRoutes() : cwd_{fs::current_path()} {
        if (const char* cur = std::getenv("ALETHEIA_LIB"))
            saved_ = cur;
        ::unsetenv("ALETHEIA_LIB");
        // Two levels down, so no relative candidate the search tries from
        // here can land on a build directory a developer keeps under /tmp.
        auto const nowhere = aletheia::test::scratch_dir() / "search" / "nowhere";
        fs::create_directories(nowhere);
        fs::current_path(nowhere);
    }
    ~HiddenSearchRoutes() {
        std::error_code ec;
        fs::current_path(cwd_, ec);
        if (saved_)
            ::setenv("ALETHEIA_LIB", saved_->c_str(), /*overwrite=*/1);
    }
    HiddenSearchRoutes(const HiddenSearchRoutes&) = delete;
    HiddenSearchRoutes(HiddenSearchRoutes&&) = delete;
    auto operator=(const HiddenSearchRoutes&) -> HiddenSearchRoutes& = delete;
    auto operator=(HiddenSearchRoutes&&) -> HiddenSearchRoutes& = delete;

private:
    fs::path cwd_;
    std::optional<std::string> saved_;
};
} // namespace

// The caller's DLC sizes the frame and the DBC places the bits: a message
// whose signals reach past a frame that small has nowhere to put them, and
// the bit writer would drop what does not fit without a word. The kernel
// names the first such signal instead.
TEST_CASE("a frame built at a DLC the message outgrows is refused", "[integration]") {
    auto const lib = find_lib();
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));
    REQUIRE(client.parse_dbc(std::stop_token{}, make_integration_dbc()).has_value());

    auto const id = CanId{StandardId::create(0x100).value()};
    const std::vector<SignalValue> speed{
        {.name = SignalName{"Speed"}, .value = PhysicalValue{Rational{100, 1}}}};

    // Speed occupies the first sixteen bits, so one byte cannot hold it.
    auto const refused = client.build_frame(std::stop_token{}, id, Dlc::create(1).value(), speed);
    REQUIRE_FALSE(refused.has_value());
    CHECK_THAT(std::string{refused.error().message()},
               Catch::Matchers::ContainsSubstring("signal 'Speed' does not fit a frame of size 1"));

    // Four bytes hold both signals of the message, and the frame is that long.
    auto const built = client.build_frame(std::stop_token{}, id, Dlc::create(4).value(), speed);
    REQUIRE(built.has_value());
    CHECK(built->size() == 4);
}

// The client sizes the result buffer from the DLC, and a CAN-FD frame is
// longer than any buffer a wrong size could still cover: sixty-four bytes come
// back from both the build and the update.
TEST_CASE("a CAN-FD frame is built and updated at its full length", "[integration]") {
    AletheiaClient client(make_ffi_backend(find_lib()));
    REQUIRE(client.parse_dbc(std::stop_token{}, make_integration_dbc()).has_value());

    auto const id = CanId{StandardId::create(0x100).value()};
    auto const dlc = Dlc::create(15).value();
    const std::vector<SignalValue> speed{
        {.name = SignalName{"Speed"}, .value = PhysicalValue{Rational{100, 1}}}};

    auto const built = client.build_frame(std::stop_token{}, id, dlc, speed);
    REQUIRE(built.has_value());
    CHECK(built->size() == 64);
    auto const updated = client.update_frame(std::stop_token{}, id, dlc, *built, speed);
    REQUIRE(updated.has_value());
    CHECK(updated->size() == 64);
}

// The result buffer is the caller's: the kernel refuses one too short for the
// frame before writing into it, and hands back how much it wrote into one
// longer than the frame, which the backend trims the result to.
TEST_CASE("the FFI backend's result buffer holds the frame the DLC sizes", "[integration]") {
    auto const backend = make_ffi_backend(find_lib());
    auto const state = backend->init();
    REQUIRE(backend
                ->process(state, R"({"type":"command","command":"parseDBC","dbc":{)"
                                 R"("version":"1.0","messages":[{"id":256,"name":"M","dlc":8,)"
                                 R"("sender":"ECU","signals":[{"name":"Speed","startBit":0,)"
                                 R"("length":16,"byteOrder":"little_endian","signed":false,)"
                                 R"("factor":1,"offset":0,"minimum":0,"maximum":65535,)"
                                 R"("unit":"","presence":"always","receivers":[]}]}]}})")
                .contains(R"("status": "success")"));

    auto const id = CanId{StandardId::create(0x100).value()};
    auto const dlc = Dlc::create(8).value();
    const std::vector<std::byte> data(8, std::byte{0});
    const std::vector<std::uint32_t> indices{0};
    const std::vector<std::int64_t> numerators{1000};
    const std::vector<std::int64_t> denominators{1};
    auto const injection = SignalInjection::create(indices, numerators, denominators).value();

    SECTION("a buffer shorter than the frame is refused") {
        // The library's own refusal, under a code the kernel's vocabulary does
        // not hold.
        auto const built = backend->build_frame_bin(state, id, dlc, injection, 4);
        REQUIRE_FALSE(built.has_value());
        CHECK(built.error().code() == ErrorCode::Unknown);
        CHECK(built.error().message() == "aletheia_build_frame_bin: out size 4 < 8 frame bytes");
        auto const updated = backend->update_frame_bin(state, id, dlc, data, injection, 4);
        REQUIRE_FALSE(updated.has_value());
        CHECK(updated.error().code() == ErrorCode::Unknown);
        CHECK(updated.error().message() == "aletheia_update_frame_bin: out size 4 < 8 frame bytes");
    }
    SECTION("a buffer longer than the frame comes back at the frame's length") {
        const std::vector<std::byte> speed{std::byte{0xE8}, std::byte{0x03}};
        auto const built = backend->build_frame_bin(state, id, dlc, injection, 64);
        REQUIRE(built.has_value());
        REQUIRE(built->size() == 8);
        CHECK(std::ranges::equal(std::span{*built}.first(2), speed));
        auto const updated = backend->update_frame_bin(state, id, dlc, data, injection, 64);
        REQUIRE(updated.has_value());
        REQUIRE(updated->size() == 8);
        CHECK(std::ranges::equal(std::span{*updated}.first(2), speed));
    }
}

// Every binding prints an observed value through the kernel's own rational
// formatter, so a terminating fraction reads as a decimal and a repeating one
// keeps its two parts. The client reaches it while it enriches a violation;
// this reads it directly, which is the only test in this binary that renders
// through a library the search had to find.
TEST_CASE("the kernel renders a rational exactly", "[integration]") {
    auto const backend = make_ffi_backend(find_lib()); // brings the runtime up
    CHECK(detail::format_rational_ffi(1, 2) == "0.5");
    CHECK(detail::format_rational_ffi(85, 2) == "42.5");
    CHECK(detail::format_rational_ffi(1, 3) == "1/3");
    CHECK(detail::format_rational_ffi(3, 1) == "3");
}

// The renderer consults the path the first backend registered when the
// environment names none and the working directory holds no candidate, which
// keeps a renderer in a process that moved elsewhere on the backend's library.
TEST_CASE("the library the first backend loaded is found from anywhere", "[integration]") {
    auto const lib = find_lib();
    auto const backend = make_ffi_backend(lib);
    const HiddenSearchRoutes hidden;
    auto const found = find_ffi_library();
    REQUIRE_FALSE(found.empty());
    CHECK(fs::equivalent(found, lib));
}

TEST_CASE("update then extract round-trip via real FFI", "[integration]") {
    auto backend = make_ffi_backend(find_lib());
    AletheiaClient client(std::move(backend));
    REQUIRE(client.parse_dbc(std::stop_token{}, make_integration_dbc()).has_value());

    auto const id = CanId{StandardId::create(0x100).value()};
    auto const dlc = Dlc::create(8).value();
    const std::vector<SignalValue> both{
        {.name = SignalName{"Speed"}, .value = PhysicalValue{Rational{100, 1}}},
        {.name = SignalName{"RPM"}, .value = PhysicalValue{Rational{3000, 1}}},
    };
    auto const built = client.build_frame(std::stop_token{}, id, dlc, both);
    REQUIRE(built.has_value());

    // Only RPM is written; Speed must come back as built, since the update
    // crosses the wire with the payload, its length, the DLC and the count
    // of values, and a wrong one of those loses a signal or refuses the frame.
    const std::vector<SignalValue> rpm_only{
        {.name = SignalName{"RPM"}, .value = PhysicalValue{Rational{1234, 1}}}};
    auto const updated = client.update_frame(std::stop_token{}, id, dlc, *built, rpm_only);
    REQUIRE(updated.has_value());
    auto const extracted = client.extract_signals(std::stop_token{}, id, dlc, *updated);
    REQUIRE(extracted.has_value());
    CHECK(extracted->get(SignalName{"Speed"}).get() == Rational{100, 1});
    CHECK(extracted->get(SignalName{"RPM"}).get() == Rational{1234, 1});
}

TEST_CASE("build frame via real FFI", "[integration]") {
    auto const lib = find_lib();
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));

    REQUIRE(client.parse_dbc(std::stop_token{}, make_integration_dbc()).has_value());

    auto const id = CanId{StandardId::create(0x100).value()};
    const std::vector<SignalValue> signals{
        {.name = SignalName{"Speed"}, .value = PhysicalValue{Rational{100, 1}}}, // raw = 1000
        {.name = SignalName{"RPM"}, .value = PhysicalValue{Rational{3000, 1}}},  // raw = 3000
    };

    auto const result = client.build_frame(std::stop_token{}, id, Dlc::create(8).value(), signals);
    REQUIRE(result.has_value());
    // Speed: 1000 = 0x03E8 LE → [0xE8, 0x03]
    CHECK((*result)[0] == std::byte{0xE8});
    CHECK((*result)[1] == std::byte{0x03});
    // RPM: 3000 = 0x0BB8 LE → [0xB8, 0x0B]
    CHECK((*result)[2] == std::byte{0xB8});
    CHECK((*result)[3] == std::byte{0x0B});
}

TEST_CASE("build then extract round-trip on an extended CAN ID via real FFI", "[integration]") {
    auto const lib = find_lib();
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));

    // The same message under a 29-bit identifier: the extended bit crosses the
    // wire on every binary call, and the kernel keys its message table on it.
    auto const id = CanId{ExtendedId::create(0x18FEF100).value()};
    auto dbc = make_integration_dbc();
    dbc.messages[0].id = id;
    REQUIRE(client.parse_dbc(std::stop_token{}, dbc).has_value());

    const std::vector<SignalValue> signals{
        {.name = SignalName{"Speed"}, .value = PhysicalValue{Rational{85, 2}}},
        {.name = SignalName{"RPM"}, .value = PhysicalValue{Rational{1500, 1}}},
    };
    auto const built = client.build_frame(std::stop_token{}, id, Dlc::create(8).value(), signals);
    REQUIRE(built.has_value());

    auto const extracted =
        client.extract_signals(std::stop_token{}, id, Dlc::create(8).value(), *built);
    REQUIRE(extracted.has_value());
    CHECK(extracted->get(SignalName{"Speed"}).get() == Rational{85, 2});
    CHECK(extracted->get(SignalName{"RPM"}).get() == Rational{1500, 1});
}

TEST_CASE("build frame for a CAN ID with no DBC message errors distinctly", "[integration]") {
    auto const lib = find_lib();
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));

    REQUIRE(client.parse_dbc(std::stop_token{}, make_integration_dbc()).has_value());

    // 0x200 has no message in the DBC (only 0x100 does). The error must name the
    // missing message ("no DBC message for CAN ID"), distinct from the per-signal
    // "signal not found", matching Go (resolveSignalIndices) and Python.
    auto const id = CanId{StandardId::create(0x200).value()};
    const std::vector<SignalValue> signals{
        {.name = SignalName{"Speed"}, .value = PhysicalValue{Rational{100, 1}}},
    };
    auto const result = client.build_frame(std::stop_token{}, id, Dlc::create(8).value(), signals);
    REQUIRE_FALSE(result.has_value());
    CHECK(result.error().kind() == ErrorKind::Validation);
    CHECK(std::string_view{result.error().message()}.contains("no DBC message for CAN ID"));
}

TEST_CASE("build then extract round-trip via real FFI", "[integration]") {
    auto const lib = find_lib();
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));

    REQUIRE(client.parse_dbc(std::stop_token{}, make_integration_dbc()).has_value());

    auto const id = CanId{StandardId::create(0x100).value()};
    const std::vector<SignalValue> signals{
        {.name = SignalName{"Speed"}, .value = PhysicalValue{Rational{85, 2}}},
        {.name = SignalName{"RPM"}, .value = PhysicalValue{Rational{1500, 1}}},
    };

    auto const built = client.build_frame(std::stop_token{}, id, Dlc::create(8).value(), signals);
    REQUIRE(built.has_value());

    auto const extracted =
        client.extract_signals(std::stop_token{}, id, Dlc::create(8).value(), *built);
    REQUIRE(extracted.has_value());
    // Each value is one a raw value scales to exactly, so it comes back unchanged.
    CHECK(extracted->get(SignalName{"Speed"}).get() == Rational{85, 2});
    CHECK(extracted->get(SignalName{"RPM"}).get() == Rational{1500, 1});
}

// The kernel writes a requested value only when it lies in the signal's
// declared range and a raw value scales to it exactly; otherwise building and
// updating a frame both refuse it, each refusal under its own code.
TEST_CASE("a value outside the signal's declared range is refused on build and update",
          "[integration]") {
    AletheiaClient client(make_ffi_backend(find_lib()));
    REQUIRE(client.parse_dbc(std::stop_token{}, make_integration_dbc()).has_value());

    auto const id = CanId{StandardId::create(0x100).value()};
    auto const dlc = Dlc::create(8).value();
    const std::vector<std::byte> data(8, std::byte{0});
    // RPM is [0, 65535] at factor 1: 70000 and -1 each have a raw value, and
    // each lies past one bound.
    struct Case {
        Rational value;
        std::string_view message;
    };
    for (auto const& [value, message] : std::to_array<Case>({
             {.value = Rational{70000, 1},
              .message = "value 70000 for signal 'RPM' is outside [0, 65535]"},
             {.value = Rational{-1, 1},
              .message = "value -1 for signal 'RPM' is outside [0, 65535]"},
         })) {
        CAPTURE(message);
        const std::vector<SignalValue> rpm{
            {.name = SignalName{"RPM"}, .value = PhysicalValue{value}}};

        auto const built = client.build_frame(std::stop_token{}, id, dlc, rpm);
        REQUIRE_FALSE(built.has_value());
        CHECK(built.error().code() == ErrorCode::FrameValueOutOfRange);
        CHECK(built.error().message() == message);

        auto const updated = client.update_frame(std::stop_token{}, id, dlc, data, rpm);
        REQUIRE_FALSE(updated.has_value());
        CHECK(updated.error().code() == ErrorCode::FrameValueOutOfRange);
        CHECK(updated.error().message() == message);
    }
}

TEST_CASE("the declared bounds are written exactly on build and update", "[integration]") {
    AletheiaClient client(make_ffi_backend(find_lib()));
    REQUIRE(client.parse_dbc(std::stop_token{}, make_integration_dbc()).has_value());

    auto const id = CanId{StandardId::create(0x100).value()};
    auto const dlc = Dlc::create(8).value();
    const std::vector<std::byte> data(8, std::byte{0});
    for (auto const value : {Rational{0, 1}, Rational{65535, 1}}) {
        const std::vector<SignalValue> rpm{
            {.name = SignalName{"RPM"}, .value = PhysicalValue{value}}};
        auto const built = client.build_frame(std::stop_token{}, id, dlc, rpm);
        REQUIRE(built.has_value());
        auto const updated = client.update_frame(std::stop_token{}, id, dlc, data, rpm);
        REQUIRE(updated.has_value());
        for (auto const& frame : {*built, *updated}) {
            auto const extracted = client.extract_signals(std::stop_token{}, id, dlc, frame);
            REQUIRE(extracted.has_value());
            CHECK(extracted->get(SignalName{"RPM"}).get() == value);
        }
    }
}

// Two multiplexed signals over the same bits, requested together: of two
// writes to one bit only the later would remain, so a build and an update
// both refuse them.
TEST_CASE("two signals sharing a bit are refused on build and update", "[integration]") {
    AletheiaClient client(make_ffi_backend(find_lib()));
    REQUIRE(client
                .parse_dbc_text(std::stop_token{},
                                "VERSION \"\"\n\nNS_ :\n\nBS_:\n\nBU_: ECU\n\n"
                                "BO_ 100 BasicMux: 8 ECU\n"
                                " SG_ Mode M : 0|4@1+ (1,0) [0|15] \"\" ECU\n"
                                " SG_ PayloadA m0 : 8|16@1+ (1,0) [0|65535] \"\" ECU\n"
                                " SG_ PayloadB m1 : 8|16@1+ (1,0) [0|65535] \"\" ECU\n\n")
                .has_value());

    auto const id = CanId{StandardId::create(100).value()};
    auto const dlc = Dlc::create(8).value();
    const std::vector<SignalValue> both{
        {.name = SignalName{"PayloadA"}, .value = PhysicalValue{Rational{1, 1}}},
        {.name = SignalName{"PayloadB"}, .value = PhysicalValue{Rational{1, 1}}}};

    auto const built = client.build_frame(std::stop_token{}, id, dlc, both);
    REQUIRE_FALSE(built.has_value());
    CHECK(built.error().code() == ErrorCode::FrameSignalsOverlap);
    CHECK(built.error().message() == "signals overlap");

    const std::vector<std::byte> data(8, std::byte{0});
    auto const updated = client.update_frame(std::stop_token{}, id, dlc, data, both);
    REQUIRE_FALSE(updated.has_value());
    CHECK(updated.error().code() == ErrorCode::FrameSignalsOverlap);
    CHECK(updated.error().message() == "signals overlap");
}

TEST_CASE("a value no raw value scales to is refused on build and update", "[integration]") {
    AletheiaClient client(make_ffi_backend(find_lib()));
    REQUIRE(client.parse_dbc(std::stop_token{}, make_integration_dbc()).has_value());

    auto const id = CanId{StandardId::create(0x100).value()};
    auto const dlc = Dlc::create(8).value();
    // RPM is factor 1, offset 0: 1.5 lies in its range, and between two raw values.
    const std::vector<SignalValue> rpm{
        {.name = SignalName{"RPM"}, .value = PhysicalValue{Rational{3, 2}}}};
    constexpr std::string_view message =
        "no integer raw value scales to value 1.5 for signal 'RPM' (factor 1, offset 0)";

    auto const built = client.build_frame(std::stop_token{}, id, dlc, rpm);
    REQUIRE_FALSE(built.has_value());
    CHECK(built.error().code() == ErrorCode::FrameValueNotRepresentable);
    CHECK(built.error().message() == message);

    const std::vector<std::byte> data(8, std::byte{0});
    auto const updated = client.update_frame(std::stop_token{}, id, dlc, data, rpm);
    REQUIRE_FALSE(updated.has_value());
    CHECK(updated.error().code() == ErrorCode::FrameValueNotRepresentable);
    CHECK(updated.error().message() == message);
}

TEST_CASE("FFI payload guards accept a payload of its DLC's length, 64 bytes included",
          "[integration][boundary]") {
    // Every FfiBackend method that takes a payload calls one guard,
    // `payload_length_error`, which refuses a payload whose length is not the
    // byte count its DLC names, behind the client's own check of the same
    // rule.  That makes the guard defense in depth: through the client it is
    // only ever reached at exactly the DLC's length, where it must pass.
    // Mutating its comparison flips that call from accept to reject, and these
    // calls, one per method that reaches the guard, are what kill those
    // mutants: the streaming send, the binary extraction for an identifier the
    // DBC knows, the JSON extraction for one it does not, and the frame
    // update.  Two of them report by throwing and two by returning an
    // unexpected value; the helper below covers both.  Per the
    // no-defense-removal rule the guard stays: this is the complement that
    // proves it accepts the legal length, at the largest DLC.
    auto const lib = find_lib();
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));
    REQUIRE(client.parse_dbc(std::stop_token{}, make_integration_dbc()).has_value());

    const std::vector<std::byte> data64(64, std::byte{0});
    auto const dlc = Dlc::create(15).value();                      // CAN-FD DLC 15 = 64 bytes
    auto const known = CanId{StandardId::create(0x100).value()};   // in the DBC → binary path
    auto const unknown = CanId{StandardId::create(0x7FF).value()}; // not in DBC → JSON fallback
    const std::vector<SignalValue> signals{
        {.name = SignalName{"Speed"}, .value = PhysicalValue{Rational{100, 1}}}};

    auto const mentions_mismatch = [](std::string_view msg) {
        return msg.contains("does not match DLC");
    };
    // A 64-byte call at DLC 15 must NOT produce the guard's error, whether
    // the guard reports by throwing or by returning std::unexpected.  The
    // original passes the guard (any other outcome is fine); a mutant
    // rejecting the exact length fails the check.
    auto const accepts_64 = [&](auto&& call) {
        try {
            auto const result = call();
            if (!result.has_value())
                CHECK_FALSE(mentions_mismatch(result.error().message()));
        } catch (const AletheiaException& e) {
            CHECK_FALSE(mentions_mismatch(e.what()));
        }
    };

    REQUIRE(client.start_stream(std::stop_token{}).has_value());
    accepts_64([&] {
        return client.send_frame(std::stop_token{}, Timestamp{1'000'000}, known, dlc, data64);
    });
    accepts_64([&] { return client.extract_signals(std::stop_token{}, known, dlc, data64); });
    accepts_64([&] { return client.extract_signals(std::stop_token{}, unknown, dlc, data64); });
    accepts_64([&] { return client.update_frame(std::stop_token{}, known, dlc, data64, signals); });
}
