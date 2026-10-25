// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
// Unit tests: the client's payload and timestamp checks, the DLC table,
// Rational's order, and the FFI backend: how it and the renderer find, open
// and refuse a library, what it hands the kernel and frees, the exception it
// throws, and the kernel's allocation count it reads.
#include <catch2/catch_message.hpp>
#include <catch2/catch_test_macros.hpp>
#include <catch2/generators/catch_generators.hpp>
#include <catch2/matchers/catch_matchers.hpp>
#include <catch2/matchers/catch_matchers_string.hpp>

#include "detail/dl_symbol.hpp"
#include "detail/ffi_abi.hpp"
#include "detail/mock_backend.hpp"
#include "integration_fixtures.hpp"
#include "loaded_library.hpp"
#include "temp_path.hpp"
#include <aletheia/aletheia.hpp>
#include <aletheia/detail/rational_renderer.hpp>

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <dlfcn.h>
#include <exception>
#include <filesystem>
#include <fstream>
#include <limits>
#include <memory>
#include <optional>
#include <ranges>
#include <stop_token>
#include <string>
#include <string_view>
#include <tuple>
#include <utility>
#include <variant>
#include <vector>

using namespace aletheia;
using Catch::Matchers::ContainsSubstring;

// A stand-in kernel `cabal run shake -- build` makes beside the library: one
// missing is a build that has not run since it was added.
static auto stand_in(const std::filesystem::path& path) -> std::filesystem::path {
    INFO("stand-in " << path.string() << " not built; run 'cabal run shake -- build'");
    REQUIRE(std::filesystem::exists(path));
    return path;
}

// ===========================================================================
// Payload validation tests
// ===========================================================================

TEST_CASE("send_frame rejects payload length mismatch", "[client][validation]") {
    auto mock = std::make_unique<MockBackend>();
    AletheiaClient client(std::move(mock));

    auto const id = CanId{StandardId::create(0x100).value()};
    auto const dlc = Dlc::create(8).value(); // expects 8 bytes
    const FramePayload short_data(3, std::byte{0});
    auto const result =
        client.send_frame(std::stop_token{}, Timestamp{1'000'000}, id, dlc, short_data);

    CHECK_FALSE(result.has_value());
    CHECK(result.error().kind() == ErrorKind::Validation);
    CHECK_THAT(std::string{result.error().message()}, ContainsSubstring("payload length 3"));
    CHECK_THAT(std::string{result.error().message()}, ContainsSubstring("expected 8 bytes"));
}

TEST_CASE("extract_signals rejects payload length mismatch", "[client][validation]") {
    auto mock = std::make_unique<MockBackend>();
    AletheiaClient client(std::move(mock));

    auto const id = CanId{StandardId::create(0x100).value()};
    auto const dlc = Dlc::create(8).value();
    const FramePayload long_data(16, std::byte{0}); // 16 bytes but DLC 8 expects 8
    auto const result = client.extract_signals(std::stop_token{}, id, dlc, long_data);

    CHECK_FALSE(result.has_value());
    CHECK(result.error().kind() == ErrorKind::Validation);
}

TEST_CASE("update_frame rejects payload length mismatch", "[client][validation]") {
    auto mock = std::make_unique<MockBackend>();
    AletheiaClient client(std::move(mock));

    auto const id = CanId{StandardId::create(0x100).value()};
    auto const dlc = Dlc::create(8).value();
    const FramePayload bad_data(5, std::byte{0});
    const std::vector<SignalValue> signals{
        {.name = SignalName{"S"}, .value = PhysicalValue{Rational{1, 1}}}};
    auto const result = client.update_frame(std::stop_token{}, id, dlc, bad_data, signals);

    CHECK_FALSE(result.has_value());
    CHECK(result.error().kind() == ErrorKind::Validation);
}

TEST_CASE("send_frame accepts correct payload length", "[client][validation]") {
    auto mock = std::make_unique<MockBackend>();
    mock->queue_response(R"({"status": "ack"})");
    AletheiaClient client(std::move(mock));

    auto const id = CanId{StandardId::create(0x100).value()};
    auto const dlc = Dlc::create(8).value();
    const FramePayload data(8, std::byte{0}); // exactly 8 bytes for DLC 8
    auto const result = client.send_frame(std::stop_token{}, Timestamp{1'000'000}, id, dlc, data);

    REQUIRE(result.has_value());
    CHECK(std::holds_alternative<Ack>(*result));
}

TEST_CASE("send_frame accepts CAN-FD payload", "[client][validation]") {
    auto mock = std::make_unique<MockBackend>();
    mock->queue_response(R"({"status": "ack"})");
    AletheiaClient client(std::move(mock));

    auto const id = CanId{StandardId::create(0x100).value()};
    auto const dlc = Dlc::create(15).value(); // DLC 15 = 64 bytes
    const FramePayload data(64, std::byte{0});
    auto const result = client.send_frame(std::stop_token{}, Timestamp{1'000'000}, id, dlc, data);

    REQUIRE(result.has_value());
    CHECK(std::holds_alternative<Ack>(*result));
}

// ===========================================================================
// Timestamp validation
// ===========================================================================

TEST_CASE("send_frame rejects negative timestamp", "[client][validation]") {
    auto mock = std::make_unique<MockBackend>();
    AletheiaClient client(std::move(mock));

    auto const id = CanId{StandardId::create(0x100).value()};
    auto const dlc = Dlc::create(8).value();
    const FramePayload data(8, std::byte{0});
    auto const result = client.send_frame(std::stop_token{}, Timestamp{-1000}, id, dlc, data);

    CHECK_FALSE(result.has_value());
    CHECK(result.error().kind() == ErrorKind::Validation);
    CHECK_THAT(std::string{result.error().message()}, ContainsSubstring("non-negative"));
}

TEST_CASE("send_error succeeds with mock backend", "[client][validation]") {
    auto mock = std::make_unique<MockBackend>();
    mock->queue_response(R"({"status": "ack"})"); // send_error binary response
    AletheiaClient client(std::move(mock));
    auto const result = client.send_error(std::stop_token{}, Timestamp{1'000'000});
    CHECK(result.has_value());
}

TEST_CASE("send_error rejects negative timestamp", "[client][validation]") {
    auto mock = std::make_unique<MockBackend>();
    AletheiaClient client(std::move(mock));
    auto const result = client.send_error(std::stop_token{}, Timestamp{-1000});
    CHECK_FALSE(result.has_value());
    CHECK(result.error().kind() == ErrorKind::Validation);
    CHECK_THAT(std::string{result.error().message()}, ContainsSubstring("non-negative"));
}

TEST_CASE("send_remote succeeds with mock backend", "[client][validation]") {
    auto mock = std::make_unique<MockBackend>();
    mock->queue_response(R"({"status": "ack"})"); // send_remote binary response
    AletheiaClient client(std::move(mock));
    auto const id = CanId{StandardId::create(0x100).value()};
    auto const result = client.send_remote(std::stop_token{}, Timestamp{1'000'000}, id);
    CHECK(result.has_value());
}

TEST_CASE("send_remote rejects negative timestamp", "[client][validation]") {
    auto mock = std::make_unique<MockBackend>();
    AletheiaClient client(std::move(mock));
    auto const id = CanId{StandardId::create(0x100).value()};
    auto const result = client.send_remote(std::stop_token{}, Timestamp{-1000}, id);
    CHECK_FALSE(result.has_value());
    CHECK(result.error().kind() == ErrorKind::Validation);
    CHECK_THAT(std::string{result.error().message()}, ContainsSubstring("non-negative"));
}

// ===========================================================================
// DLC table
// ===========================================================================

TEST_CASE("every DLC code maps to its byte count and back, and no other count has a code",
          "[types]") {
    // The byte counts are written here, not read from the header's table, so a
    // wrong entry there is caught.
    constexpr std::array<std::size_t, 16> bytes_by_code{0, 1,  2,  3,  4,  5,  6,  7,
                                                        8, 12, 16, 20, 24, 32, 48, 64};
    for (auto const [index, bytes] : std::views::enumerate(bytes_by_code)) {
        auto const code = static_cast<std::uint8_t>(index);
        INFO("code " << int{code});
        auto const dlc = Dlc::create(code);
        REQUIRE(dlc.has_value());
        CHECK(dlc_to_bytes(*dlc) == bytes);
        auto const back = bytes_to_dlc(bytes);
        REQUIRE(back.has_value());
        CHECK(back->value() == code);
    }
    auto const has_no_code = [&](std::size_t count) {
        return !std::ranges::contains(bytes_by_code, count);
    };
    auto const refused = [](std::size_t count) {
        INFO("byte count " << count);
        auto const answer = bytes_to_dlc(count);
        REQUIRE_FALSE(answer.has_value());
        CHECK_THAT(answer.error(), ContainsSubstring("invalid DLC"));
    };
    auto const up_to_65 = std::views::iota(std::size_t{0}, std::size_t{66});
    std::ranges::for_each(up_to_65 | std::views::filter(has_no_code), refused);
    // Counts past the table that name an entry once narrowed to 8, 16 or 32 bits.
    constexpr std::array<std::size_t, 3> aliases{256 + 8, 65'536 + 8, 4'294'967'296 + 8};
    std::ranges::for_each(aliases, refused);
}

// ===========================================================================
// Rational comparison
// ===========================================================================

TEST_CASE("Rational operator<=> and operator==", "[types]") {
    const Rational a{1, 2};  // 0.5
    const Rational b{2, 4};  // 0.5
    const Rational c{3, 4};  // 0.75
    const Rational d{-1, 2}; // -0.5

    SECTION("equality") {
        CHECK(a == b);
        CHECK_FALSE(a == c);
        CHECK(Rational{0, 1} == Rational{0, 5});
        CHECK(Rational{std::numeric_limits<std::int64_t>::max(),
                       std::numeric_limits<std::int64_t>::max()} == Rational{1, 1});
    }

    SECTION("less than") {
        CHECK(a < c);
        CHECK(d < a);
        CHECK(Rational{1, 3} < Rational{1, 2});
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
        const Rational neg{-3, 4};
        CHECK(neg < a);
        CHECK(d == Rational{-1, 2});
        CHECK(Rational{-5, 7} == Rational{-10, 14});
        CHECK(Rational{-1, 3} < Rational{1, 3});
    }

    SECTION("pairs whose cross products pass 64 bits, or that a double cannot tell apart") {
        constexpr auto max = std::numeric_limits<std::int64_t>::max();
        CHECK(Rational{max, 1} > Rational{max - 1, 1});
        CHECK(Rational{max, 2} < Rational{max - 1, 1});
        CHECK(Rational{-max, 3} < Rational{-(max - 1), 3});
        CHECK(Rational{1, max} < Rational{1, max - 1});
    }
}

// ===========================================================================
// The FFI backend and the renderer
// ===========================================================================
//
// `ErrorKind::Ffi` is declared in error.hpp for a library-load or runtime-init
// failure, and mirrors Python's FFIError and Go's ErrFFI. A case asserting a
// kind holds it to the path that emits it, so a failure downgraded to a plain
// runtime error or to another kind trips here.

TEST_CASE("make_ffi_backend with nonexistent library throws Ffi-kinded exception", "[ffi][error]") {
    // dlopen of a path that does not exist returns null + sets dlerror;
    // FfiBackend's constructor lifts that to AletheiaException(Ffi).
    REQUIRE_THROWS_AS(make_ffi_backend("/nonexistent/aletheia/libaletheia-ffi.so", 1),
                      AletheiaException);
    try {
        static_cast<void>(make_ffi_backend("/nonexistent/aletheia/libaletheia-ffi.so", 1));
        FAIL("expected AletheiaException");
    } catch (const AletheiaException& e) {
        CHECK(e.kind() == ErrorKind::Ffi);
        CHECK_THAT(std::string{e.what()}, ContainsSubstring("dlopen failed"));
    }
}

TEST_CASE("make_ffi_backend with a count outside the CPUs the library counts throws Validation",
          "[ffi][validation]") {
    // The constructor's count guard is caller-argument validation, not an FFI
    // failure, as in Go and Python. The bound is read from the library opened,
    // and the recording kernel counts four CPUs whatever the machine.
    for (auto const cores : {0, 5}) {
        try {
            static_cast<void>(make_ffi_backend(stand_in(ALETHEIA_TEST_RECORDING_KERNEL), cores));
            FAIL("expected AletheiaException");
        } catch (const AletheiaException& e) {
            CHECK(e.kind() == ErrorKind::Validation);
            CHECK(std::string_view{e.what()} ==
                  "core count " + std::to_string(cores) +
                      " is outside 1 to 4, the CPUs this process may use");
        }
    }
}

// The fixture library carries none of the kernel's symbols, so the constructor
// opens it, fails on its first lookup and must close it again: afterwards the
// loader holds no mapping of it, which RTLD_NOLOAD reports without loading.
TEST_CASE("a refused construction leaves the library it opened unloaded", "[ffi][validation]") {
    auto const lib = stand_in(ALETHEIA_TEST_SYMBOLLESS_LIB);
    REQUIRE_THROWS_WITH(make_ffi_backend(lib), ContainsSubstring("dlsym failed"));
    const aletheia::test::LoadedLibrary still_mapped{dlopen(lib.c_str(), RTLD_NOW | RTLD_NOLOAD)};
    CHECK(still_mapped == nullptr);
}

// A library laid out for another ABI version is refused by the version it
// reports, the first thing the backend reads, and left unloaded.
TEST_CASE("a library at another ABI version is refused and left unloaded", "[ffi][validation]") {
    auto const lib = stand_in(ALETHEIA_TEST_STALE_ABI_KERNEL);
    try {
        std::ignore = make_ffi_backend(lib);
        FAIL("a library at another ABI version was accepted");
    } catch (const AletheiaException& e) {
        CHECK(e.error().kind() == ErrorKind::Ffi);
        CHECK_THAT(std::string{e.what()},
                   ContainsSubstring("the library implements ABI version " +
                                     std::to_string(aletheia::detail::abi_version + 1)));
    }
    const aletheia::test::LoadedLibrary still_mapped{dlopen(lib.c_str(), RTLD_NOW | RTLD_NOLOAD)};
    CHECK(still_mapped == nullptr);
}

namespace {
// Save/restore ALETHEIA_LIB around a test. Catch2 runs test cases sequentially,
// so mutating the process environment is safe as long as it is restored.
class ScopedAletheiaLib {
public:
    explicit ScopedAletheiaLib(const char* value) {
        if (const char* cur = std::getenv("ALETHEIA_LIB"))
            saved_ = cur;
        if (value != nullptr)
            ::setenv("ALETHEIA_LIB", value, /*overwrite=*/1);
        else
            ::unsetenv("ALETHEIA_LIB");
    }
    ScopedAletheiaLib(const ScopedAletheiaLib&) = delete;
    ScopedAletheiaLib(ScopedAletheiaLib&&) = delete;
    auto operator=(const ScopedAletheiaLib&) -> ScopedAletheiaLib& = delete;
    auto operator=(ScopedAletheiaLib&&) -> ScopedAletheiaLib& = delete;
    ~ScopedAletheiaLib() {
        if (saved_)
            ::setenv("ALETHEIA_LIB", saved_->c_str(), /*overwrite=*/1);
        else
            ::unsetenv("ALETHEIA_LIB");
    }

private:
    std::optional<std::string> saved_;
};
} // namespace

TEST_CASE("the loader is read one way, and a refusal never reads a null from it", "[ffi][loader]") {
    // dlerror holds the loader's text for the failure just made and answers
    // null once that text has been read, so a refusal built after another has
    // read it must stand on a fixed phrase rather than on a null.
    const aletheia::test::LoadedLibrary symbolless{
        dlopen(stand_in(ALETHEIA_TEST_SYMBOLLESS_LIB).c_str(), RTLD_NOW)};
    REQUIRE(symbolless != nullptr);
    auto const missing = aletheia::detail::dl_symbol(symbolless.get(), "aletheia_abi_version");
    REQUIRE_FALSE(missing.has_value());
    CHECK_THAT(missing.error(), ContainsSubstring("aletheia_abi_version: "));
    CHECK_THAT(missing.error(), !ContainsSubstring("the loader reported no detail"));
    CHECK(aletheia::detail::dl_error_text() == "the loader reported no detail");

    const aletheia::test::LoadedLibrary recording{
        dlopen(stand_in(ALETHEIA_TEST_RECORDING_KERNEL).c_str(), RTLD_NOW)};
    REQUIRE(recording != nullptr);
    auto const present = aletheia::detail::dl_symbol(recording.get(), "aletheia_abi_version");
    REQUIRE(present.has_value());
    CHECK(present.value() != nullptr);
}

TEST_CASE("make_ffi_backend_from_env opens the library ALETHEIA_LIB names", "[ffi][validation]") {
    // The route's success, before its two refusals below: a guard on the
    // variable read backwards refuses a set variable, which this reports.
    auto const lib = find_ffi_library();
    if (lib.empty())
        SKIP("no kernel library to name");
    const ScopedAletheiaLib guard{lib.c_str()};
    auto const backend = make_ffi_backend_from_env(1);
    REQUIRE(backend != nullptr);
    CHECK(backend->init());
}

TEST_CASE("make_ffi_backend_from_env refuses ALETHEIA_LIB unset or empty as a usage error",
          "[ffi][validation]") {
    // Unset and empty are one case, the caller's error rather than an FFI
    // failure, refused naming the variable; the constructor's own refusal of
    // an empty path names none.
    auto const* const value = GENERATE(as<const char*>{}, nullptr, "");
    const ScopedAletheiaLib guard{value};
    try {
        static_cast<void>(make_ffi_backend_from_env(1));
        FAIL("expected AletheiaException");
    } catch (const AletheiaException& e) {
        CHECK(e.kind() == ErrorKind::Validation);
        CHECK(std::string_view{e.what()} == "ALETHEIA_LIB is not set: set it to the path of "
                                            "libaletheia-ffi.so, or call make_ffi_backend(path)");
    }
}

TEST_CASE("start_runtime_from_env refuses ALETHEIA_LIB unset or empty, naming its counted twin",
          "[ffi][validation]") {
    auto const* const value = GENERATE(as<const char*>{}, nullptr, "");
    const ScopedAletheiaLib guard{value};
    try {
        static_cast<void>(start_runtime_from_env(1));
        FAIL("expected AletheiaException");
    } catch (const AletheiaException& e) {
        CHECK(e.kind() == ErrorKind::Validation);
        CHECK(std::string_view{e.what()} ==
              "ALETHEIA_LIB is not set: set it to the path of "
              "libaletheia-ffi.so, or call start_runtime(path, cores)");
    }
}

TEST_CASE("start_runtime_from_env and the count-less factory open the library ALETHEIA_LIB names",
          "[ffi][validation]") {
    // The listener started the runtime on one core, so a start asking one and a
    // backend asking none both find it running as asked.
    auto const lib = find_ffi_library();
    if (lib.empty())
        SKIP("no kernel library to name");
    const ScopedAletheiaLib guard{lib.c_str()};
    CHECK_FALSE(start_runtime_from_env(1).has_value());
    auto const backend = make_ffi_backend_from_env();
    REQUIRE(backend != nullptr);
    CHECK_FALSE(backend->rts_mismatch_info().has_value());
}

TEST_CASE(
    "make_ffi_backend_from_env with a nonexistent ALETHEIA_LIB path throws Ffi-kinded exception",
    "[ffi][error]") {
    // A set path that does not exist reaches dlopen (Ffi), not the unset
    // guard: a guard refusing every set value would answer as the case above.
    const ScopedAletheiaLib guard{"/nonexistent/aletheia/libaletheia-ffi.so"};
    try {
        static_cast<void>(make_ffi_backend_from_env(1));
        FAIL("expected AletheiaException");
    } catch (const AletheiaException& e) {
        CHECK(e.kind() == ErrorKind::Ffi);
        CHECK_THAT(std::string{e.what()}, ContainsSubstring("dlopen failed"));
    }
}

TEST_CASE("AletheiaException is catchable as std::exception", "[error]") {
    // A catch on the standard exception type catches this one, through the
    // runtime-error base it derives from, so a caller that never learned the
    // library's own exception type still sees the failure.
    try {
        throw AletheiaException(AletheiaError{ErrorKind::Ffi, "test message"});
    } catch (const std::exception& e) {
        CHECK_THAT(std::string{e.what()}, ContainsSubstring("test message"));
    }
}

TEST_CASE("the library search takes ALETHEIA_LIB when it names a file that exists",
          "[ffi][search]") {
    // The environment route comes first and is taken on existence alone: any
    // file that exists is answered as given, before the registered path, so
    // the answer is the file this test made and not the library the process
    // already holds.
    const aletheia::test::TempPath file{"search_env_route.so"};
    { const std::ofstream touch{file.path}; }
    REQUIRE(std::filesystem::exists(file.path));
    const ScopedAletheiaLib guard{file.path.c_str()};
    CHECK(find_ffi_library() == file.path);
}

TEST_CASE("the library search answers by route, on existence alone", "[ffi][search]") {
    // Each route is one existence check, tried in order: the environment
    // value, the registered path, then the build-tree candidates under the
    // given directory. The search takes its inputs, so each route is reached
    // whatever the process already holds.
    using aletheia::detail::search_ffi_library;
    const aletheia::test::TempPath env_file{"search_env.so"};
    const aletheia::test::TempPath registered_file{"search_registered.so"};
    const aletheia::test::TempPath tree{"search_tree"};
    { const std::ofstream touch{env_file.path}; }
    { const std::ofstream touch{registered_file.path}; }
    std::filesystem::create_directories(tree.path / "build");
    auto const candidate = tree.path / "build" / "libaletheia-ffi.so";
    { const std::ofstream touch{candidate}; }
    auto const nowhere = std::filesystem::path{"/nonexistent/aletheia"};

    SECTION("the environment value wins when it exists") {
        CHECK(search_ffi_library(env_file.path.c_str(), registered_file.path.string(), tree.path) ==
              env_file.path);
    }
    SECTION("a registered path that exists answers next") {
        CHECK(search_ffi_library(nowhere.c_str(), registered_file.path.string(), tree.path) ==
              registered_file.path);
        CHECK(search_ffi_library(nullptr, registered_file.path.string(), tree.path) ==
              registered_file.path);
    }
    SECTION("a build-tree candidate under the directory answers last, canonically") {
        CHECK(search_ffi_library(nullptr, "", tree.path) == std::filesystem::canonical(candidate));
        CHECK(search_ffi_library(nowhere.c_str(), nowhere.string(), tree.path) ==
              std::filesystem::canonical(candidate));
    }
    SECTION("an empty environment value is no route") {
        CHECK(search_ffi_library("", registered_file.path.string(), tree.path) ==
              registered_file.path);
        CHECK(search_ffi_library("", "", tree.path) == std::filesystem::canonical(candidate));
    }
    SECTION("no route answering is the empty path") {
        CHECK(search_ffi_library(nullptr, "", nowhere).empty());
        CHECK(search_ffi_library(nowhere.c_str(), nowhere.string(), nowhere).empty());
    }
}

TEST_CASE("a start refuses a library that will not serve it, and leaves it unmapped",
          "[ffi][runtime]") {
    // The listener started the runtime, so a start of a library that serves
    // answers the running count, and one that does not throws before it is
    // read further, closing what it opened.
    auto const refused = [](const std::filesystem::path& lib, std::string_view why) {
        CHECK_THROWS_WITH(start_runtime(lib, 1), ContainsSubstring(std::string{why}));
        const aletheia::test::LoadedLibrary still_mapped{
            dlopen(lib.c_str(), RTLD_NOW | RTLD_NOLOAD)};
        CHECK(still_mapped == nullptr);
    };
    SECTION("an empty path") {
        CHECK_THROWS_WITH(start_runtime({}, 1),
                          "library path is empty: pass the path of libaletheia-ffi.so");
    }
    SECTION("a path that does not open") {
        CHECK_THROWS_WITH(start_runtime("/nonexistent/aletheia/libaletheia-ffi.so", 1),
                          ContainsSubstring("dlopen failed"));
    }
    SECTION("a library without the version entry") {
        refused(stand_in(ALETHEIA_TEST_SYMBOLLESS_LIB), "dlsym failed for aletheia_abi_version");
    }
    SECTION("a library at this ABI version without the runtime's start entry") {
        refused(stand_in(ALETHEIA_TEST_ABI_ONLY_LIB), "dlsym failed for hs_init_with_rtsopts");
    }
    SECTION("a library at another ABI version") {
        refused(stand_in(ALETHEIA_TEST_STALE_ABI_KERNEL),
                "the library implements ABI version " +
                    std::to_string(aletheia::detail::abi_version + 1));
    }
    SECTION("the kernel library itself, which serves") {
        auto const lib = find_ffi_library();
        if (lib.empty())
            SKIP("no kernel library to load");
        CHECK_FALSE(start_runtime(lib, 1).has_value());
    }
}

TEST_CASE("the FFI backend hands the kernel the timestamp and bus bits it was given",
          "[ffi][marshal]") {
    // The recording kernel refuses every call with a message quoting its
    // arguments, which is the only way to read what reached an entry the real
    // kernel acknowledges without reading. Its runtime entry is a no-op, and
    // the first backend of a process registers its library for the renderer
    // and marks the runtime up, so this one is built only where the real
    // library has already done both.
    if (find_ffi_library().empty())
        SKIP("no kernel library holds the process, so the stand-in must not be its first backend");
    auto backend = make_ffi_backend(std::filesystem::path{ALETHEIA_TEST_RECORDING_KERNEL});
    AletheiaClient client(std::move(backend));
    auto const message = [](auto const& result) -> std::string {
        REQUIRE_FALSE(result.has_value());
        return std::string{result.error().message()};
    };

    CHECK_THAT(message(client.send_error(std::stop_token{}, Timestamp{123456})),
               ContainsSubstring("send_error ts=123456"));

    auto const extended = CanId{ExtendedId::create(0x18FEF100).value()};
    CHECK_THAT(message(client.send_remote(std::stop_token{}, Timestamp{7890}, extended)),
               ContainsSubstring("send_remote ts=7890 id=" +
                                 std::to_string(can_id_value(extended)) + " extended=1"));

    auto const standard = CanId{StandardId::create(0x100).value()};
    CHECK_THAT(message(client.send_remote(std::stop_token{}, Timestamp{7891}, standard)),
               ContainsSubstring("send_remote ts=7891 id=256 extended=0"));

    auto const dlc = Dlc::create(2).value();
    const FramePayload data{std::byte{1}, std::byte{2}};
    CHECK_THAT(message(client.send_frame(std::stop_token{}, Timestamp{99}, standard, dlc, data,
                                         true, false)),
               ContainsSubstring("send_frame ts=99 id=256 extended=0 dlc=2 len=2 brs=1/1 esi=1/0"));
    CHECK_THAT(message(client.send_frame(std::stop_token{}, Timestamp{99}, standard, dlc, data,
                                         std::nullopt, std::nullopt)),
               ContainsSubstring("brs=0/0 esi=0/0"));
}

TEST_CASE("the FFI backend hands the kernel every byte of a command", "[ffi][marshal]") {
    // The kernel reads a command's text by its size, so a NUL inside it is
    // the kernel's to refuse rather than the end of the command.
    if (find_ffi_library().empty())
        SKIP("no kernel library holds the process, so the stand-in must not be its first backend");
    auto const backend = make_ffi_backend(std::filesystem::path{ALETHEIA_TEST_RECORDING_KERNEL});
    auto const state = backend->init();
    using namespace std::string_view_literals;
    CHECK_THAT(backend->process(state, "{}\0{}"sv), ContainsSubstring("process size=5"));
}

// One of the recording kernel's counters, which are the one way to read a
// release the real kernel acknowledges without reading.
using CountFn = int (*)();
static auto recording_kernel_counter(const aletheia::test::LoadedLibrary& handle, const char* name)
    -> CountFn {
    // NOLINTNEXTLINE(cppcoreguidelines-pro-type-reinterpret-cast)
    auto* const count = reinterpret_cast<CountFn>(dlsym(handle.get(), name));
    REQUIRE(count != nullptr);
    return count;
}

TEST_CASE("the FFI backend closes the kernel state it opened", "[ffi][marshal]") {
    if (find_ffi_library().empty())
        SKIP("no kernel library holds the process, so the stand-in must not be its first backend");
    const std::filesystem::path stand_in{ALETHEIA_TEST_RECORDING_KERNEL};
    const aletheia::test::LoadedLibrary handle{dlopen(stand_in.c_str(), RTLD_NOW)};
    REQUIRE(handle != nullptr);
    auto* const count = recording_kernel_counter(handle, "aletheia_test_close_count");
    auto const before = count();
    { const AletheiaClient client(make_ffi_backend(stand_in)); }
    CHECK(count() == before + 1);
}

TEST_CASE("the FFI backend frees the string the kernel handed it", "[ffi][marshal]") {
    // Every string-returning entry hands the backend a block the kernel
    // allocated, and the backend releases it once it has copied the text; a
    // release left out leaks, which no test observes by the text alone.
    if (find_ffi_library().empty())
        SKIP("no kernel library holds the process, so the stand-in must not be its first backend");
    const std::filesystem::path stand_in{ALETHEIA_TEST_RECORDING_KERNEL};
    const aletheia::test::LoadedLibrary handle{dlopen(stand_in.c_str(), RTLD_NOW)};
    REQUIRE(handle != nullptr);
    auto* const count = recording_kernel_counter(handle, "aletheia_test_free_count");
    auto const backend = make_ffi_backend(stand_in);
    auto const state = backend->init();
    auto const before = count();
    CHECK_THAT(backend->process(state, "{}"), ContainsSubstring("process size=2"));
    CHECK(count() == before + 1);
}

TEST_CASE("the kernel's allocation count grows across a DBC load", "[ffi][allocation]") {
    // The count is the runtime's, read through the library that started it,
    // and a load between two reads allocates in the kernel.
    auto const lib = find_ffi_library();
    if (lib.empty())
        SKIP("no kernel library to load");
    auto const dbc = aletheia::test::make_integration_dbc();
    AletheiaClient client(make_ffi_backend(lib));
    auto const before = allocated_bytes();
    REQUIRE(client.parse_dbc(std::stop_token{}, dbc).has_value());
    auto const after = allocated_bytes();
    REQUIRE(before.has_value());
    REQUIRE(after.has_value());
    CHECK(after.value() > before.value());
}

TEST_CASE("a later backend leaves the allocation count on the library that started the runtime",
          "[ffi][allocation]") {
    // The recording kernel answers each read of its count with one more than
    // the last, so two reads of its entry around the process's read are one
    // apart only when the process's read went to the library that started the
    // runtime instead.
    if (find_ffi_library().empty())
        SKIP("no kernel library holds the process, so the stand-in must not be its first backend");
    auto const lib = stand_in(ALETHEIA_TEST_RECORDING_KERNEL);
    const aletheia::test::LoadedLibrary handle{dlopen(lib.c_str(), RTLD_NOW)};
    REQUIRE(handle != nullptr);
    auto const symbol = aletheia::detail::dl_symbol(handle.get(), "aletheia_allocated_bytes");
    REQUIRE(symbol.has_value());
    auto* const entry = aletheia::detail::symbol_as<std::uint64_t (*)()>(symbol.value());
    auto const backend = make_ffi_backend(lib);
    auto const before = entry();
    REQUIRE(allocated_bytes().has_value());
    CHECK(entry() == before + 1);
}

TEST_CASE("the search's default library path is the first one registered", "[ffi][search]") {
    // The start registers the library it loaded as the search's default,
    // first write wins; a later registration of another library, here one that
    // exists but carries no entry, changes nothing the lookup answers. With the
    // environment unset the lookup reads the default, which is what is compared.
    const ScopedAletheiaLib unset(nullptr);
    auto const before = find_ffi_library();
    REQUIRE_FALSE(before.empty());
    aletheia::detail::register_default_lib_path(
        std::filesystem::path{ALETHEIA_TEST_SYMBOLLESS_LIB});
    CHECK(find_ffi_library() == before);
}
