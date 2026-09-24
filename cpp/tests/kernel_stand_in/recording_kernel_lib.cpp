// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// A kernel stand-in that answers every call with a refusal quoting what it
// was handed, so a test can read what the backend marshals to the kernel
// entries whose arguments the real kernel acknowledges without reading: the
// timestamp of an error or remote event, and the CAN-FD bus bits of a frame.
// It carries every symbol the backend resolves, at the kernel's own
// signatures, and its runtime entry is a no-op: the runtime is brought up
// once per process by the first backend the suite builds, on the real
// library, and never by this one.
#include <atomic>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <string>

// The message the backend frees through aletheia_free_str, so it is one
// block from the allocator the kernel's own strings come from.
static auto handed_back(const std::string& text) -> char* {
    auto const size = text.size() + 1;
    // NOLINTNEXTLINE(cppcoreguidelines-no-malloc): released by aletheia_free_str
    auto* out = static_cast<char*>(std::malloc(size));
    if (out != nullptr)
        std::memcpy(out, text.c_str(), size);
    return out;
}

static auto refusal(const std::string& detail) -> char* {
    return handed_back(R"({"status":"error","code":"recording_kernel","message":")" + detail +
                       "\"}");
}

static auto u(std::uint64_t v) -> std::string {
    return std::to_string(v);
}

extern "C" {

void hs_init_with_rtsopts(int* /*argc*/, char*** /*argv*/) {
}

auto aletheia_init() -> void* {
    static int state = 0;
    return &state;
}

// Closes are counted so a test can read that the state it opened was closed,
// which the real kernel acknowledges without reading.
std::atomic<int> closes{0};
void aletheia_close(void* /*state*/) {
    ++closes;
}
auto aletheia_test_close_count() -> int {
    return closes.load();
}

void aletheia_free_str(char* p) {
    std::free(p); // NOLINT(cppcoreguidelines-no-malloc): pairs with handed_back
}

void aletheia_free_buf(std::uint8_t* /*buf*/) {
}

auto aletheia_process(void* /*state*/, const char* /*input*/) -> char* {
    return refusal("process");
}

auto aletheia_start_stream(void* /*state*/) -> char* {
    return refusal("start_stream");
}

auto aletheia_end_stream(void* /*state*/) -> char* {
    return refusal("end_stream");
}

auto aletheia_format_dbc(void* /*state*/) -> char* {
    return refusal("format_dbc");
}

auto aletheia_send_error(void* /*state*/, std::uint64_t ts) -> char* {
    return refusal("send_error ts=" + u(ts));
}

auto aletheia_send_remote(void* /*state*/, std::uint64_t ts, std::uint32_t id,
                          std::uint8_t extended) -> char* {
    return refusal("send_remote ts=" + u(ts) + " id=" + u(id) + " extended=" + u(extended));
}

auto aletheia_send_frame(void* /*state*/, std::uint64_t ts, std::uint32_t id, std::uint8_t extended,
                         std::uint8_t dlc, const std::uint8_t* /*data*/, std::uint8_t len,
                         std::uint8_t brs_present, std::uint8_t brs_value, std::uint8_t esi_present,
                         std::uint8_t esi_value) -> char* {
    return refusal("send_frame ts=" + u(ts) + " id=" + u(id) + " extended=" + u(extended) +
                   " dlc=" + u(dlc) + " len=" + u(len) + " brs=" + u(brs_present) + "/" +
                   u(brs_value) + " esi=" + u(esi_present) + "/" + u(esi_value));
}

// The renderer's three entries, so the stand-in serves it too: what the
// backend hands the kernel is the question, and a render answers nothing.
auto aletheia_format_rational(std::int64_t num, std::int64_t den) -> char* {
    return handed_back(u(static_cast<std::uint64_t>(num)) + "/" +
                       u(static_cast<std::uint64_t>(den)));
}

auto aletheia_parse_decimal(const char* /*input*/) -> char* {
    return refusal("parse_decimal");
}

auto aletheia_extract_signals(void* /*state*/, std::uint32_t /*id*/, std::uint8_t /*extended*/,
                              std::uint8_t /*dlc*/, const std::uint8_t* /*data*/,
                              std::uint8_t /*len*/) -> char* {
    return refusal("extract_signals");
}

// The three binary entries refuse with the bare message, as the kernel's do.
auto aletheia_build_frame_bin(void* /*state*/, std::uint32_t /*id*/, std::uint8_t /*extended*/,
                              std::uint8_t /*dlc*/, std::uint32_t /*count*/,
                              const std::uint32_t* /*indices*/, const std::int64_t* /*nums*/,
                              const std::int64_t* /*dens*/, std::uint8_t* /*out*/, char** err)
    -> std::int8_t {
    *err = handed_back("build_frame_bin");
    return 1;
}

auto aletheia_update_frame_bin(void* /*state*/, std::uint32_t /*id*/, std::uint8_t /*extended*/,
                               std::uint8_t /*dlc*/, const std::uint8_t* /*data*/,
                               std::uint8_t /*len*/, std::uint32_t /*count*/,
                               const std::uint32_t* /*indices*/, const std::int64_t* /*nums*/,
                               const std::int64_t* /*dens*/, std::uint8_t* /*out*/, char** err)
    -> std::int8_t {
    *err = handed_back("update_frame_bin");
    return 1;
}

auto aletheia_extract_signals_bin(void* /*state*/, std::uint32_t /*id*/, std::uint8_t /*extended*/,
                                  std::uint8_t /*dlc*/, const std::uint8_t* /*data*/,
                                  std::uint8_t /*len*/, std::uint8_t** /*out*/,
                                  std::uint32_t* /*out_size*/, char** err) -> std::int8_t {
    *err = handed_back("extract_signals_bin");
    return 1;
}

} // extern "C"
