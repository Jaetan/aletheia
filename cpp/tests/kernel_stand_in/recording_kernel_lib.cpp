// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// A kernel stand-in that answers every call with a refusal quoting what it
// was handed, so a test can read what the backend marshals to the kernel
// entries whose arguments the real kernel acknowledges without reading: the
// timestamp of an error or remote event, the CAN-FD bus bits of a frame, and
// the size of a command's text.
// It carries every symbol the backend resolves, at the kernel's own
// signatures, its structures the backend's own mirror of the kernel's (so the
// undefined-behaviour sanitizer's function-type check holds every entry to the
// type the backend calls it through), and its runtime entry is a no-op: the
// runtime is brought up once per process by the first backend the suite
// builds, on the real library, and never by this one.
#include "detail/ffi_abi.hpp"

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

using aletheia::detail::FfiBuffer;
using aletheia::detail::FfiDecimal;
using aletheia::detail::FfiFrame;
using aletheia::detail::FfiRational;
using aletheia::detail::FfiSignalValues;
using aletheia::detail::FfiText;

extern "C" {

auto aletheia_abi_version() -> std::uint32_t {
    return aletheia::detail::abi_version;
}

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

auto aletheia_process(void* /*state*/, const FfiText* input) -> char* {
    return refusal("process size=" + u(input->size));
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

auto aletheia_send_error(void* /*state*/, const FfiFrame* frame) -> char* {
    return refusal("send_error ts=" + u(frame->timestamp));
}

auto aletheia_send_remote(void* /*state*/, const FfiFrame* frame) -> char* {
    return refusal("send_remote ts=" + u(frame->timestamp) + " id=" + u(frame->can_id) +
                   " extended=" + u(frame->extended));
}

auto aletheia_send_frame(void* /*state*/, const FfiFrame* frame) -> char* {
    return refusal("send_frame ts=" + u(frame->timestamp) + " id=" + u(frame->can_id) +
                   " extended=" + u(frame->extended) + " dlc=" + u(frame->dlc) +
                   " len=" + u(frame->data_len) + " brs=" + u(frame->brs_present) + "/" +
                   u(frame->brs_value) + " esi=" + u(frame->esi_present) + "/" +
                   u(frame->esi_value));
}

// The renderer's three entries, so the stand-in serves it too: what the
// backend hands the kernel is the question, and a render answers nothing.
auto aletheia_format_rational(const FfiRational* value) -> char* {
    return handed_back(u(static_cast<std::uint64_t>(value->numerator)) + "/" +
                       u(static_cast<std::uint64_t>(value->denominator)));
}

auto aletheia_parse_decimal(const FfiText* /*input*/, FfiDecimal* out) -> std::int8_t {
    out->err = refusal("parse_decimal");
    return 1;
}

auto aletheia_extract_signals(void* /*state*/, const FfiFrame* /*frame*/) -> char* {
    return refusal("extract_signals");
}

// The three binary entries refuse with the bare message, as the kernel's do.
auto aletheia_build_frame_bin(void* /*state*/, const FfiFrame* /*frame*/,
                              const FfiSignalValues* /*values*/, FfiBuffer* out) -> std::int8_t {
    out->err = handed_back("build_frame_bin");
    return 1;
}

auto aletheia_update_frame_bin(void* /*state*/, const FfiFrame* /*frame*/,
                               const FfiSignalValues* /*values*/, FfiBuffer* out) -> std::int8_t {
    out->err = handed_back("update_frame_bin");
    return 1;
}

auto aletheia_extract_signals_bin(void* /*state*/, const FfiFrame* /*frame*/, FfiBuffer* out)
    -> std::int8_t {
    out->err = handed_back("extract_signals_bin");
    return 1;
}

} // extern "C"
