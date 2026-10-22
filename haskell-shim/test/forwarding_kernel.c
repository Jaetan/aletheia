// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// A kernel stand-in that hands every entry to the kernel ALETHEIA_FORWARD_TO
// names and appends each refusal that kernel answers to the file
// ALETHEIA_REFUSAL_LOG names, so a test reads every call the kernel refused,
// whatever the caller did with the answer. The doc-example harnesses and the
// demo-script runs load it in place of the library: an example that discards
// a refused call passes on its exit status alone, and the log is what fails
// it. A refusal is the error envelope every entry answers with, a returned
// string or a binary entry's err; each is one line of the log, the entry's
// name, a tab and the envelope. Both variables are read at the first call,
// which aborts the process naming what is missing. The build makes it beside
// the library, where the bindings' tests load it.
#include "aletheia.h"

#include <dlfcn.h>
#include <fcntl.h>
#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

// Every entry of the library, resolved once from the kernel it forwards to.
static struct {
    void (*hs_init_with_rtsopts)(int *, char ***);
    __typeof__(&aletheia_abi_version) abi_version;
    __typeof__(&aletheia_init) init;
    __typeof__(&aletheia_close) close;
    __typeof__(&aletheia_free_str) free_str;
    __typeof__(&aletheia_free_buf) free_buf;
    __typeof__(&aletheia_allocated_bytes) allocated_bytes;
    __typeof__(&aletheia_format_rational) format_rational;
    __typeof__(&aletheia_parse_decimal) parse_decimal;
    __typeof__(&aletheia_process) process;
    __typeof__(&aletheia_send_frame) send_frame;
    __typeof__(&aletheia_send_error) send_error;
    __typeof__(&aletheia_send_remote) send_remote;
    __typeof__(&aletheia_start_stream) start_stream;
    __typeof__(&aletheia_end_stream) end_stream;
    __typeof__(&aletheia_format_dbc) format_dbc;
    __typeof__(&aletheia_extract_signals) extract_signals;
    __typeof__(&aletheia_build_frame_bin) build_frame_bin;
    __typeof__(&aletheia_update_frame_bin) update_frame_bin;
    __typeof__(&aletheia_extract_signals_bin) extract_signals_bin;
} kernel;

static const char *log_path;

static _Noreturn void fail(const char *what, const char *detail) {
    fprintf(stderr, "forwarding_kernel: %s: %s\n", what, detail);
    abort();
}

static void *resolve(void *handle, const char *name) {
    void *entry = dlsym(handle, name);
    if (entry == NULL)
        fail("missing entry", name);
    return entry;
}

static void open_kernel(void) {
    const char *path = getenv("ALETHEIA_FORWARD_TO");
    if (path == NULL)
        fail("ALETHEIA_FORWARD_TO", "unset");
    log_path = getenv("ALETHEIA_REFUSAL_LOG");
    if (log_path == NULL)
        fail("ALETHEIA_REFUSAL_LOG", "unset");
    void *handle = dlopen(path, RTLD_NOW | RTLD_LOCAL);
    if (handle == NULL)
        fail("ALETHEIA_FORWARD_TO", dlerror());
    kernel.hs_init_with_rtsopts = resolve(handle, "hs_init_with_rtsopts");
    kernel.abi_version = resolve(handle, "aletheia_abi_version");
    kernel.init = resolve(handle, "aletheia_init");
    kernel.close = resolve(handle, "aletheia_close");
    kernel.free_str = resolve(handle, "aletheia_free_str");
    kernel.free_buf = resolve(handle, "aletheia_free_buf");
    kernel.allocated_bytes = resolve(handle, "aletheia_allocated_bytes");
    kernel.format_rational = resolve(handle, "aletheia_format_rational");
    kernel.parse_decimal = resolve(handle, "aletheia_parse_decimal");
    kernel.process = resolve(handle, "aletheia_process");
    kernel.send_frame = resolve(handle, "aletheia_send_frame");
    kernel.send_error = resolve(handle, "aletheia_send_error");
    kernel.send_remote = resolve(handle, "aletheia_send_remote");
    kernel.start_stream = resolve(handle, "aletheia_start_stream");
    kernel.end_stream = resolve(handle, "aletheia_end_stream");
    kernel.format_dbc = resolve(handle, "aletheia_format_dbc");
    kernel.extract_signals = resolve(handle, "aletheia_extract_signals");
    kernel.build_frame_bin = resolve(handle, "aletheia_build_frame_bin");
    kernel.update_frame_bin = resolve(handle, "aletheia_update_frame_bin");
    kernel.extract_signals_bin = resolve(handle, "aletheia_extract_signals_bin");
}

static void forward(void) {
    static pthread_once_t once = PTHREAD_ONCE_INIT;
    pthread_once(&once, open_kernel);
}

// The kernel writes every envelope with this opening, so a reply that starts
// any other way is an answer, not a refusal.
static void record(const char *entry, const char *reply) {
    static const char refusal[] = "{\"status\": \"error\"";
    if (reply == NULL || strncmp(reply, refusal, sizeof refusal - 1) != 0)
        return;
    int fd = open(log_path, O_WRONLY | O_APPEND | O_CREAT | O_CLOEXEC, 0644);
    if (fd < 0)
        fail("ALETHEIA_REFUSAL_LOG", log_path);
    dprintf(fd, "%s\t%s\n", entry, reply);
    close(fd);
}

void hs_init_with_rtsopts(int *argc, char ***argv) {
    forward();
    kernel.hs_init_with_rtsopts(argc, argv);
}

uint32_t aletheia_abi_version(void) {
    forward();
    return kernel.abi_version();
}

void *aletheia_init(void) {
    forward();
    return kernel.init();
}

void aletheia_close(void *state) {
    forward();
    kernel.close(state);
}

void aletheia_free_str(char *ptr) {
    forward();
    kernel.free_str(ptr);
}

void aletheia_free_buf(uint8_t *ptr) {
    forward();
    kernel.free_buf(ptr);
}

uint64_t aletheia_allocated_bytes(void) {
    forward();
    return kernel.allocated_bytes();
}

char *aletheia_format_rational(const struct aletheia_rational *value) {
    forward();
    return kernel.format_rational(value);
}

int8_t aletheia_parse_decimal(const struct aletheia_text *input, struct aletheia_decimal *out) {
    forward();
    int8_t status = kernel.parse_decimal(input, out);
    if (status != 0 && out != NULL)
        record("aletheia_parse_decimal", out->err);
    return status;
}

char *aletheia_process(void *state, const struct aletheia_text *input) {
    forward();
    char *reply = kernel.process(state, input);
    record("aletheia_process", reply);
    return reply;
}

char *aletheia_send_frame(void *state, const struct aletheia_frame *frame) {
    forward();
    char *reply = kernel.send_frame(state, frame);
    record("aletheia_send_frame", reply);
    return reply;
}

char *aletheia_send_error(void *state, const struct aletheia_frame *frame) {
    forward();
    char *reply = kernel.send_error(state, frame);
    record("aletheia_send_error", reply);
    return reply;
}

char *aletheia_send_remote(void *state, const struct aletheia_frame *frame) {
    forward();
    char *reply = kernel.send_remote(state, frame);
    record("aletheia_send_remote", reply);
    return reply;
}

char *aletheia_start_stream(void *state) {
    forward();
    char *reply = kernel.start_stream(state);
    record("aletheia_start_stream", reply);
    return reply;
}

char *aletheia_end_stream(void *state) {
    forward();
    char *reply = kernel.end_stream(state);
    record("aletheia_end_stream", reply);
    return reply;
}

char *aletheia_format_dbc(void *state) {
    forward();
    char *reply = kernel.format_dbc(state);
    record("aletheia_format_dbc", reply);
    return reply;
}

char *aletheia_extract_signals(void *state, const struct aletheia_frame *frame) {
    forward();
    char *reply = kernel.extract_signals(state, frame);
    record("aletheia_extract_signals", reply);
    return reply;
}

int8_t aletheia_build_frame_bin(void *state, const struct aletheia_frame *frame,
                                const struct aletheia_signal_values *values,
                                struct aletheia_buffer *out) {
    forward();
    int8_t status = kernel.build_frame_bin(state, frame, values, out);
    if (status != 0 && out != NULL)
        record("aletheia_build_frame_bin", out->err);
    return status;
}

int8_t aletheia_update_frame_bin(void *state, const struct aletheia_frame *frame,
                                 const struct aletheia_signal_values *values,
                                 struct aletheia_buffer *out) {
    forward();
    int8_t status = kernel.update_frame_bin(state, frame, values, out);
    if (status != 0 && out != NULL)
        record("aletheia_update_frame_bin", out->err);
    return status;
}

int8_t aletheia_extract_signals_bin(void *state, const struct aletheia_frame *frame,
                                    struct aletheia_buffer *out) {
    forward();
    int8_t status = kernel.extract_signals_bin(state, frame, out);
    if (status != 0 && out != NULL)
        record("aletheia_extract_signals_bin", out->err);
    return status;
}
