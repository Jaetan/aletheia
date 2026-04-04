/*
 * Microbenchmark: bytesToAgdaVec and frame construction scaling.
 *
 * Sends frames with varying payload sizes (CAN 2.0B through CAN-FD)
 * using a CAN ID that has no DBC signals (0x999), so signal cache
 * updates are a no-op. This isolates:
 *   - peekArray (C ptr → [Word8])
 *   - bytesToAgdaVec ([Word8] → MAlonzo Vec)
 *   - TimedFrame/CANFrame construction
 *   - Response serialization (constant — always Ack)
 *
 * The response serialization is constant across all sizes (always Ack),
 * so the delta between sizes is purely frame construction cost.
 *
 * Build:
 *   gcc -O2 -o vec_construction benchmarks/vec_construction.c -ldl
 *
 * Run:
 *   LD_LIBRARY_PATH=build ./vec_construction
 */

#include <dlfcn.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <stdint.h>

typedef void  (*hs_init_t)(int *, char ***);
typedef void *(*init_t)(void);
typedef char *(*process_t)(void *, const char *);
typedef char *(*send_frame_t)(void *, uint64_t, uint32_t, uint8_t, uint8_t,
                              const uint8_t *, uint8_t);
typedef void  (*free_str_t)(char *);
typedef void  (*close_t)(void *);

static hs_init_t    fn_hs_init;
static init_t       fn_init;
static process_t    fn_process;
static send_frame_t fn_send_frame;
static free_str_t   fn_free_str;
static close_t      fn_close;

static void *load_lib(const char *path) {
    void *lib = dlopen(path, RTLD_NOW | RTLD_GLOBAL);
    if (!lib) { fprintf(stderr, "dlopen: %s\n", dlerror()); exit(1); }
    fn_hs_init    = (hs_init_t)dlsym(lib, "hs_init");
    fn_init       = (init_t)dlsym(lib, "aletheia_init");
    fn_process    = (process_t)dlsym(lib, "aletheia_process");
    fn_send_frame = (send_frame_t)dlsym(lib, "aletheia_send_frame");
    fn_free_str   = (free_str_t)dlsym(lib, "aletheia_free_str");
    fn_close      = (close_t)dlsym(lib, "aletheia_close");
    return lib;
}

/* DBC with one message on 0x100 — we'll send on 0x999 to avoid cache work */
static const char *DBC_JSON =
    "{\"type\":\"command\",\"command\":\"parseDBC\",\"dbc\":{"
    "\"version\":\"1.0\",\"messages\":["
    "{\"id\":256,\"name\":\"Msg\",\"dlc\":8,\"sender\":\"ECU\",\"signals\":["
    "{\"name\":\"Speed\",\"startBit\":0,\"length\":16,"
    "\"byteOrder\":\"little_endian\",\"signed\":false,"
    "\"factor\":0.25,\"offset\":0,\"minimum\":0,\"maximum\":16383,"
    "\"unit\":\"km/h\",\"presence\":\"always\"}"
    "]}]}}";

static const char *PROP_NONE =
    "{\"type\":\"command\",\"command\":\"setProperties\",\"properties\":[]}";
static const char *START =
    "{\"type\":\"command\",\"command\":\"startStream\"}";
static const char *END =
    "{\"type\":\"command\",\"command\":\"endStream\"}";

static double elapsed_ns(struct timespec *start, struct timespec *end) {
    return (double)(end->tv_sec - start->tv_sec) * 1e9 +
           (double)(end->tv_nsec - start->tv_nsec);
}

/* CAN-FD DLC → byte count mapping */
static const struct { uint8_t dlc; uint8_t bytes; const char *label; } dlc_table[] = {
    { 0,   0, " 0 bytes (DLC 0)" },
    { 1,   1, " 1 byte  (DLC 1)" },
    { 2,   2, " 2 bytes (DLC 2)" },
    { 4,   4, " 4 bytes (DLC 4)" },
    { 8,   8, " 8 bytes (DLC 8)  — CAN 2.0B max" },
    { 9,  12, "12 bytes (DLC 9)" },
    {10,  16, "16 bytes (DLC 10)" },
    {11,  20, "20 bytes (DLC 11)" },
    {12,  24, "24 bytes (DLC 12)" },
    {13,  32, "32 bytes (DLC 13)" },
    {14,  48, "48 bytes (DLC 14)" },
    {15,  64, "64 bytes (DLC 15) — CAN-FD max" },
};
#define DLC_TABLE_SIZE (sizeof(dlc_table) / sizeof(dlc_table[0]))

static double bench_payload(void *state, uint8_t dlc, uint8_t data_len,
                            int frames, int runs) {
    uint8_t data[64];
    memset(data, 0x42, sizeof(data));

    double best = 1e18;
    for (int r = 0; r < runs; r++) {
        /* Warmup */
        for (int i = 0; i < 2000; i++) {
            char *resp = fn_send_frame(state, (uint64_t)i * 1000,
                                       0x999, 0, dlc, data, data_len);
            fn_free_str(resp);
        }

        struct timespec t0, t1;
        clock_gettime(CLOCK_MONOTONIC, &t0);
        for (int i = 0; i < frames; i++) {
            char *resp = fn_send_frame(state, (uint64_t)(2000 + i) * 1000,
                                       0x999, 0, dlc, data, data_len);
            fn_free_str(resp);
        }
        clock_gettime(CLOCK_MONOTONIC, &t1);

        double ns_per = elapsed_ns(&t0, &t1) / frames;
        if (ns_per < best) best = ns_per;
    }
    return best;
}

int main(void) {
    void *lib = load_lib("build/libaletheia-ffi.so");

    int argc = 3;
    char *argv_data[] = {"bench", "+RTS", "-N1", NULL};
    char **argv = argv_data;
    fn_hs_init(&argc, &argv);

    printf("bytesToAgdaVec + frame construction scaling\n");
    printf("Library: build/libaletheia-ffi.so\n");
    printf("0 properties, CAN ID 0x999 (no signal cache work)\n\n");

    int frames = 100000;
    int runs = 5;

    /* Set up one session for all tests */
    void *state = fn_init();
    char *r;
    r = fn_process(state, DBC_JSON);
    if (!strstr(r, "success")) {
        fprintf(stderr, "parseDBC failed: %s\n", r);
        return 1;
    }
    fn_free_str(r);
    r = fn_process(state, PROP_NONE);
    fn_free_str(r);
    r = fn_process(state, START);
    fn_free_str(r);

    /* Run benchmarks for each payload size */
    printf("%-36s  %10s  %10s  %10s\n",
           "Payload", "ns/frame", "fps", "ns/byte");
    printf("%-36s  %10s  %10s  %10s\n",
           "-------", "--------", "---", "-------");

    double results[DLC_TABLE_SIZE];
    for (size_t i = 0; i < DLC_TABLE_SIZE; i++) {
        double ns = bench_payload(state, dlc_table[i].dlc,
                                  dlc_table[i].bytes, frames, runs);
        results[i] = ns;
        double fps = 1e9 / ns;
        double ns_per_byte = dlc_table[i].bytes > 0
            ? ns / dlc_table[i].bytes : 0;
        printf("%-36s  %10.1f  %10.0f  %10.1f\n",
               dlc_table[i].label, ns, fps, ns_per_byte);
    }

    /* End session */
    r = fn_process(state, END);
    fn_free_str(r);
    fn_close(state);

    /* Analysis */
    printf("\n=== Analysis ===\n");
    double base = results[0];  /* 0-byte payload */
    printf("  Fixed overhead (0 bytes):          %8.1f ns\n", base);
    printf("  (= FFI + dispatch + serialize + CString)\n\n");

    printf("  Marginal cost of payload bytes:\n");
    for (size_t i = 1; i < DLC_TABLE_SIZE; i++) {
        double delta = results[i] - base;
        double per_byte = delta / dlc_table[i].bytes;
        printf("    %2d bytes: %+8.1f ns total, %6.1f ns/byte\n",
               dlc_table[i].bytes, delta, per_byte);
    }

    printf("\n  CAN 2.0B (8 bytes) vs CAN-FD (64 bytes):\n");
    double can20 = results[4];   /* 8 bytes */
    double canfd = results[11];  /* 64 bytes */
    printf("    CAN 2.0B:  %8.1f ns/frame\n", can20);
    printf("    CAN-FD:    %8.1f ns/frame\n", canfd);
    printf("    Delta:     %8.1f ns  (%.1fx)\n", canfd - can20,
           canfd / can20);
    printf("    Per extra byte (56 bytes): %.1f ns/byte\n",
           (canfd - can20) / 56.0);

    dlclose(lib);
    return 0;
}
