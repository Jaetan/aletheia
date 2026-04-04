/*
 * Microbenchmark: Agda/Haskell response serialization overhead.
 *
 * Loads libaletheia-ffi.so directly and measures per-frame round-trip time
 * with varying numbers of LTL properties. The 0-property case isolates the
 * frame dispatch + response serialization + CString allocation cost.
 *
 * Build:
 *   gcc -O2 -o response_overhead_ffi benchmarks/response_overhead_ffi.c -ldl
 *
 * Run:
 *   LD_LIBRARY_PATH=build ./response_overhead_ffi
 */

#include <dlfcn.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <stdint.h>

/* Function pointer types matching aletheia.h */
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
    if (!lib) {
        fprintf(stderr, "dlopen: %s\n", dlerror());
        exit(1);
    }
    fn_hs_init    = (hs_init_t)dlsym(lib, "hs_init");
    fn_init       = (init_t)dlsym(lib, "aletheia_init");
    fn_process    = (process_t)dlsym(lib, "aletheia_process");
    fn_send_frame = (send_frame_t)dlsym(lib, "aletheia_send_frame");
    fn_free_str   = (free_str_t)dlsym(lib, "aletheia_free_str");
    fn_close      = (close_t)dlsym(lib, "aletheia_close");
    if (!fn_hs_init || !fn_init || !fn_process || !fn_send_frame ||
        !fn_free_str || !fn_close) {
        fprintf(stderr, "Missing symbol: %s\n", dlerror());
        exit(1);
    }
    return lib;
}

/* Send a JSON command, free response, return it (caller must not use after next call) */
static char *cmd(void *state, const char *json) {
    char *resp = fn_process(state, json);
    return resp; /* caller frees */
}

/* Simple DBC with one message, one signal */
static const char *DBC_JSON =
    "{\"type\":\"command\",\"command\":\"parseDBC\",\"dbc\":{"
    "\"version\":\"1.0\",\"messages\":["
    "{\"id\":256,\"name\":\"Msg\",\"dlc\":8,\"sender\":\"ECU\",\"signals\":["
    "{\"name\":\"Speed\",\"startBit\":0,\"length\":16,"
    "\"byteOrder\":\"little_endian\",\"signed\":false,"
    "\"factor\":0.25,\"offset\":0,\"minimum\":0,\"maximum\":16383,"
    "\"unit\":\"km/h\",\"presence\":\"always\"}"
    "]}]}}";

/* LTL property: G(Speed < 16383) — always satisfied by our test frames */
static const char *PROP_ALWAYS =
    "{\"type\":\"command\",\"command\":\"setProperties\",\"properties\":["
    "{\"op\":\"Always\",\"arg\":{\"op\":\"Atomic\","
    "\"pred\":{\"type\":\"comparison\",\"signal\":\"Speed\","
    "\"cmp\":\"LessThan\",\"value\":{\"numerator\":16383,\"denominator\":1}}}}"
    "]}";

/* No properties */
static const char *PROP_NONE =
    "{\"type\":\"command\",\"command\":\"setProperties\",\"properties\":[]}";

static const char *START = "{\"type\":\"command\",\"command\":\"startStream\"}";
static const char *END   = "{\"type\":\"command\",\"command\":\"endStream\"}";

static double elapsed_ns(struct timespec *start, struct timespec *end) {
    return (double)(end->tv_sec - start->tv_sec) * 1e9 +
           (double)(end->tv_nsec - start->tv_nsec);
}

typedef struct {
    double total_ns;
    double ns_per_frame;
    double fps;
    int ack_count;
    int other_count;
} bench_result;

static bench_result run_bench(void *state, int frames, const uint8_t *data,
                              uint8_t data_len) {
    bench_result r = {0};
    struct timespec t0, t1;

    /* Warmup: 1000 frames */
    for (int i = 0; i < 1000; i++) {
        char *resp = fn_send_frame(state, (uint64_t)i * 1000, 256, 0, 8,
                                   data, data_len);
        fn_free_str(resp);
    }

    clock_gettime(CLOCK_MONOTONIC, &t0);
    for (int i = 0; i < frames; i++) {
        char *resp = fn_send_frame(state, (uint64_t)(1000 + i) * 1000, 256, 0,
                                   8, data, data_len);
        /* {"status": "ack"} — check byte 12 for 'a' */
        if (resp[12] == 'a')
            r.ack_count++;
        else
            r.other_count++;
        fn_free_str(resp);
    }
    clock_gettime(CLOCK_MONOTONIC, &t1);

    r.total_ns = elapsed_ns(&t0, &t1);
    r.ns_per_frame = r.total_ns / frames;
    r.fps = 1e9 / r.ns_per_frame;
    return r;
}

static void setup_session(void *state, const char *props_cmd) {
    char *r;

    r = cmd(state, DBC_JSON);
    if (!strstr(r, "success")) {
        fprintf(stderr, "parseDBC failed: %s\n", r);
        exit(1);
    }
    fn_free_str(r);

    r = cmd(state, props_cmd);
    fn_free_str(r);

    r = cmd(state, START);
    fn_free_str(r);
}

static void end_session(void *state) {
    char *r = cmd(state, END);
    fn_free_str(r);
}

int main(void) {
    const char *lib_path = "build/libaletheia-ffi.so";
    void *lib = load_lib(lib_path);

    /* Init GHC RTS with -N1 (single-threaded, matches default) */
    int argc = 3;
    char *argv_data[] = {"bench", "+RTS", "-N1", NULL};
    char **argv = argv_data;
    fn_hs_init(&argc, &argv);

    printf("Response serialization overhead (Agda/Haskell side)\n");
    printf("Library: %s\n\n", lib_path);

    uint8_t frame_data[8] = {0x00, 0x04, 0, 0, 0, 0, 0, 0}; /* Speed = 1024 * 0.25 = 256 */
    int frames = 500000;
    int runs = 7;

    /* ============================================================ */
    /* Benchmark 1: 0 properties (pure dispatch + serialization)    */
    /* ============================================================ */
    printf("=== 0 properties (dispatch + serialize only) ===\n");
    double best_0 = 1e18;
    for (int r = 0; r < runs; r++) {
        void *state = fn_init();
        setup_session(state, PROP_NONE);
        bench_result br = run_bench(state, frames, frame_data, 8);
        end_session(state);
        fn_close(state);
        printf("  Run %d: %8.1f ns/frame  (%7.0f fps)  ack=%d other=%d\n",
               r + 1, br.ns_per_frame, br.fps, br.ack_count, br.other_count);
        if (br.ns_per_frame < best_0) best_0 = br.ns_per_frame;
    }
    printf("  Best:  %8.1f ns/frame\n\n", best_0);

    /* ============================================================ */
    /* Benchmark 2: 1 property (dispatch + LTL step + serialize)    */
    /* ============================================================ */
    printf("=== 1 property (dispatch + 1x LTL step + serialize) ===\n");
    double best_1 = 1e18;
    for (int r = 0; r < runs; r++) {
        void *state = fn_init();
        setup_session(state, PROP_ALWAYS);
        bench_result br = run_bench(state, frames, frame_data, 8);
        end_session(state);
        fn_close(state);
        printf("  Run %d: %8.1f ns/frame  (%7.0f fps)  ack=%d other=%d\n",
               r + 1, br.ns_per_frame, br.fps, br.ack_count, br.other_count);
        if (br.ns_per_frame < best_1) best_1 = br.ns_per_frame;
    }
    printf("  Best:  %8.1f ns/frame\n\n", best_1);

    /* ============================================================ */
    /* Benchmark 3: 2 properties                                    */
    /* ============================================================ */
    static const char *PROP_TWO =
        "{\"type\":\"command\",\"command\":\"setProperties\",\"properties\":["
        "{\"op\":\"Always\",\"arg\":{\"op\":\"Atomic\","
        "\"pred\":{\"type\":\"comparison\",\"signal\":\"Speed\","
        "\"cmp\":\"LessThan\",\"value\":{\"numerator\":16383,\"denominator\":1}}}},"
        "{\"op\":\"Always\",\"arg\":{\"op\":\"Atomic\","
        "\"pred\":{\"type\":\"comparison\",\"signal\":\"Speed\","
        "\"cmp\":\"GreaterThanOrEqual\",\"value\":{\"numerator\":0,\"denominator\":1}}}}"
        "]}";

    printf("=== 2 properties (dispatch + 2x LTL step + serialize) ===\n");
    double best_2 = 1e18;
    for (int r = 0; r < runs; r++) {
        void *state = fn_init();
        setup_session(state, PROP_TWO);
        bench_result br = run_bench(state, frames, frame_data, 8);
        end_session(state);
        fn_close(state);
        printf("  Run %d: %8.1f ns/frame  (%7.0f fps)  ack=%d other=%d\n",
               r + 1, br.ns_per_frame, br.fps, br.ack_count, br.other_count);
        if (br.ns_per_frame < best_2) best_2 = br.ns_per_frame;
    }
    printf("  Best:  %8.1f ns/frame\n\n", best_2);

    /* ============================================================ */
    /* Benchmark 4: malloc+free baseline (string allocation only)   */
    /* ============================================================ */
    printf("=== malloc+free baseline (what CString alloc costs in C) ===\n");
    static const char ack_str[] = "{\"status\": \"ack\"}";
    double best_alloc = 1e18;
    for (int r = 0; r < runs; r++) {
        struct timespec ta, tb;
        /* Warmup */
        for (int i = 0; i < 1000; i++) {
            char *s = malloc(sizeof(ack_str));
            memcpy(s, ack_str, sizeof(ack_str));
            volatile char c = s[12]; /* prevent optimization */
            (void)c;
            free(s);
        }
        clock_gettime(CLOCK_MONOTONIC, &ta);
        for (int i = 0; i < frames; i++) {
            char *s = malloc(sizeof(ack_str));
            memcpy(s, ack_str, sizeof(ack_str));
            volatile char c = s[12];
            (void)c;
            free(s);
        }
        clock_gettime(CLOCK_MONOTONIC, &tb);
        double ns_per = elapsed_ns(&ta, &tb) / frames;
        printf("  Run %d: %8.1f ns/op\n", r + 1, ns_per);
        if (ns_per < best_alloc) best_alloc = ns_per;
    }
    printf("  Best:  %8.1f ns/op\n\n", best_alloc);

    /* ============================================================ */
    /* Analysis                                                     */
    /* ============================================================ */
    double ltl_step = best_1 - best_0;
    double ltl_step_2 = (best_2 - best_0) / 2.0;

    printf("=== Analysis ===\n");
    printf("  Baseline (0 props):                %8.1f ns/frame\n", best_0);
    printf("    = Haskell FFI overhead\n");
    printf("    + Agda frame dispatch\n");
    printf("    + Agda response serialization (formatResponse + formatJSON)\n");
    printf("    + Haskell Text->String->CString\n");
    printf("    + C: free_str\n\n");
    printf("  Marginal cost per LTL property:\n");
    printf("    From 0→1 props:                  %8.1f ns\n", ltl_step);
    printf("    From 0→2 props (avg):            %8.1f ns\n", ltl_step_2);
    printf("\n");
    printf("  C malloc+memcpy+free (17 bytes):   %8.1f ns\n", best_alloc);
    printf("  Agda/Haskell compute (best_0 - alloc): %5.1f ns\n",
           best_0 - best_alloc);
    printf("  (= frame dispatch + response serialize + Text→String→CString)\n\n");

    double budget = 1e9 / 48000.0;
    printf("=== Context (48k fps target) ===\n");
    printf("  Per-frame budget:                  %8.0f ns\n", budget);
    printf("  Baseline %% of budget:              %8.1f%%\n",
           best_0 / budget * 100);
    printf("  1-prop %% of budget:                %8.1f%%\n",
           best_1 / budget * 100);
    printf("  2-prop %% of budget:                %8.1f%%\n",
           best_2 / budget * 100);

    dlclose(lib);
    return 0;
}
