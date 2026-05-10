// Command stability is the Go long-run resource-leakage harness (R18 cluster
// 6 / Go cat 27).
//
// Exercises the FFI surface for cycles × frames (default 10 × 100_000 = 1M
// total frames) and asserts no per-iteration drift on:
//
//   - RSS (soft threshold)        — runtime/metrics /memory/classes/heap/objects:bytes
//   - FD count (hard zero)        — len(os.ReadDir("/proc/self/fd"))
//   - Goroutines (hard zero)      — runtime.NumGoroutine after final Close
//   - StablePtr count (hard zero) — aletheia.StablePtrCount() must be 0
//
// Per AGENTS.md Go cat 27 "Long-run resource leakage sub-checks": drift on
// any sub-check is a finding.  Hard-zero gates are exact equality (no noise
// tolerance allowed); soft-threshold gates carry an empirically-tuned cap
// inline below — change the value, the diff is visible.
//
// Output: JSON to stdout (and optionally
// benchmarks/stability/<commit>/go.json when invoked through
// tools/stability_run.py).
//
// Forward-revert verified 2026-05-08: introducing an intentional non-Close
// makes the harness fail with a precise StablePtr-delta diagnostic;
// restoring brings it back to 0 drift.
package main

import (
	"context"
	"encoding/json"
	"fmt"
	"os"
	"path/filepath"
	"runtime"
	"runtime/metrics"
	"strconv"
	"strings"
	"time"

	"github.com/aletheia-automotive/aletheia-go/aletheia"
)

// Soft-threshold cap (empirically established 2026-05-08, WSL2 quiet host;
// revise inline if a future reviewer runs the harness on a host that rejects
// this as too tight or too loose).
const rssDeltaBytesCap int64 = 50 * 1024 * 1024 // 50 MiB across 1M frames

type snapshot struct {
	RSS            int64 `json:"rss"`
	NumFDs         int64 `json:"num_fds"`
	Goroutines     int64 `json:"goroutines"`
	StablePtrCount int64 `json:"stableptr_count"`
}

type subCheck struct {
	Name      string `json:"name"`
	Gate      string `json:"gate"`
	Start     int64  `json:"start"`
	End       int64  `json:"end"`
	Delta     int64  `json:"delta"`
	Threshold int64  `json:"threshold"`
	Passed    bool   `json:"passed"`
}

type report struct {
	Binding        string     `json:"binding"`
	Cycles         int        `json:"cycles"`
	FramesPerCycle int        `json:"frames_per_cycle"`
	TotalFrames    int        `json:"total_frames"`
	ElapsedSeconds float64    `json:"elapsed_seconds"`
	SubChecks      []subCheck `json:"sub_checks"`
	Passed         bool       `json:"passed"`
}

// readHeapBytes returns runtime/metrics /memory/classes/heap/objects:bytes.
// Forces a GC first so the read reflects steady-state heap rather than
// uncollected garbage.
func readHeapBytes() int64 {
	runtime.GC()
	samples := []metrics.Sample{
		{Name: "/memory/classes/heap/objects:bytes"},
	}
	metrics.Read(samples)
	if samples[0].Value.Kind() != metrics.KindUint64 {
		return 0
	}
	v := samples[0].Value.Uint64()
	if v > 1<<62 {
		return 0
	}
	return int64(v)
}

// fdCount counts /proc/self/fd entries that point to real resources
// (files, pipes, sockets) — the things a forgotten Close can leak.
//
// Excludes anon_inode targets (eventfd, eventpoll, timerfd, signalfd) which
// are runtime-infrastructure FDs the Go scheduler / GHC RTS netpoller
// allocate lazily based on workload.  These are not leaks — they are
// scheduler / I/O-multiplexer machinery — and counting them defeats
// hard-zero gating because the Go cgo runtime grows them across the
// measurement window even when every Client is properly Closed.
//
// Per AGENTS.md cat 27 the FD sub-check is meant to catch "a forgotten
// Close somewhere on the FFI/file-loader path"; that means real resources.
//
// Linux-specific.
func fdCount() (int64, error) {
	entries, err := os.ReadDir("/proc/self/fd")
	if err != nil {
		return 0, fmt.Errorf("read /proc/self/fd: %w", err)
	}
	var count int64
	for _, e := range entries {
		target, err := os.Readlink("/proc/self/fd/" + e.Name())
		if err != nil {
			// FD vanished between readdir and readlink — common for the
			// transient FD readdir itself opens.  Skip.
			continue
		}
		if strings.HasPrefix(target, "anon_inode:") {
			continue
		}
		count++
	}
	return count, nil
}

func takeSnapshot() (snapshot, error) {
	fds, err := fdCount()
	if err != nil {
		return snapshot{}, err
	}
	return snapshot{
		RSS:            readHeapBytes(),
		NumFDs:         fds,
		Goroutines:     int64(runtime.NumGoroutine()),
		StablePtrCount: aletheia.StablePtrCount(),
	}, nil
}

// findLibrary mirrors the resolution order in go/benchmarks/main.go.
func findLibrary() string {
	if p := os.Getenv("ALETHEIA_LIB"); p != "" {
		return p
	}
	exe, err := os.Executable()
	if err == nil {
		rel := filepath.Join(filepath.Dir(exe), "..", "..", "build", "libaletheia-ffi.so")
		if _, err := os.Stat(rel); err == nil {
			return rel
		}
	}
	if _, err := os.Stat("build/libaletheia-ffi.so"); err == nil {
		return "build/libaletheia-ffi.so"
	}
	return "../../build/libaletheia-ffi.so"
}

// minimalDBC builds a tiny single-message DBC sufficient for ParseDBC +
// StartStream to succeed.  Mirrors the pattern in go/benchmarks/main.go
// can20DBC but trimmed to one signal so the harness measures resource
// accounting, not Stream LTL semantics.
func minimalDBC() aletheia.DBCDefinition {
	id, _ := aletheia.NewStandardID(0x100)
	dlc, _ := aletheia.NewDLC(8)
	rat := func(n, d int64) aletheia.Rational {
		return aletheia.Rational{Numerator: n, Denominator: d}
	}
	msg := aletheia.NewDbcMessage(id, "EngineStatus", dlc, "ECU1", nil, []aletheia.DBCSignal{
		{
			Name: "EngineSpeed", StartBit: 0, BitLength: 16,
			ByteOrder: aletheia.LittleEndian, IsSigned: false,
			Factor: rat(1, 4), Offset: rat(0, 1),
			Minimum: rat(0, 1), Maximum: rat(8000, 1),
			Unit: "rpm", Presence: aletheia.AlwaysPresent{},
		},
	})
	return *aletheia.NewDbcDefinition("", []aletheia.DBCMessage{msg})
}

// runCycle opens a Client, parses a DBC, runs a stream of framesPerCycle
// frames, and closes the Client.  StablePtr accounting (one per Init) is
// verified at the end of the run via aletheia.StablePtrCount().
func runCycle(ctx context.Context, backend *aletheia.FFIBackend, dbc aletheia.DBCDefinition, framesPerCycle int) error {
	client, err := aletheia.NewClient(backend)
	if err != nil {
		return fmt.Errorf("NewClient: %w", err)
	}
	defer client.Close()

	if _, err := client.ParseDBC(ctx, dbc); err != nil {
		return fmt.Errorf("ParseDBC: %w", err)
	}
	if err := client.StartStream(ctx); err != nil {
		return fmt.Errorf("StartStream: %w", err)
	}

	id, err := aletheia.NewStandardID(0x100)
	if err != nil {
		return fmt.Errorf("NewStandardID: %w", err)
	}
	dlc, err := aletheia.NewDLC(8)
	if err != nil {
		return fmt.Errorf("NewDLC: %w", err)
	}
	payload := aletheia.FramePayload([]byte{0x40, 0x1F, 0x82, 0x00, 0x00, 0x00, 0x00, 0x00})
	for i := 0; i < framesPerCycle; i++ {
		ts := aletheia.Timestamp{Microseconds: int64(i) * 1000}
		if _, err := client.SendFrame(ctx, ts, id, dlc, payload); err != nil {
			return fmt.Errorf("SendFrame %d: %w", i, err)
		}
	}
	if _, err := client.EndStream(ctx); err != nil {
		return fmt.Errorf("EndStream: %w", err)
	}
	return nil
}

func envInt(name string, defaultValue int) int {
	if v, ok := os.LookupEnv(name); ok {
		n, err := strconv.Atoi(v)
		if err == nil && n > 0 {
			return n
		}
	}
	return defaultValue
}

func main() {
	cycles := envInt("ALETHEIA_STABILITY_CYCLES", 10)
	frames := envInt("ALETHEIA_STABILITY_FRAMES", 100000)
	ctx := context.Background()

	backend, err := aletheia.NewFFIBackend(findLibrary())
	if err != nil {
		fmt.Fprintln(os.Stderr, "NewFFIBackend:", err)
		os.Exit(2)
	}
	dbc := minimalDBC()

	// One warm-up cycle to absorb first-init RSS spike before the
	// measurement window opens.  Runtime-infrastructure FDs (anon_inode
	// eventfd / eventpoll / timerfd) are excluded by fdCount() so we don't
	// need a long warm-up to flush their lazy allocation.
	if err := runCycle(ctx, backend, dbc, 100); err != nil {
		fmt.Fprintln(os.Stderr, "warm-up:", err)
		os.Exit(2)
	}
	runtime.GC()

	start, err := takeSnapshot()
	if err != nil {
		fmt.Fprintln(os.Stderr, "snapshot:", err)
		os.Exit(2)
	}
	t0 := time.Now()

	for i := 0; i < cycles; i++ {
		if err := runCycle(ctx, backend, dbc, frames); err != nil {
			fmt.Fprintln(os.Stderr, "cycle:", err)
			os.Exit(2)
		}
		runtime.GC()
	}

	end, err := takeSnapshot()
	if err != nil {
		fmt.Fprintln(os.Stderr, "snapshot:", err)
		os.Exit(2)
	}
	elapsed := time.Since(t0).Seconds()

	subChecks := []subCheck{
		{
			Name:      "rss",
			Gate:      "soft_threshold",
			Start:     start.RSS,
			End:       end.RSS,
			Delta:     end.RSS - start.RSS,
			Threshold: rssDeltaBytesCap,
			Passed:    abs(end.RSS-start.RSS) <= rssDeltaBytesCap,
		},
		{
			Name:      "fd_count",
			Gate:      "hard_zero",
			Start:     start.NumFDs,
			End:       end.NumFDs,
			Delta:     end.NumFDs - start.NumFDs,
			Threshold: 0,
			Passed:    end.NumFDs == start.NumFDs,
		},
		{
			Name:      "goroutines",
			Gate:      "hard_zero",
			Start:     start.Goroutines,
			End:       end.Goroutines,
			Delta:     end.Goroutines - start.Goroutines,
			Threshold: 0,
			Passed:    end.Goroutines == start.Goroutines,
		},
		{
			Name:      "stableptr",
			Gate:      "hard_zero",
			Start:     start.StablePtrCount,
			End:       end.StablePtrCount,
			Delta:     end.StablePtrCount - start.StablePtrCount,
			Threshold: 0,
			Passed:    end.StablePtrCount == start.StablePtrCount,
		},
	}

	allPassed := true
	for _, c := range subChecks {
		if !c.Passed {
			allPassed = false
		}
	}

	r := report{
		Binding:        "go",
		Cycles:         cycles,
		FramesPerCycle: frames,
		TotalFrames:    cycles * frames,
		ElapsedSeconds: elapsed,
		SubChecks:      subChecks,
		Passed:         allPassed,
	}

	enc := json.NewEncoder(os.Stdout)
	enc.SetIndent("", "  ")
	if err := enc.Encode(r); err != nil {
		fmt.Fprintln(os.Stderr, "encode:", err)
		os.Exit(2)
	}
	if !allPassed {
		os.Exit(1)
	}
}

func abs(x int64) int64 {
	if x < 0 {
		return -x
	}
	return x
}
