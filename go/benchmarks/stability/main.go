// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

// Command stability is the Go long-run resource-leakage harness.
//
// Each cycle opens a client, streams frames through the FFI surface and closes
// it. Four measurements are compared, before the cycles and after:
//
//   - rss, a soft threshold, read from runtime/metrics
//   - fd_count, exact, the entries of /proc/self/fd that name a real resource
//   - goroutines, exact, runtime.NumGoroutine after the last Close
//   - stableptr, exact, the handles the binding still holds on the Haskell side
//
// Drift on any of them is a finding, and the exact gates carry no tolerance.
//
// The cycle and frame counts come from ALETHEIA_STABILITY_CYCLES and
// ALETHEIA_STABILITY_FRAMES. The report is JSON on stdout, and
// tools/stability_run.py archives it per commit.
//
// Exit codes are that runner's contract: zero when every gate passed, one when
// a gate failed and the verdict is in the report, and anything else for a
// failure that produced no verdict at all.
package main

import (
	"context"
	"encoding/json"
	"fmt"
	"os"
	"path/filepath"
	"runtime"
	"runtime/metrics"
	"slices"
	"strconv"
	"strings"
	"time"

	"github.com/aletheia-automotive/aletheia-go/aletheia"
)

// The soft cap, measured on a quiet host, changed here where a diff shows it.
const rssDeltaBytesCap int64 = 50 * 1024 * 1024

// die reports a failure that produced no verdict and exits with the code the
// runner reads as an environment failure rather than as drift.
func die(format string, args ...any) {
	fmt.Fprintf(os.Stderr, "stability: "+format+"\n", args...)
	os.Exit(2)
}

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

// fdCount counts the entries of /proc/self/fd that name a real resource, a
// file, a pipe or a socket, which is what a forgotten Close leaks.
//
// An anon_inode target is not one: the Go scheduler and the GHC RTS netpoller
// allocate eventfd, eventpoll, timerfd and signalfd descriptors lazily as the
// workload grows, so counting them would make an exact gate fire on a run where
// every client was closed.
//
// Linux only, /proc/self/fd being where this is readable.
func fdCount() (int64, error) {
	entries, err := os.ReadDir("/proc/self/fd")
	if err != nil {
		return 0, fmt.Errorf("read /proc/self/fd: %w", err)
	}
	var count int64
	for _, e := range entries {
		target, err := os.Readlink("/proc/self/fd/" + e.Name())
		if err != nil {
			// The descriptor went away between the listing and the read, which
			// is what the listing's own descriptor does.
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

// findLibrary answers the path the kernel is loaded from: what ALETHEIA_LIB
// names, else the build tree as seen from the executable or from the working
// directory. Every candidate is checked; the last is returned unchecked, so a
// harness that cannot load names a path rather than nothing.
func findLibrary() string {
	if path := os.Getenv("ALETHEIA_LIB"); path != "" {
		return path
	}
	const soName = "libaletheia-ffi.so"
	// The working directories this is run from: the repo root, go/ where
	// tools/stability_run.py runs it, and its own, three levels under the root.
	candidates := []string{
		filepath.Join("build", soName),
		filepath.Join("..", "build", soName),
		filepath.Join("..", "..", "..", "build", soName),
	}
	// A built binary sits in that last directory.
	if exe, err := os.Executable(); err == nil {
		fromExe := filepath.Join(filepath.Dir(exe), "..", "..", "..", "build", soName)
		candidates = append([]string{fromExe}, candidates...)
	}
	for _, candidate := range candidates {
		if _, err := os.Stat(candidate); err == nil {
			return candidate
		}
	}
	return candidates[len(candidates)-1]
}

// The one message the harness sends, built once. The constructors validate, so
// a failure here is a mistake in this file rather than anything a run produces.
func mustFrame() (aletheia.CANID, aletheia.DLC, aletheia.FramePayload) {
	id, err := aletheia.NewStandardID(0x100)
	if err != nil {
		panic(err)
	}
	dlc, err := aletheia.NewDLC(8)
	if err != nil {
		panic(err)
	}
	return id, dlc, aletheia.FramePayload([]byte{0x40, 0x1F, 0x82, 0x00, 0x00, 0x00, 0x00, 0x00})
}

var frameID, frameDLC, framePayload = mustFrame()

// minimalDBC describes the one message, with one signal, so that the harness
// measures what it accounts for rather than the cost of checking a formula.
func minimalDBC() aletheia.DBCDefinition {
	rat := func(n, d int64) aletheia.Rational {
		return aletheia.Rational{Numerator: n, Denominator: d}
	}
	msg := aletheia.NewDBCMessage(frameID, "EngineStatus", frameDLC, "ECU1", nil, []aletheia.DBCSignal{
		{
			Name: "EngineSpeed", StartBit: 0, BitLength: 16,
			ByteOrder: aletheia.LittleEndian, IsSigned: false,
			Factor: rat(1, 4), Offset: rat(0, 1),
			Minimum: rat(0, 1), Maximum: rat(8000, 1),
			Unit: "rpm", Presence: aletheia.AlwaysPresent{},
		},
	})
	return *aletheia.NewDBCDefinition("", []aletheia.DBCMessage{msg})
}

// runCycle opens a client, streams framesPerCycle frames through it and closes
// it. What the cycle leaves behind is what the gates measure.
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
	for i := 0; i < framesPerCycle; i++ {
		ts := aletheia.Timestamp{Microseconds: int64(i) * 1000}
		if _, err := client.SendFrame(ctx, ts, frameID, frameDLC, framePayload, nil, nil); err != nil {
			return fmt.Errorf("SendFrame %d: %w", i, err)
		}
	}
	if _, err := client.EndStream(ctx); err != nil {
		return fmt.Errorf("EndStream: %w", err)
	}
	return nil
}

// envCount reads a positive whole number from the environment, answering the
// default when the variable is unset. Anything else is refused: a run that
// quietly measured the default would report it as the answer to what was asked.
func envCount(name string, defaultValue int) int {
	raw, ok := os.LookupEnv(name)
	if !ok {
		return defaultValue
	}
	n, err := strconv.Atoi(raw)
	if err != nil || n < 1 {
		die("%s must be a positive whole number, got %q", name, raw)
	}
	return n
}

func main() {
	cycles := envCount("ALETHEIA_STABILITY_CYCLES", 10)
	frames := envCount("ALETHEIA_STABILITY_FRAMES", 100000)
	ctx := context.Background()

	libPath := findLibrary()
	backend, err := aletheia.NewFFIBackend(libPath)
	if err != nil {
		die("loading %s failed: %v", libPath, err)
	}
	dbc := minimalDBC()

	// One cycle before the window opens, so the first initialisation's own
	// memory is inside neither snapshot.
	if err := runCycle(ctx, backend, dbc, 100); err != nil {
		die("the warm-up cycle failed: %v", err)
	}
	runtime.GC()

	start, err := takeSnapshot()
	if err != nil {
		die("the opening snapshot failed: %v", err)
	}
	t0 := time.Now()

	for i := 0; i < cycles; i++ {
		if err := runCycle(ctx, backend, dbc, frames); err != nil {
			die("cycle %d of %d failed: %v", i+1, cycles, err)
		}
		runtime.GC()
	}

	end, err := takeSnapshot()
	if err != nil {
		die("the closing snapshot failed: %v", err)
	}
	elapsed := time.Since(t0).Seconds()

	// An exact gate passes only when the two snapshots agree, so it carries no
	// threshold. The names and gate words are docs/STABILITY_BENCH.yaml's.
	exact := func(name string, from, to int64) subCheck {
		return subCheck{Name: name, Gate: "hard_zero", Start: from, End: to, Delta: to - from, Passed: to == from}
	}
	subChecks := []subCheck{
		{
			Name: "rss", Gate: "soft_threshold",
			Start: start.RSS, End: end.RSS, Delta: end.RSS - start.RSS,
			Threshold: rssDeltaBytesCap,
			Passed:    abs(end.RSS-start.RSS) <= rssDeltaBytesCap,
		},
		exact("fd_count", start.NumFDs, end.NumFDs),
		exact("goroutines", start.Goroutines, end.Goroutines),
		exact("stableptr", start.StablePtrCount, end.StablePtrCount),
	}

	allPassed := !slices.ContainsFunc(subChecks, func(c subCheck) bool { return !c.Passed })

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
		die("writing the report failed: %v", err)
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
