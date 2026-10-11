// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package main

import (
	"fmt"
	"io"
	"os"
	"slices"
	"strings"
	"time"

	"github.com/Jaetan/aletheia/go/v5/aletheia"
)

func benchmarkStreaming(backend *aletheia.FFIBackend, f frameFamily, props []aletheia.Formula, numFrames int) (float64, error) {
	client, err := streamingClientFor(backend, f, props)
	if err != nil {
		return 0, err
	}
	defer client.Close()

	start := time.Now()
	for i := 0; i < numFrames; i++ {
		if _, err := client.SendFrame(ctx, aletheia.Timestamp{Microseconds: int64(i)}, f.id, f.dlc, f.frame, nil, nil); err != nil {
			return 0, err
		}
	}
	elapsed := time.Since(start)

	if _, err := client.EndStream(ctx); err != nil {
		return 0, err
	}
	return float64(numFrames) / elapsed.Seconds(), nil
}

func benchmarkExtraction(backend *aletheia.FFIBackend, f frameFamily, numFrames int) (float64, error) {
	client, err := clientFor(backend, f)
	if err != nil {
		return 0, err
	}
	defer client.Close()

	start := time.Now()
	for i := 0; i < numFrames; i++ {
		if _, err := client.ExtractSignals(ctx, f.id, f.dlc, f.frame); err != nil {
			return 0, err
		}
	}
	elapsed := time.Since(start)
	return float64(numFrames) / elapsed.Seconds(), nil
}

func benchmarkBuilding(backend *aletheia.FFIBackend, f frameFamily, numFrames int) (float64, error) {
	client, err := clientFor(backend, f)
	if err != nil {
		return 0, err
	}
	defer client.Close()

	start := time.Now()
	for i := 0; i < numFrames; i++ {
		if _, err := client.BuildFrame(ctx, f.id, f.dlc, f.signals); err != nil {
			return 0, err
		}
	}
	elapsed := time.Since(start)
	return float64(numFrames) / elapsed.Seconds(), nil
}

type throughputResult struct {
	Name       string  `json:"name"`
	Frames     int     `json:"frames"`
	Runs       int     `json:"runs"`
	FPSMean    float64 `json:"fps_mean"`
	FPSStdev   float64 `json:"fps_stdev"`
	FPSMin     float64 `json:"fps_min"`
	FPSMax     float64 `json:"fps_max"`
	USPerFrame float64 `json:"us_per_frame"`
}

func runThroughput(backend *aletheia.FFIBackend, out *os.File, numFrames, numRuns, warmupRuns int) []throughputResult {
	type lane struct {
		name string
		run  func(int) (float64, error)
	}
	var lanes []lane
	for _, f := range families() {
		lanes = append(lanes,
			lane{f.lane(fmt.Sprintf("Stream LTL (%d props)", len(f.props))), func(n int) (float64, error) {
				return benchmarkStreaming(backend, f, f.props, n)
			}},
			lane{f.lane("Signal Extraction"), func(n int) (float64, error) {
				return benchmarkExtraction(backend, f, n)
			}},
			lane{f.lane("Frame Building"), func(n int) (float64, error) {
				return benchmarkBuilding(backend, f, n)
			}},
		)
	}

	var results []throughputResult
	for _, l := range lanes {
		r, err := throughputLane(out, l.name, l.run, numFrames, numRuns, warmupRuns)
		if err != nil {
			die("%v", err)
		}
		results = append(results, r)
	}

	fmt.Fprintf(out, "\n%s\n", strings.Repeat("=", 70))
	fmt.Fprintf(out, "Summary\n")
	fmt.Fprintf(out, "%s\n", strings.Repeat("=", 70))
	fmt.Fprintf(out, "%-35s %12s %10s %10s %10s\n", "Benchmark", "Mean", "Stdev", "Min", "Max")
	fmt.Fprintf(out, "%s\n", strings.Repeat("-", 80))
	for _, r := range results {
		fmt.Fprintf(out, "%-35s %10.0f/s %9.0f %9.0f %9.0f\n", r.Name, r.FPSMean, r.FPSStdev, r.FPSMin, r.FPSMax)
	}
	fmt.Fprintf(out, "%s\n", strings.Repeat("=", 70))

	return results
}

// throughputLane warms a lane up over a tenth of the frames, untimed, then
// measures it numRuns times. A pass that fails, warmup or measured, is the
// lane's error, named by the pass: a lane whose warmup failed ran against a
// client it could not drive, and nothing it measures afterwards is a number.
func throughputLane(out io.Writer, name string, run func(int) (float64, error), numFrames, numRuns, warmupRuns int) (throughputResult, error) {
	fmt.Fprintf(out, "\n%s:\n", name)
	fmt.Fprintf(out, "%s\n", strings.Repeat("-", 40))

	for w := 0; w < warmupRuns; w++ {
		if _, err := run(numFrames / 10); err != nil {
			return throughputResult{}, fmt.Errorf("lane %q warmup %d/%d failed: %w", name, w+1, warmupRuns, err)
		}
	}

	fpsList := make([]float64, 0, numRuns)
	for r := 0; r < numRuns; r++ {
		fps, err := run(numFrames)
		if err != nil {
			return throughputResult{}, fmt.Errorf("lane %q run %d/%d failed: %w", name, r+1, numRuns, err)
		}
		fpsList = append(fpsList, fps)
		fmt.Fprintf(out, "  Run %d/%d: %.0f ops/sec\n", r+1, numRuns, fps)
	}

	m := mean(fpsList)
	return throughputResult{
		Name:       name,
		Frames:     numFrames,
		Runs:       numRuns,
		FPSMean:    round1(m),
		FPSStdev:   round1(stdev(fpsList)),
		FPSMin:     round1(slices.Min(fpsList)),
		FPSMax:     round1(slices.Max(fpsList)),
		USPerFrame: round1(usPerFrameOf(m)),
	}, nil
}
