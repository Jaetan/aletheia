// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package main

import (
	"fmt"
	"os"
	"slices"
	"strings"
	"time"

	"github.com/Jaetan/aletheia/go/v5/aletheia"
)

type latencyStats struct {
	Name   string  `json:"name"`
	Count  int     `json:"count"`
	MeanUS float64 `json:"mean_us"`
	MinUS  float64 `json:"min_us"`
	MaxUS  float64 `json:"max_us"`
	P50US  float64 `json:"p50_us"`
	P90US  float64 `json:"p90_us"`
	P99US  float64 `json:"p99_us"`
	P999US float64 `json:"p999_us"`
}

// measureLatencies times one operation numOps times, after warmup passes that
// are not timed. The durations are microseconds.
func measureLatencies(op func() error, numOps, warmup int) ([]float64, error) {
	for i := 0; i < warmup; i++ {
		if err := op(); err != nil {
			return nil, err
		}
	}
	latencies := make([]float64, 0, numOps)
	for i := 0; i < numOps; i++ {
		start := time.Now()
		if err := op(); err != nil {
			return nil, err
		}
		latencies = append(latencies, float64(time.Since(start).Nanoseconds())/1000.0)
	}
	return latencies, nil
}

func measureStreamLatencies(backend *aletheia.FFIBackend, f frameFamily, numOps, warmup int) ([]float64, error) {
	client, err := streamingClientFor(backend, f, f.props)
	if err != nil {
		return nil, err
	}
	defer client.Close()

	// The stream reads timestamps in order, so the warmup frames carry the first
	// ones and the measured frames continue the count.
	sent := 0
	latencies, err := measureLatencies(func() error {
		_, err := client.SendFrame(ctx, aletheia.Timestamp{Microseconds: int64(sent)}, f.id, f.dlc, f.frame, nil, nil)
		sent++
		return err
	}, numOps, warmup)
	if err != nil {
		return nil, err
	}

	if _, err := client.EndStream(ctx); err != nil {
		return nil, err
	}
	return latencies, nil
}

func measureExtractionLatencies(backend *aletheia.FFIBackend, f frameFamily, numOps, warmup int) ([]float64, error) {
	client, err := clientFor(backend, f)
	if err != nil {
		return nil, err
	}
	defer client.Close()

	return measureLatencies(func() error {
		_, err := client.ExtractSignals(ctx, f.id, f.dlc, f.frame)
		return err
	}, numOps, warmup)
}

func measureBuildLatencies(backend *aletheia.FFIBackend, f frameFamily, numOps, warmup int) ([]float64, error) {
	client, err := clientFor(backend, f)
	if err != nil {
		return nil, err
	}
	defer client.Close()

	return measureLatencies(func() error {
		_, err := client.BuildFrame(ctx, f.id, f.dlc, f.signals)
		return err
	}, numOps, warmup)
}

func analyzeLatencies(name string, raw []float64) latencyStats {
	sorted := slices.Sorted(slices.Values(raw))
	return latencyStats{
		Name:   name,
		Count:  len(raw),
		MeanUS: round1(mean(raw)),
		MinUS:  round1(slices.Min(raw)),
		MaxUS:  round1(slices.Max(raw)),
		P50US:  round1(percentile(sorted, 50)),
		P90US:  round1(percentile(sorted, 90)),
		P99US:  round1(percentile(sorted, 99)),
		P999US: round1(percentile(sorted, 99.9)),
	}
}

func printLatencyStats(out *os.File, s latencyStats) {
	fmt.Fprintf(out, "\n%s:\n", s.Name)
	fmt.Fprintf(out, "%s\n", strings.Repeat("-", 50))
	fmt.Fprintf(out, "  Count:    %d operations\n", s.Count)
	fmt.Fprintf(out, "  Mean:     %.1f us\n", s.MeanUS)
	fmt.Fprintf(out, "  Min:      %.1f us\n", s.MinUS)
	fmt.Fprintf(out, "  Max:      %.1f us\n", s.MaxUS)
	fmt.Fprintf(out, "  p50:      %.1f us\n", s.P50US)
	fmt.Fprintf(out, "  p90:      %.1f us\n", s.P90US)
	fmt.Fprintf(out, "  p99:      %.1f us\n", s.P99US)
	fmt.Fprintf(out, "  p99.9:    %.1f us\n", s.P999US)
	if s.MeanUS > 0 {
		fmt.Fprintf(out, "  Implied:  %.0f ops/sec (from mean)\n", 1_000_000/s.MeanUS)
	}
}

// latencyLane turns one measured lane into its stats row and prints it.
func latencyLane(out *os.File, name string, lat []float64, err error) latencyStats {
	if err != nil {
		die("latency lane %q failed: %v", name, err)
	}
	s := analyzeLatencies(name, lat)
	printLatencyStats(out, s)
	return s
}

func runLatencySuite(backend *aletheia.FFIBackend, out *os.File, f frameFamily, numOps, warmup int) []latencyStats {
	// The lane names are a different spelling from the throughput ones, and
	// benchmarks/SCHEMA.yaml pins both across the four bindings.
	lanes := []struct {
		what    string
		doing   string
		measure func() ([]float64, error)
	}{
		{"Streaming LTL", "streaming", func() ([]float64, error) {
			return measureStreamLatencies(backend, f, numOps, warmup)
		}},
		{"Signal Extraction", "signal extraction", func() ([]float64, error) {
			return measureExtractionLatencies(backend, f, numOps, warmup)
		}},
		{"Frame Building", "frame building", func() ([]float64, error) {
			return measureBuildLatencies(backend, f, numOps, warmup)
		}},
	}

	stats := make([]latencyStats, 0, len(lanes))
	for _, lane := range lanes {
		fmt.Fprintf(out, "\nBenchmarking %s %s...\n", f.name, lane.doing)
		lat, err := lane.measure()
		stats = append(stats, latencyLane(out, f.name+" "+lane.what, lat, err))
	}
	return stats
}

func runLatency(backend *aletheia.FFIBackend, out *os.File, numOps, warmup int) []latencyStats {
	var stats []latencyStats
	for _, f := range families() {
		stats = append(stats, runLatencySuite(backend, out, f, numOps, warmup)...)
	}

	fmt.Fprintf(out, "\n%s\n", strings.Repeat("=", 70))
	fmt.Fprintf(out, "Summary (all times in microseconds)\n")
	fmt.Fprintf(out, "%s\n", strings.Repeat("=", 70))
	fmt.Fprintf(out, "%-30s %10s %10s %10s %10s\n", "Operation", "Mean", "p50", "p99", "p99.9")
	fmt.Fprintf(out, "%s\n", strings.Repeat("-", 70))
	for _, s := range stats {
		fmt.Fprintf(out, "%-30s %10.1f %10.1f %10.1f %10.1f\n", s.Name, s.MeanUS, s.P50US, s.P99US, s.P999US)
	}
	fmt.Fprintf(out, "%s\n", strings.Repeat("=", 70))

	return stats
}
