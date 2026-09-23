// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package main

import (
	"bytes"
	"errors"
	"slices"
	"strings"
	"testing"
)

// These tests drive the throughput lane with an operation of their own, so
// they need no kernel: a failing lane cannot be made from outside a real one.

var errRefused = errors.New("kernel refused the frame")

func TestThroughputLaneAbortsOnAFailedWarmup(t *testing.T) {
	var calls []int
	run := func(n int) (float64, error) {
		calls = append(calls, n)
		return 0, errRefused
	}
	var out bytes.Buffer
	_, err := throughputLane(&out, "Stream LTL", run, 100, 3, 2)
	if err == nil {
		t.Fatal("a failed warmup returned no error")
	}
	for _, want := range []string{`lane "Stream LTL"`, "warmup 1/2", errRefused.Error()} {
		if !strings.Contains(err.Error(), want) {
			t.Errorf("error %q does not name %q", err, want)
		}
	}
	if !errors.Is(err, errRefused) {
		t.Errorf("error %q does not wrap the operation's", err)
	}
	if !slices.Equal(calls, []int{10}) {
		t.Errorf("calls after the failed warmup: %v, want the one warmup pass over a tenth of the frames", calls)
	}
	if strings.Contains(out.String(), "Run 1/") {
		t.Errorf("a measured run was printed after the failed warmup:\n%s", out.String())
	}
}

func TestThroughputLaneNamesTheFailedRun(t *testing.T) {
	var calls []int
	run := func(n int) (float64, error) {
		calls = append(calls, n)
		if len(calls) == 4 {
			return 0, errRefused
		}
		return 1000, nil
	}
	var out bytes.Buffer
	_, err := throughputLane(&out, "Frame Building", run, 100, 3, 2)
	if err == nil {
		t.Fatal("a failed measured run returned no error")
	}
	for _, want := range []string{`lane "Frame Building"`, "run 2/3", errRefused.Error()} {
		if !strings.Contains(err.Error(), want) {
			t.Errorf("error %q does not name %q", err, want)
		}
	}
	if !slices.Equal(calls, []int{10, 10, 100, 100}) {
		t.Errorf("calls: %v, want two warmup passes and the two runs up to the failure", calls)
	}
}

func TestThroughputLaneMeasuresEveryRun(t *testing.T) {
	var calls []int
	run := func(n int) (float64, error) {
		calls = append(calls, n)
		return float64(1000 + len(calls)), nil
	}
	var out bytes.Buffer
	r, err := throughputLane(&out, "Signal Extraction", run, 100, 3, 2)
	if err != nil {
		t.Fatalf("a healthy lane failed: %v", err)
	}
	if !slices.Equal(calls, []int{10, 10, 100, 100, 100}) {
		t.Errorf("calls: %v, want two warmup passes then three runs", calls)
	}
	if r.Name != "Signal Extraction" || r.Frames != 100 || r.Runs != 3 {
		t.Errorf("result names the lane wrong: %+v", r)
	}
	if r.FPSMin != 1003 || r.FPSMax != 1005 || r.FPSMean != 1004 {
		t.Errorf("result statistics are not the runs' (1003, 1004, 1005): %+v", r)
	}
	for _, want := range []string{"Signal Extraction:", "Run 1/3: 1003 ops/sec", "Run 3/3: 1005 ops/sec"} {
		if !strings.Contains(out.String(), want) {
			t.Errorf("output lacks %q:\n%s", want, out.String())
		}
	}
}
