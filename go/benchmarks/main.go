// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

// Aletheia Go Benchmark
//
// Measures throughput, latency, and scaling for CAN 2.0B and CAN-FD frames
// through the Aletheia FFI pipeline (Go -> cgo -> Haskell/MAlonzo/Agda).
//
// Usage, from the go/ module directory, the repo root having no go.mod:
//
//	cd go && go run ./benchmarks [throughput|latency|scaling] \
//	    [--frames N] [--runs N] [--ops N] [--warmup N] [--quick] [--json]
package main

import (
	"context"
	"encoding/json"
	"flag"
	"fmt"
	"math"
	"os"
	"path/filepath"
	"runtime"
	"slices"
	"strings"
	"time"

	"github.com/Jaetan/aletheia/go/v5/aletheia"
)

// die reports a condition that makes the report untrue and exits. Every
// measured failure is fatal: a lane left out, or a row computed from fewer
// runs than it claims, is indistinguishable from a healthy one in
// benchmarks/SCHEMA.yaml and reads as "not measured yet" rather than "broken".
func die(format string, args ...any) {
	fmt.Fprintf(os.Stderr, "benchmark: "+format+"\n", args...)
	os.Exit(1)
}

// ctx is the benchmark default context. Benchmarks measure unconditional
// throughput; cancellation is exercised in the test suite, not here.
var ctx = context.Background()

// findLibrary answers the path the kernel is loaded from: what ALETHEIA_LIB
// names, else the build tree as seen from the executable or from the working
// directory. Every candidate is checked; the last is returned unchecked, so a
// benchmark that cannot load names a path rather than nothing.
func findLibrary() string {
	if path := os.Getenv("ALETHEIA_LIB"); path != "" {
		return path
	}
	const soName = "libaletheia-ffi.so"
	// The repo root, go/ and go/benchmarks/: the working directories the usage
	// above and benchmarks/run_all.sh run this from.
	candidates := []string{
		filepath.Join("build", soName),
		filepath.Join("..", "build", soName),
		filepath.Join("..", "..", "build", soName),
	}
	// A built binary sits in go/benchmarks/, two levels under the repo root.
	if exe, err := os.Executable(); err == nil {
		fromExe := filepath.Join(filepath.Dir(exe), "..", "..", "build", soName)
		candidates = append([]string{fromExe}, candidates...)
	}
	for _, candidate := range candidates {
		if _, err := os.Stat(candidate); err == nil {
			return candidate
		}
	}
	return candidates[len(candidates)-1]
}

func mustStdID(v uint16) aletheia.CANID {
	id, err := aletheia.NewStandardID(v)
	if err != nil {
		panic(err)
	}
	return id
}

func mustDLC(v uint8) aletheia.DLC {
	dlc, err := aletheia.NewDLC(v)
	if err != nil {
		panic(err)
	}
	return dlc
}

// rat is a shorthand for creating Rational values in benchmark DBC definitions.
func rat(num, den int64) aletheia.Rational {
	return aletheia.Rational{Numerator: num, Denominator: den}
}

func can20DBC() aletheia.DBCDefinition {
	// The constructors fill the lookup indices. A struct literal leaves them
	// nil, which drops SignalByName, MessageByID and MessageByName onto a
	// linear scan and measures a path no user takes.
	msgs := []aletheia.DBCMessage{
		aletheia.NewDBCMessage(mustStdID(0x100), "EngineStatus", mustDLC(8), "ECU1", nil, []aletheia.DBCSignal{
			{Name: "EngineSpeed", StartBit: 0, BitLength: 16, ByteOrder: aletheia.LittleEndian, IsSigned: false,
				Factor: rat(1, 4), Offset: rat(0, 1), Minimum: rat(0, 1), Maximum: rat(8000, 1), Unit: "rpm", Presence: aletheia.AlwaysPresent{}},
			{Name: "EngineTemp", StartBit: 16, BitLength: 8, ByteOrder: aletheia.LittleEndian, IsSigned: false,
				Factor: rat(1, 1), Offset: rat(-40, 1), Minimum: rat(-40, 1), Maximum: rat(215, 1), Unit: "celsius", Presence: aletheia.AlwaysPresent{}},
		}),
		aletheia.NewDBCMessage(mustStdID(0x200), "BrakeStatus", mustDLC(8), "ECU2", nil, []aletheia.DBCSignal{
			{Name: "BrakePressure", StartBit: 0, BitLength: 16, ByteOrder: aletheia.LittleEndian, IsSigned: false,
				Factor: rat(1, 10), Offset: rat(0, 1), Minimum: rat(0, 1), Maximum: rat(65535, 10), Unit: "bar", Presence: aletheia.AlwaysPresent{}},
			{Name: "BrakePressed", StartBit: 16, BitLength: 1, ByteOrder: aletheia.LittleEndian, IsSigned: false,
				Factor: rat(1, 1), Offset: rat(0, 1), Minimum: rat(0, 1), Maximum: rat(1, 1), Unit: "", Presence: aletheia.AlwaysPresent{}},
		}),
	}
	return *aletheia.NewDBCDefinition("", msgs)
}

func canfdDBC() aletheia.DBCDefinition {
	ap := aletheia.AlwaysPresent{}
	le := aletheia.LittleEndian
	msgs := []aletheia.DBCMessage{
		aletheia.NewDBCMessage(mustStdID(0x200), "SensorFusion", mustDLC(15), "SensorGateway",
			nil,
			[]aletheia.DBCSignal{
				{Name: "GPSLatitude", StartBit: 0, BitLength: 32, ByteOrder: le, IsSigned: true, Factor: rat(1, 10000000), Offset: rat(0, 1), Minimum: rat(-90, 1), Maximum: rat(90, 1), Unit: "deg", Presence: ap},
				{Name: "GPSLongitude", StartBit: 32, BitLength: 32, ByteOrder: le, IsSigned: true, Factor: rat(1, 10000000), Offset: rat(0, 1), Minimum: rat(-180, 1), Maximum: rat(180, 1), Unit: "deg", Presence: ap},
				{Name: "GPSAltitude", StartBit: 64, BitLength: 16, ByteOrder: le, IsSigned: true, Factor: rat(1, 10), Offset: rat(0, 1), Minimum: rat(-1000, 1), Maximum: rat(55535, 10), Unit: "m", Presence: ap},
				{Name: "GPSSpeed", StartBit: 80, BitLength: 16, ByteOrder: le, IsSigned: false, Factor: rat(1, 100), Offset: rat(0, 1), Minimum: rat(0, 1), Maximum: rat(65535, 100), Unit: "m/s", Presence: ap},
				{Name: "YawRate", StartBit: 96, BitLength: 16, ByteOrder: le, IsSigned: true, Factor: rat(1, 100), Offset: rat(0, 1), Minimum: rat(-32768, 100), Maximum: rat(32767, 100), Unit: "deg/s", Presence: ap},
				{Name: "LateralAccel", StartBit: 112, BitLength: 16, ByteOrder: le, IsSigned: true, Factor: rat(1, 100), Offset: rat(0, 1), Minimum: rat(-32768, 100), Maximum: rat(32767, 100), Unit: "m/s2", Presence: ap},
				{Name: "LongAccel", StartBit: 128, BitLength: 16, ByteOrder: le, IsSigned: true, Factor: rat(1, 100), Offset: rat(0, 1), Minimum: rat(-32768, 100), Maximum: rat(32767, 100), Unit: "m/s2", Presence: ap},
				{Name: "SteeringAngle", StartBit: 144, BitLength: 16, ByteOrder: le, IsSigned: true, Factor: rat(1, 10), Offset: rat(0, 1), Minimum: rat(-32768, 10), Maximum: rat(32767, 10), Unit: "deg", Presence: ap},
				{Name: "WheelSpeedFL", StartBit: 160, BitLength: 16, ByteOrder: le, IsSigned: false, Factor: rat(1, 100), Offset: rat(0, 1), Minimum: rat(0, 1), Maximum: rat(65535, 100), Unit: "m/s", Presence: ap},
				{Name: "WheelSpeedFR", StartBit: 176, BitLength: 16, ByteOrder: le, IsSigned: false, Factor: rat(1, 100), Offset: rat(0, 1), Minimum: rat(0, 1), Maximum: rat(65535, 100), Unit: "m/s", Presence: ap},
				{Name: "WheelSpeedRL", StartBit: 192, BitLength: 16, ByteOrder: le, IsSigned: false, Factor: rat(1, 100), Offset: rat(0, 1), Minimum: rat(0, 1), Maximum: rat(65535, 100), Unit: "m/s", Presence: ap},
				{Name: "WheelSpeedRR", StartBit: 208, BitLength: 16, ByteOrder: le, IsSigned: false, Factor: rat(1, 100), Offset: rat(0, 1), Minimum: rat(0, 1), Maximum: rat(65535, 100), Unit: "m/s", Presence: ap},
				{Name: "BrakeTempFL", StartBit: 224, BitLength: 12, ByteOrder: le, IsSigned: false, Factor: rat(1, 10), Offset: rat(0, 1), Minimum: rat(0, 1), Maximum: rat(4095, 10), Unit: "celsius", Presence: ap},
				{Name: "BrakeTempFR", StartBit: 236, BitLength: 12, ByteOrder: le, IsSigned: false, Factor: rat(1, 10), Offset: rat(0, 1), Minimum: rat(0, 1), Maximum: rat(4095, 10), Unit: "celsius", Presence: ap},
				{Name: "BrakeTempRL", StartBit: 248, BitLength: 12, ByteOrder: le, IsSigned: false, Factor: rat(1, 10), Offset: rat(0, 1), Minimum: rat(0, 1), Maximum: rat(4095, 10), Unit: "celsius", Presence: ap},
				{Name: "BrakeTempRR", StartBit: 260, BitLength: 12, ByteOrder: le, IsSigned: false, Factor: rat(1, 10), Offset: rat(0, 1), Minimum: rat(0, 1), Maximum: rat(4095, 10), Unit: "celsius", Presence: ap},
				{Name: "TirePressFL", StartBit: 272, BitLength: 8, ByteOrder: le, IsSigned: false, Factor: rat(1, 100), Offset: rat(0, 1), Minimum: rat(0, 1), Maximum: rat(255, 100), Unit: "bar", Presence: ap},
				{Name: "TirePressFR", StartBit: 280, BitLength: 8, ByteOrder: le, IsSigned: false, Factor: rat(1, 100), Offset: rat(0, 1), Minimum: rat(0, 1), Maximum: rat(255, 100), Unit: "bar", Presence: ap},
				{Name: "TirePressRL", StartBit: 288, BitLength: 8, ByteOrder: le, IsSigned: false, Factor: rat(1, 100), Offset: rat(0, 1), Minimum: rat(0, 1), Maximum: rat(255, 100), Unit: "bar", Presence: ap},
				{Name: "TirePressRR", StartBit: 296, BitLength: 8, ByteOrder: le, IsSigned: false, Factor: rat(1, 100), Offset: rat(0, 1), Minimum: rat(0, 1), Maximum: rat(255, 100), Unit: "bar", Presence: ap},
				{Name: "SensorStatus", StartBit: 304, BitLength: 8, ByteOrder: le, IsSigned: false, Factor: rat(1, 1), Offset: rat(0, 1), Minimum: rat(0, 1), Maximum: rat(255, 1), Unit: "", Presence: ap},
				{Name: "IMUTemp", StartBit: 312, BitLength: 8, ByteOrder: le, IsSigned: true, Factor: rat(1, 1), Offset: rat(-40, 1), Minimum: rat(-40, 1), Maximum: rat(215, 1), Unit: "celsius", Presence: ap},
				{Name: "BatteryVolt", StartBit: 320, BitLength: 12, ByteOrder: le, IsSigned: false, Factor: rat(1, 100), Offset: rat(0, 1), Minimum: rat(0, 1), Maximum: rat(4095, 100), Unit: "V", Presence: ap},
				{Name: "GPSHeading", StartBit: 332, BitLength: 16, ByteOrder: le, IsSigned: false, Factor: rat(1, 100), Offset: rat(0, 1), Minimum: rat(0, 1), Maximum: rat(65535, 100), Unit: "deg", Presence: ap},
				{Name: "TimestampMs", StartBit: 348, BitLength: 32, ByteOrder: le, IsSigned: false, Factor: rat(1, 1), Offset: rat(0, 1), Minimum: rat(0, 1), Maximum: rat(4294967295, 1), Unit: "ms", Presence: ap},
			}),
	}
	return *aletheia.NewDBCDefinition("", msgs)
}

var can20Frame = aletheia.FramePayload([]byte{0x40, 0x1F, 0x82, 0x00, 0x00, 0x00, 0x00, 0x00})

var canfdFrame = func() aletheia.FramePayload {
	base := []byte{
		0x00, 0xE1, 0xF5, 0x05, // GPSLatitude
		0x00, 0x6C, 0xDC, 0x02, // GPSLongitude
		0xE8, 0x03, // GPSAltitude
		0xD0, 0x07, // GPSSpeed
		0x00, 0x00, // YawRate
		0x00, 0x00, // LateralAccel
		0x00, 0x00, // LongAccel
		0x00, 0x00, // SteeringAngle
		0xE8, 0x03, // WheelSpeedFL
		0xE8, 0x03, // WheelSpeedFR
		0xE8, 0x03, // WheelSpeedRL
		0xE8, 0x03, // WheelSpeedRR
	}
	// Pad to 64 bytes.
	for len(base) < 64 {
		base = append(base, 0x00)
	}
	return aletheia.FramePayload(base)
}()

var can20Properties = []aletheia.Formula{
	alwaysBetween("EngineSpeed", 0, 8000),
	alwaysBetween("EngineTemp", -40, 215),
}

var canfdProperties = []aletheia.Formula{
	alwaysBetween("GPSSpeed", 0, 655),
	alwaysBetween("YawRate", -327, 327),
	alwaysBetween("WheelSpeedFL", 0, 655),
}

// CAN 2.0B signal values for frame building.
var can20Signals = []aletheia.SignalValue{
	{Name: "EngineSpeed", Value: aletheia.IntRational(2000)},
	{Name: "EngineTemp", Value: aletheia.IntRational(90)},
}

// CAN-FD signal values for frame building.
var canfdSignals = []aletheia.SignalValue{
	{Name: "GPSSpeed", Value: aletheia.IntRational(20)},
	{Name: "YawRate", Value: aletheia.IntRational(0)},
	{Name: "WheelSpeedFL", Value: aletheia.IntRational(10)},
	{Name: "WheelSpeedFR", Value: aletheia.IntRational(10)},
}

var (
	can20ID  = mustStdID(0x100)
	can20DLC = mustDLC(8)
	canfdID  = mustStdID(0x200)
	canfdDLC = mustDLC(15)
)

// frameFamily is one CAN family the benchmarks measure: the DBC describing it,
// the frame they send, the properties they check and the signals they build.
type frameFamily struct {
	name    string
	dbc     aletheia.DBCDefinition
	id      aletheia.CANID
	dlc     aletheia.DLC
	frame   aletheia.FramePayload
	props   []aletheia.Formula
	signals []aletheia.SignalValue
}

// families are the two, in the order every mode reports them.
func families() []frameFamily {
	return []frameFamily{
		{name: "CAN 2.0B", dbc: can20DBC(), id: can20ID, dlc: can20DLC, frame: can20Frame, props: can20Properties, signals: can20Signals},
		{name: "CAN-FD", dbc: canfdDBC(), id: canfdID, dlc: canfdDLC, frame: canfdFrame, props: canfdProperties, signals: canfdSignals},
	}
}

// lane spells a throughput lane name. The padding is the summary table's column
// alignment, and the spelling is pinned across the four bindings by
// benchmarks/SCHEMA.yaml.
func (f frameFamily) lane(what string) string {
	return fmt.Sprintf("%-10s%s", f.name+":", what)
}

// clientFor opens a client on the family's DBC. streamingClientFor adds the
// properties and starts the stream. A setup failure closes the client, so no
// measurement runs against a half-built one.
func clientFor(backend *aletheia.FFIBackend, f frameFamily) (*aletheia.Client, error) {
	client, err := aletheia.NewClient(backend)
	if err != nil {
		return nil, err
	}
	if _, err := client.ParseDBC(ctx, f.dbc); err != nil {
		client.Close()
		return nil, err
	}
	return client, nil
}

func streamingClientFor(backend *aletheia.FFIBackend, f frameFamily, props []aletheia.Formula) (*aletheia.Client, error) {
	client, err := clientFor(backend, f)
	if err != nil {
		return nil, err
	}
	if err := client.SetProperties(ctx, props); err != nil {
		client.Close()
		return nil, err
	}
	if err := client.StartStream(ctx); err != nil {
		client.Close()
		return nil, err
	}
	return client, nil
}

func mean(xs []float64) float64 {
	if len(xs) == 0 {
		return 0
	}
	var sum float64
	for _, x := range xs {
		sum += x
	}
	return sum / float64(len(xs))
}

func stdev(xs []float64) float64 {
	if len(xs) < 2 {
		return 0
	}
	m := mean(xs)
	var ss float64
	for _, x := range xs {
		d := x - m
		ss += d * d
	}
	return math.Sqrt(ss / float64(len(xs)-1))
}

// round1 and round3 are the rounding the cross-binding schema pins: one
// decimal for a rate or a duration, three for a ratio.
func round1(x float64) float64 { return math.Round(x*10) / 10 }
func round3(x float64) float64 { return math.Round(x*1000) / 1000 }

// usPerFrameOf inverts a rate, relativeOf compares one to a sweep's baseline.
// Neither invents a number from a non-positive one.
func usPerFrameOf(fps float64) float64 {
	if fps <= 0 {
		return 0
	}
	return 1_000_000 / fps
}

func relativeOf(fps, baseline float64) float64 {
	if baseline <= 0 {
		return 0
	}
	return fps / baseline
}

func percentile(sorted []float64, p float64) float64 {
	if len(sorted) == 0 {
		return 0
	}
	k := float64(len(sorted)-1) * p / 100.0
	f := int(k)
	c := f + 1
	if c >= len(sorted) {
		c = f
	}
	return sorted[f] + (k-float64(f))*(sorted[c]-sorted[f])
}

type systemInfo struct {
	CPU      string `json:"cpu"`
	Cores    int    `json:"cores"`
	Platform string `json:"platform"`
	Go       string `json:"go"`
}

func getSystemInfo() systemInfo {
	return systemInfo{
		CPU:      runtime.GOARCH,
		Cores:    runtime.NumCPU(),
		Platform: runtime.GOOS,
		Go:       runtime.Version(),
	}
}

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
		fmt.Fprintf(out, "\n%s:\n", l.name)
		fmt.Fprintf(out, "%s\n", strings.Repeat("-", 40))

		// A warmup failure is reported and not fatal: it produces no number that
		// reaches the report, and one that matters recurs in the measured runs.
		for w := 0; w < warmupRuns; w++ {
			if _, err := l.run(numFrames / 10); err != nil {
				fmt.Fprintf(out, "  Warmup error: %v\n", err)
			}
		}

		// A failed measured run is fatal, as it is for the other three harnesses.
		fpsList := make([]float64, 0, numRuns)
		for r := 0; r < numRuns; r++ {
			fps, err := l.run(numFrames)
			if err != nil {
				die("lane %q run %d/%d failed: %v", l.name, r+1, numRuns, err)
			}
			fpsList = append(fpsList, fps)
			fmt.Fprintf(out, "  Run %d/%d: %.0f ops/sec\n", r+1, numRuns, fps)
		}

		m := mean(fpsList)
		results = append(results, throughputResult{
			Name:       l.name,
			Frames:     numFrames,
			Runs:       numRuns,
			FPSMean:    round1(m),
			FPSStdev:   round1(stdev(fpsList)),
			FPSMin:     round1(slices.Min(fpsList)),
			FPSMax:     round1(slices.Max(fpsList)),
			USPerFrame: round1(usPerFrameOf(m)),
		})
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

// Scaling reports four sweeps under one mapping. The field order below is the
// wire order benchmarks/SCHEMA.yaml pins across the four bindings.
type traceSizeRow struct {
	Frames   int     `json:"frames"`
	FPS      float64 `json:"fps"`
	Relative float64 `json:"relative"`
}

type propCountRow struct {
	Properties int     `json:"properties"`
	FPS        float64 `json:"fps"`
	USPerFrame float64 `json:"us_per_frame"`
	Relative   float64 `json:"relative"`
}

type complexityRow struct {
	Complexity string  `json:"complexity"`
	FPS        float64 `json:"fps"`
	USPerFrame float64 `json:"us_per_frame"`
	Relative   float64 `json:"relative"`
}

type scalingResults struct {
	TraceSizeCAN20     []traceSizeRow  `json:"trace_size_can20"`
	TraceSizeCANFD     []traceSizeRow  `json:"trace_size_canfd"`
	PropertyCount      []propCountRow  `json:"property_count"`
	PropertyComplexity []complexityRow `json:"property_complexity"`
}

// alwaysBetween, alwaysLessThan and alwaysLessThanRat build the Always-wrapped
// atomic predicates the scaling sweeps share. The signals and bounds are the
// ones python/benchmarks/scaling.py sweeps, so the two harnesses measure the
// same properties.
func alwaysBetween(sig string, lo, hi int64) aletheia.Formula {
	return aletheia.Always{Inner: aletheia.Atomic{Predicate: aletheia.Between{Signal: aletheia.SignalName(sig), Min: aletheia.IntRational(lo), Max: aletheia.IntRational(hi)}}}
}

func alwaysLessThan(sig string, v int64) aletheia.Formula {
	return alwaysLessThanRat(sig, v, 1)
}

func alwaysLessThanRat(sig string, num, den int64) aletheia.Formula {
	return aletheia.Always{Inner: aletheia.Atomic{Predicate: aletheia.LessThan{Signal: aletheia.SignalName(sig), Value: rat(num, den)}}}
}

// propertyTemplates are the ten the property-count sweep cycles through.
func propertyTemplates() []aletheia.Formula {
	return []aletheia.Formula{
		alwaysBetween("EngineSpeed", 0, 8000),
		alwaysBetween("EngineTemp", -40, 215),
		alwaysLessThanRat("BrakePressure", 13107, 2),
		alwaysLessThan("EngineSpeed", 7000),
		alwaysLessThan("EngineTemp", 200),
		alwaysLessThan("BrakePressure", 5000),
		alwaysBetween("EngineSpeed", 500, 7500),
		alwaysBetween("EngineTemp", -20, 180),
		alwaysBetween("BrakePressure", 0, 4000),
		alwaysLessThan("EngineSpeed", 6000),
	}
}

func makeProperties(count int) []aletheia.Formula {
	templates := propertyTemplates()
	props := make([]aletheia.Formula, count)
	for i := 0; i < count; i++ {
		props[i] = templates[i%len(templates)]
	}
	return props
}

// meanFPS averages streaming fps over numRuns passes. Averaging is the
// methodology all four bindings share: noise on an un-averaged baseline would
// multiply into every relative value in the sweep.
func meanFPS(backend *aletheia.FFIBackend, f frameFamily, props []aletheia.Formula, numFrames, numRuns int) float64 {
	fpsList := make([]float64, 0, numRuns)
	for r := 0; r < numRuns; r++ {
		fps, err := benchmarkStreaming(backend, f, props, numFrames)
		if err != nil {
			die("scaling point (%d frames) run %d/%d failed: %v", numFrames, r+1, numRuns, err)
		}
		fpsList = append(fpsList, fps)
	}
	return mean(fpsList)
}

func traceSizes(quick bool) []int {
	if quick {
		return []int{1000, 5000, 10000, 50000}
	}
	return []int{1000, 5000, 10000, 50000, 100000}
}

// complexityLevels are the five labelled bundles the complexity sweep measures,
// in the order benchmarks/SCHEMA.yaml spells them.
func complexityLevels() []struct {
	label string
	props []aletheia.Formula
} {
	// Implies is not a primitive: it lowers to Or(Not(antecedent), consequent),
	// which is what makes this bundle a complexity step rather than a rename.
	implication := aletheia.Always{Inner: aletheia.Implies(
		aletheia.Atomic{Predicate: aletheia.LessThan{Signal: "EngineSpeed", Value: aletheia.IntRational(1000)}},
		aletheia.Atomic{Predicate: aletheia.LessThan{Signal: "EngineTemp", Value: aletheia.IntRational(100)}},
	)}
	engineSpeed := alwaysBetween("EngineSpeed", 0, 8000)
	engineTemp := alwaysBetween("EngineTemp", -40, 215)
	brakeHalf := alwaysLessThanRat("BrakePressure", 13107, 2)
	return []struct {
		label string
		props []aletheia.Formula
	}{
		{"Simple predicate", []aletheia.Formula{alwaysLessThan("EngineSpeed", 8000)}},
		{"Range predicate", []aletheia.Formula{engineSpeed}},
		{"Two predicates (AND)", []aletheia.Formula{engineSpeed, engineTemp}},
		{"Three predicates", []aletheia.Formula{engineSpeed, engineTemp, brakeHalf}},
		{"Implication", []aletheia.Formula{implication}},
	}
}

func runScaling(backend *aletheia.FFIBackend, out *os.File, numRuns int, quick bool) scalingResults {
	fams := families()
	can20, canfd := fams[0], fams[1]
	numFrames := 10000
	if quick {
		numFrames = 5000
	}

	fmt.Fprintf(out, "\n%s\nScaling (runs=%d, quick=%v)\n%s\n", strings.Repeat("=", 70), numRuns, quick, strings.Repeat("=", 70))

	// Warmup.
	_ = meanFPS(backend, can20, makeProperties(1), 1000, 1)

	// Every sweep takes its baseline from its own first row.
	sweep := func(points int, at func(int) float64) []float64 {
		values := make([]float64, 0, points)
		for i := 0; i < points; i++ {
			values = append(values, at(i))
		}
		return values
	}

	scanTrace := func(f frameFamily, props []aletheia.Formula) []traceSizeRow {
		sizes := traceSizes(quick)
		values := sweep(len(sizes), func(i int) float64 {
			return meanFPS(backend, f, props, sizes[i], numRuns)
		})
		rows := make([]traceSizeRow, 0, len(sizes))
		for i, m := range values {
			rows = append(rows, traceSizeRow{Frames: sizes[i], FPS: round1(m), Relative: round3(relativeOf(m, values[0]))})
		}
		return rows
	}

	traceCAN20 := scanTrace(can20, []aletheia.Formula{alwaysBetween("EngineSpeed", 0, 8000)})
	traceCANFD := scanTrace(canfd, []aletheia.Formula{alwaysBetween("GPSSpeed", 0, 655)})

	counts := []int{1, 2, 3, 5, 7, 10}
	countValues := sweep(len(counts), func(i int) float64 {
		return meanFPS(backend, can20, makeProperties(counts[i]), numFrames, numRuns)
	})
	propCount := make([]propCountRow, 0, len(counts))
	for i, m := range countValues {
		propCount = append(propCount, propCountRow{
			Properties: counts[i], FPS: round1(m), USPerFrame: round1(usPerFrameOf(m)),
			Relative: round3(relativeOf(m, countValues[0])),
		})
	}

	levels := complexityLevels()
	levelValues := sweep(len(levels), func(i int) float64 {
		return meanFPS(backend, can20, levels[i].props, numFrames, numRuns)
	})
	complexity := make([]complexityRow, 0, len(levels))
	for i, m := range levelValues {
		complexity = append(complexity, complexityRow{
			Complexity: levels[i].label, FPS: round1(m), USPerFrame: round1(usPerFrameOf(m)),
			Relative: round3(relativeOf(m, levelValues[0])),
		})
	}

	fmt.Fprintf(out, "%s\n", strings.Repeat("=", 70))
	return scalingResults{
		TraceSizeCAN20:     traceCAN20,
		TraceSizeCANFD:     traceCANFD,
		PropertyCount:      propCount,
		PropertyComplexity: complexity,
	}
}

type jsonOutput struct {
	Benchmark string     `json:"benchmark"`
	Language  string     `json:"language"`
	Timestamp string     `json:"timestamp"`
	System    systemInfo `json:"system"`
	Results   any        `json:"results"`
}

func emitJSON(benchmark string, results any) {
	out := jsonOutput{
		Benchmark: benchmark,
		Language:  "go",
		Timestamp: time.Now().UTC().Format(time.RFC3339),
		System:    getSystemInfo(),
		Results:   results,
	}
	enc := json.NewEncoder(os.Stdout)
	enc.SetIndent("", "  ")
	if err := enc.Encode(out); err != nil {
		die("writing the %s report failed: %v", benchmark, err)
	}
}

func main() {
	fs := flag.NewFlagSet("bench", flag.ExitOnError)
	frames := fs.Int("frames", 10000, "Frames per run")
	runs := fs.Int("runs", 5, "Number of runs")
	warmup := fs.Int("warmup", 2, "Warmup runs (throughput) / warmup ops (latency)")
	ops := fs.Int("ops", 5000, "Operations to measure (latency)")
	quick := fs.Bool("quick", false, "Fewer iterations (scaling)")
	jsonFlag := fs.Bool("json", false, "Emit JSON to stdout")

	// Parse: first positional arg is the mode.
	args := os.Args[1:]
	mode := "throughput"
	if len(args) > 0 && !strings.HasPrefix(args[0], "-") {
		mode = args[0]
		args = args[1:]
	}
	fs.Parse(args)

	// A count of zero measures nothing, and a row computed from nothing reads as
	// a rate of zero rather than as a failure. Each is checked whichever mode is
	// running, so the refusal does not depend on which flag that mode reads.
	for _, count := range []struct {
		flag  string
		value int
	}{{"--frames", *frames}, {"--runs", *runs}, {"--ops", *ops}} {
		if count.value < 1 {
			die("%s must be at least 1, got %d", count.flag, count.value)
		}
	}
	if *warmup < 0 {
		die("--warmup must not be negative, got %d", *warmup)
	}

	out := os.Stdout
	if *jsonFlag {
		out = os.Stderr
	}

	// Load FFI backend.
	libPath := findLibrary()
	fmt.Fprintf(out, "%s\n", strings.Repeat("=", 70))
	fmt.Fprintf(out, "Aletheia Go Benchmark (%s)\n", mode)
	fmt.Fprintf(out, "%s\n", strings.Repeat("=", 70))
	fmt.Fprintf(out, "Library: %s\n", libPath)

	backend, err := aletheia.NewFFIBackend(libPath)
	if err != nil {
		die("loading %s failed: %v", libPath, err)
	}

	switch mode {
	case "throughput":
		fmt.Fprintf(out, "Frames per run: %d\n", *frames)
		fmt.Fprintf(out, "Runs: %d\n", *runs)
		fmt.Fprintf(out, "Warmup runs: %d\n", *warmup)
		results := runThroughput(backend, out, *frames, *runs, *warmup)
		if *jsonFlag {
			emitJSON("throughput", results)
		}

	case "latency":
		fmt.Fprintf(out, "Operations: %d\n", *ops)
		fmt.Fprintf(out, "Warmup: %d\n", *warmup)
		results := runLatency(backend, out, *ops, *warmup)
		if *jsonFlag {
			emitJSON("latency", results)
		}

	case "scaling":
		fmt.Fprintf(out, "Runs: %d\n", *runs)
		fmt.Fprintf(out, "Quick: %v\n", *quick)
		results := runScaling(backend, out, *runs, *quick)
		if *jsonFlag {
			emitJSON("scaling", results)
		}

	default:
		die("unknown mode %q, expected throughput, latency or scaling", mode)
	}
}
