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
	"io"
	"math"
	"os"
	"path/filepath"
	"runtime"
	"strings"
	"time"

	"github.com/Jaetan/aletheia/go/v5/aletheia"
)

// die reports a condition that makes the report untrue and exits. Every
// failed pass, warmup or measured, is fatal: a lane left out, or a row
// computed from fewer runs than it claims, is indistinguishable from a healthy
// one in benchmarks/SCHEMA.yaml and reads as "not measured yet" rather than
// "broken".
func die(format string, args ...any) {
	fmt.Fprintf(os.Stderr, "benchmark: "+format+"\n", args...)
	os.Exit(1)
}

// ctx is the benchmark default context. Benchmarks measure unconditional
// throughput; cancellation is exercised in the test suite, not here.
var ctx = context.Background()

// findLibrary answers the path the kernel is loaded from: what ALETHEIA_LIB
// names, else the build tree as seen from the working directory. Every
// candidate is checked; the last is returned unchecked, so a benchmark that
// cannot load names a path rather than nothing.
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

func mustExtID(v uint32) aletheia.CANID {
	id, err := aletheia.NewExtendedID(v)
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
				{Name: "GPSAltitude", StartBit: 64, BitLength: 16, ByteOrder: le, IsSigned: true, Factor: rat(1, 10), Offset: rat(0, 1), Minimum: rat(-1000, 1), Maximum: rat(32767, 10), Unit: "m", Presence: ap},
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
				{Name: "IMUTemp", StartBit: 312, BitLength: 8, ByteOrder: le, IsSigned: false, Factor: rat(1, 1), Offset: rat(-40, 1), Minimum: rat(-40, 1), Maximum: rat(215, 1), Unit: "celsius", Presence: ap},
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

// round1, round3 and round4 are the rounding the cross-binding schema pins:
// one decimal for a rate or a duration in microseconds, three for a ratio,
// four for a duration in seconds.
func round1(x float64) float64 { return math.Round(x*10) / 10 }
func round3(x float64) float64 { return math.Round(x*1000) / 1000 }
func round4(x float64) float64 { return math.Round(x*10000) / 10000 }

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

// The flags each mode read, --json aside, under the flag's name, so a report
// states the run that produced it (parameters in benchmarks/SCHEMA.yaml).
type throughputParameters struct {
	Frames int `json:"frames"`
	Runs   int `json:"runs"`
	Warmup int `json:"warmup"`
}

type latencyParameters struct {
	Ops    int `json:"ops"`
	Warmup int `json:"warmup"`
}

type scalingParameters struct {
	Runs  int  `json:"runs"`
	Quick bool `json:"quick"`
}

type jsonOutput struct {
	Benchmark  string     `json:"benchmark"`
	Language   string     `json:"language"`
	Timestamp  string     `json:"timestamp"`
	System     systemInfo `json:"system"`
	Parameters any        `json:"parameters"`
	Results    any        `json:"results"`
}

func emitJSON(benchmark string, parameters, results any) {
	out := jsonOutput{
		Benchmark:  benchmark,
		Language:   "go",
		Timestamp:  time.Now().UTC().Format(time.RFC3339),
		System:     getSystemInfo(),
		Parameters: parameters,
		Results:    results,
	}
	if err := writeReport(os.Stdout, out); err != nil {
		die("%v", err)
	}
}

// writeReport encodes one report to w. A write that fails is an error naming
// the report, so the run exits non-zero and says why: benchmarks/run_all.sh
// would otherwise read a clean exit over a report it cannot parse, with no
// line naming the write.
func writeReport(w io.Writer, out jsonOutput) error {
	enc := json.NewEncoder(w)
	enc.SetIndent("", "  ")
	if err := enc.Encode(out); err != nil {
		return reportFailed(out.Benchmark, err)
	}
	return nil
}

// reportFailed names the report a write failed on and wraps the write's error.
func reportFailed(benchmark string, err error) error {
	return fmt.Errorf("writing the %s report failed: %w", benchmark, err)
}

// reportWriter is the text report's writer. It keeps the first error a write
// returns and makes every later write a no-op, so the lanes print as they go
// and main checks the report once they are done.
type reportWriter struct {
	w   io.Writer
	err error
}

func (r *reportWriter) Write(p []byte) (int, error) {
	if r.err != nil {
		return 0, r.err
	}
	n, err := r.w.Write(p)
	r.err = err
	return n, err
}

// check answers the first failed write's error as the benchmark's report
// failing, or nil when every write reached the stream.
func (r *reportWriter) check(benchmark string) error {
	if r.err == nil {
		return nil
	}
	return reportFailed(benchmark, r.err)
}

// checkCounts refuses a count that measures nothing, since a row computed
// from nothing reads as a rate of zero rather than as a failure. Every count
// is checked whichever mode is running, so the refusal does not depend on
// which flag that mode reads.
func checkCounts(frames, runs, ops, warmup int) error {
	for _, count := range []struct {
		flag  string
		value int
	}{{"--frames", frames}, {"--runs", runs}, {"--ops", ops}} {
		if count.value < 1 {
			return fmt.Errorf("%s must be at least 1, got %d", count.flag, count.value)
		}
	}
	if warmup < 0 {
		return fmt.Errorf("--warmup must not be negative, got %d", warmup)
	}
	return nil
}

// checkMode refuses a mode this program does not run, and an argument the
// flags leave over: flag parsing stops at the first argument that is not a
// flag, so a mode written after a flag would run the default mode and drop
// every flag after it.
func checkMode(mode string, leftover []string) error {
	switch mode {
	case "throughput", "latency", "scaling":
	default:
		return fmt.Errorf("unknown mode %q, expected throughput, latency or scaling", mode)
	}
	if len(leftover) > 0 {
		return fmt.Errorf("unexpected argument %q: the mode is the first argument, and only flags follow it", leftover[0])
	}
	return nil
}

// A mode run without --warmup warms as the other bindings' harnesses do: two
// untimed passes before a throughput lane, five hundred untimed operations
// before a latency lane.
const (
	throughputWarmupRuns = 2
	latencyWarmupOps     = 500
)

func main() {
	fs := flag.NewFlagSet("bench", flag.ExitOnError)
	frames := fs.Int("frames", 10000, "Frames per run")
	runs := fs.Int("runs", 5, "Number of runs")
	warmup := fs.Int("warmup", throughputWarmupRuns,
		fmt.Sprintf("Warmup runs (throughput) / warmup ops (latency, default %d)", latencyWarmupOps))
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
	warmupGiven := false
	fs.Visit(func(f *flag.Flag) { warmupGiven = warmupGiven || f.Name == "warmup" })
	if mode == "latency" && !warmupGiven {
		*warmup = latencyWarmupOps
	}

	// Before the kernel loads, so a refused run measures nothing.
	if err := checkMode(mode, fs.Args()); err != nil {
		die("%v", err)
	}
	if err := checkCounts(*frames, *runs, *ops, *warmup); err != nil {
		die("%v", err)
	}

	// Without --json the text is the report, and a failed write fails the
	// run. With --json the report is the JSON on stdout and the text is
	// progress on stderr, whose writes go unchecked as die's own message does.
	report := &reportWriter{w: os.Stdout}
	var out io.Writer = report
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
			emitJSON("throughput", throughputParameters{Frames: *frames, Runs: *runs, Warmup: *warmup}, results)
		}

	case "latency":
		fmt.Fprintf(out, "Operations: %d\n", *ops)
		fmt.Fprintf(out, "Warmup: %d\n", *warmup)
		results := runLatency(backend, out, *ops, *warmup)
		if *jsonFlag {
			emitJSON("latency", latencyParameters{Ops: *ops, Warmup: *warmup}, results)
		}

	case "scaling":
		fmt.Fprintf(out, "Runs: %d\n", *runs)
		fmt.Fprintf(out, "Quick: %v\n", *quick)
		results := runScaling(backend, out, *runs, *quick)
		if *jsonFlag {
			emitJSON("scaling", scalingParameters{Runs: *runs, Quick: *quick}, results)
		}
	}
	if err := report.check(mode); err != nil {
		die("%v", err)
	}
}
