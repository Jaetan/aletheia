// Aletheia Go Benchmark
//
// Measures throughput, latency, and scaling for CAN 2.0B and CAN-FD frames
// through the Aletheia FFI pipeline (Go -> cgo -> Haskell/MAlonzo/Agda).
//
// Usage:
//
//	go run go/benchmarks/main.go [throughput|latency|scaling] [--frames N] [--runs N] [--json]
package main

import (
	"encoding/json"
	"flag"
	"fmt"
	"math"
	"os"
	"path/filepath"
	"runtime"
	"sort"
	"strings"
	"time"

	"github.com/aletheia-automotive/aletheia-go/aletheia"
)

// ---------------------------------------------------------------------------
// Library discovery
// ---------------------------------------------------------------------------

func findLibrary() string {
	if p := os.Getenv("ALETHEIA_LIB"); p != "" {
		return p
	}
	// Relative to the go/ directory (two levels up from go/benchmarks/).
	exe, err := os.Executable()
	if err == nil {
		rel := filepath.Join(filepath.Dir(exe), "..", "..", "build", "libaletheia-ffi.so")
		if _, err := os.Stat(rel); err == nil {
			return rel
		}
	}
	// Relative to the go/ directory when run with `go run` from the repo root.
	if _, err := os.Stat("build/libaletheia-ffi.so"); err == nil {
		return "build/libaletheia-ffi.so"
	}
	return "../../build/libaletheia-ffi.so"
}

// ---------------------------------------------------------------------------
// DBC definitions (programmatic, matching examples/*.dbc)
// ---------------------------------------------------------------------------

func mustStdID(v uint16) aletheia.CanID {
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

func can20DBC() aletheia.DbcDefinition {
	// Use NewDbcMessage / NewDbcDefinition so the generated indices exercise
	// the map-backed lookup path real users get. Directly populating the
	// structs leaves the signalIndex / nameIndex / idIndex fields nil and
	// drops SignalByName, MessageByID, and MessageByName onto their linear-
	// scan fallback — a benchmark-correctness defect.
	msgs := []aletheia.DbcMessage{
		aletheia.NewDbcMessage(mustStdID(0x100), "EngineStatus", mustDLC(8), "ECU1", nil, []aletheia.DbcSignal{
			{Name: "EngineSpeed", StartBit: 0, BitLength: 16, ByteOrder: aletheia.LittleEndian, IsSigned: false,
				Factor: rat(1, 4), Offset: rat(0, 1), Minimum: rat(0, 1), Maximum: rat(8000, 1), Unit: "rpm", Presence: aletheia.AlwaysPresent{}},
			{Name: "EngineTemp", StartBit: 16, BitLength: 8, ByteOrder: aletheia.LittleEndian, IsSigned: false,
				Factor: rat(1, 1), Offset: rat(-40, 1), Minimum: rat(-40, 1), Maximum: rat(215, 1), Unit: "celsius", Presence: aletheia.AlwaysPresent{}},
		}),
		aletheia.NewDbcMessage(mustStdID(0x200), "BrakeStatus", mustDLC(8), "ECU2", nil, []aletheia.DbcSignal{
			{Name: "BrakePressure", StartBit: 0, BitLength: 16, ByteOrder: aletheia.LittleEndian, IsSigned: false,
				Factor: rat(1, 10), Offset: rat(0, 1), Minimum: rat(0, 1), Maximum: rat(65535, 10), Unit: "bar", Presence: aletheia.AlwaysPresent{}},
			{Name: "BrakePressed", StartBit: 16, BitLength: 1, ByteOrder: aletheia.LittleEndian, IsSigned: false,
				Factor: rat(1, 1), Offset: rat(0, 1), Minimum: rat(0, 1), Maximum: rat(1, 1), Unit: "", Presence: aletheia.AlwaysPresent{}},
		}),
	}
	return *aletheia.NewDbcDefinition("", msgs)
}

func canfdDBC() aletheia.DbcDefinition {
	ap := aletheia.AlwaysPresent{}
	le := aletheia.LittleEndian
	// See comment on can20DBC — constructors populate the map-backed indices
	// so the benchmark measures the lookup path real users exercise.
	msgs := []aletheia.DbcMessage{
		aletheia.NewDbcMessage(mustStdID(0x200), "SensorFusion", mustDLC(15), "SensorGateway",
			nil,
			[]aletheia.DbcSignal{
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
	return *aletheia.NewDbcDefinition("", msgs)
}

// ---------------------------------------------------------------------------
// Frame payloads
// ---------------------------------------------------------------------------

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

// ---------------------------------------------------------------------------
// LTL properties
// ---------------------------------------------------------------------------

var can20Properties = []aletheia.Formula{
	aletheia.Always{Inner: aletheia.Atomic{Predicate: aletheia.Between{Signal: "EngineSpeed", Min: 0, Max: 8000}}},
	aletheia.Always{Inner: aletheia.Atomic{Predicate: aletheia.Between{Signal: "EngineTemp", Min: -40, Max: 215}}},
}

var canfdProperties = []aletheia.Formula{
	aletheia.Always{Inner: aletheia.Atomic{Predicate: aletheia.Between{Signal: "GPSSpeed", Min: 0, Max: 655}}},
	aletheia.Always{Inner: aletheia.Atomic{Predicate: aletheia.Between{Signal: "YawRate", Min: -327, Max: 327}}},
	aletheia.Always{Inner: aletheia.Atomic{Predicate: aletheia.Between{Signal: "WheelSpeedFL", Min: 0, Max: 655}}},
}

// CAN 2.0B signal values for frame building.
var can20Signals = []aletheia.SignalValue{
	{Name: "EngineSpeed", Value: 2000.0},
	{Name: "EngineTemp", Value: 90.0},
}

// CAN-FD signal values for frame building.
var canfdSignals = []aletheia.SignalValue{
	{Name: "GPSSpeed", Value: 20.0},
	{Name: "YawRate", Value: 0.0},
	{Name: "WheelSpeedFL", Value: 10.0},
	{Name: "WheelSpeedFR", Value: 10.0},
}

// ---------------------------------------------------------------------------
// CAN IDs and DLCs (pre-created)
// ---------------------------------------------------------------------------

var (
	can20ID  = mustStdID(0x100)
	can20DLC = mustDLC(8)
	canfdID  = mustStdID(0x200)
	canfdDLC = mustDLC(15)
)

// ---------------------------------------------------------------------------
// Statistics helpers
// ---------------------------------------------------------------------------

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

func minSlice(xs []float64) float64 {
	m := xs[0]
	for _, x := range xs[1:] {
		if x < m {
			m = x
		}
	}
	return m
}

func maxSlice(xs []float64) float64 {
	m := xs[0]
	for _, x := range xs[1:] {
		if x > m {
			m = x
		}
	}
	return m
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

// ---------------------------------------------------------------------------
// System info
// ---------------------------------------------------------------------------

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

// ---------------------------------------------------------------------------
// Benchmark: Throughput
// ---------------------------------------------------------------------------

func benchmarkStreaming(backend *aletheia.FFIBackend, dbc aletheia.DbcDefinition, id aletheia.CanID, dlc aletheia.DLC, frame aletheia.FramePayload, props []aletheia.Formula, numFrames int) (float64, error) {
	client, err := aletheia.NewClient(backend)
	if err != nil {
		return 0, err
	}
	defer client.Close()

	if _, err := client.ParseDBC(dbc); err != nil {
		return 0, err
	}
	if err := client.SetProperties(props); err != nil {
		return 0, err
	}
	if err := client.StartStream(); err != nil {
		return 0, err
	}

	start := time.Now()
	for i := 0; i < numFrames; i++ {
		if _, err := client.SendFrame(aletheia.Timestamp{Microseconds: int64(i)}, id, dlc, frame); err != nil {
			return 0, err
		}
	}
	elapsed := time.Since(start)

	if _, err := client.EndStream(); err != nil {
		return 0, err
	}
	return float64(numFrames) / elapsed.Seconds(), nil
}

func benchmarkExtraction(backend *aletheia.FFIBackend, dbc aletheia.DbcDefinition, id aletheia.CanID, dlc aletheia.DLC, frame aletheia.FramePayload, numFrames int) (float64, error) {
	client, err := aletheia.NewClient(backend)
	if err != nil {
		return 0, err
	}
	defer client.Close()

	if _, err := client.ParseDBC(dbc); err != nil {
		return 0, err
	}

	start := time.Now()
	for i := 0; i < numFrames; i++ {
		if _, err := client.ExtractSignals(id, dlc, frame); err != nil {
			return 0, err
		}
	}
	elapsed := time.Since(start)
	return float64(numFrames) / elapsed.Seconds(), nil
}

func benchmarkBuilding(backend *aletheia.FFIBackend, dbc aletheia.DbcDefinition, id aletheia.CanID, signals []aletheia.SignalValue, dlc aletheia.DLC, numFrames int) (float64, error) {
	client, err := aletheia.NewClient(backend)
	if err != nil {
		return 0, err
	}
	defer client.Close()

	if _, err := client.ParseDBC(dbc); err != nil {
		return 0, err
	}

	start := time.Now()
	for i := 0; i < numFrames; i++ {
		if _, err := client.BuildFrame(id, signals, dlc); err != nil {
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
	type benchDef struct {
		name string
		fn   func(int) (float64, error)
	}

	dbc20 := can20DBC()
	dbcFD := canfdDBC()

	benchmarks := []benchDef{
		{"CAN 2.0B: Stream LTL (2 props)", func(n int) (float64, error) {
			return benchmarkStreaming(backend, dbc20, can20ID, can20DLC, can20Frame, can20Properties, n)
		}},
		{"CAN 2.0B: Signal Extraction", func(n int) (float64, error) {
			return benchmarkExtraction(backend, dbc20, can20ID, can20DLC, can20Frame, n)
		}},
		{"CAN 2.0B: Frame Building", func(n int) (float64, error) {
			return benchmarkBuilding(backend, dbc20, can20ID, can20Signals, can20DLC, n)
		}},
		{"CAN-FD:   Stream LTL (3 props)", func(n int) (float64, error) {
			return benchmarkStreaming(backend, dbcFD, canfdID, canfdDLC, canfdFrame, canfdProperties, n)
		}},
		{"CAN-FD:   Signal Extraction", func(n int) (float64, error) {
			return benchmarkExtraction(backend, dbcFD, canfdID, canfdDLC, canfdFrame, n)
		}},
		{"CAN-FD:   Frame Building", func(n int) (float64, error) {
			return benchmarkBuilding(backend, dbcFD, canfdID, canfdSignals, canfdDLC, n)
		}},
	}

	var results []throughputResult
	for _, b := range benchmarks {
		fmt.Fprintf(out, "\n%s:\n", b.name)
		fmt.Fprintf(out, "%s\n", strings.Repeat("-", 40))

		// Warmup.
		for w := 0; w < warmupRuns; w++ {
			if _, err := b.fn(numFrames / 10); err != nil {
				fmt.Fprintf(out, "  Warmup error: %v\n", err)
			}
		}

		// Actual runs.
		var fpsList []float64
		for r := 0; r < numRuns; r++ {
			fps, err := b.fn(numFrames)
			if err != nil {
				fmt.Fprintf(out, "  Run %d/%d: ERROR %v\n", r+1, numRuns, err)
				continue
			}
			fpsList = append(fpsList, fps)
			fmt.Fprintf(out, "  Run %d/%d: %.0f ops/sec\n", r+1, numRuns, fps)
		}

		if len(fpsList) == 0 {
			continue
		}
		m := mean(fpsList)
		usPerFrame := 0.0
		if m > 0 {
			usPerFrame = 1_000_000 / m
		}
		results = append(results, throughputResult{
			Name:       b.name,
			Frames:     numFrames,
			Runs:       numRuns,
			FPSMean:    math.Round(m*10) / 10,
			FPSStdev:   math.Round(stdev(fpsList)*10) / 10,
			FPSMin:     math.Round(minSlice(fpsList)*10) / 10,
			FPSMax:     math.Round(maxSlice(fpsList)*10) / 10,
			USPerFrame: math.Round(usPerFrame*10) / 10,
		})
	}

	// Summary.
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

// ---------------------------------------------------------------------------
// Benchmark: Latency
// ---------------------------------------------------------------------------

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

func measureStreamLatencies(backend *aletheia.FFIBackend, dbc aletheia.DbcDefinition, id aletheia.CanID, dlc aletheia.DLC, frame aletheia.FramePayload, props []aletheia.Formula, numOps, warmup int) ([]float64, error) {
	client, err := aletheia.NewClient(backend)
	if err != nil {
		return nil, err
	}
	defer client.Close()

	if _, err := client.ParseDBC(dbc); err != nil {
		return nil, err
	}
	if err := client.SetProperties(props); err != nil {
		return nil, err
	}
	if err := client.StartStream(); err != nil {
		return nil, err
	}

	// Warmup.
	for i := 0; i < warmup; i++ {
		if _, err := client.SendFrame(aletheia.Timestamp{Microseconds: int64(i)}, id, dlc, frame); err != nil {
			return nil, err
		}
	}

	// Measure.
	latencies := make([]float64, 0, numOps)
	for i := 0; i < numOps; i++ {
		start := time.Now()
		if _, err := client.SendFrame(aletheia.Timestamp{Microseconds: int64(warmup + i)}, id, dlc, frame); err != nil {
			return nil, err
		}
		latencies = append(latencies, float64(time.Since(start).Nanoseconds())/1000.0) // microseconds
	}

	if _, err := client.EndStream(); err != nil {
		return nil, err
	}
	return latencies, nil
}

func measureExtractionLatencies(backend *aletheia.FFIBackend, dbc aletheia.DbcDefinition, id aletheia.CanID, dlc aletheia.DLC, frame aletheia.FramePayload, numOps, warmup int) ([]float64, error) {
	client, err := aletheia.NewClient(backend)
	if err != nil {
		return nil, err
	}
	defer client.Close()

	if _, err := client.ParseDBC(dbc); err != nil {
		return nil, err
	}

	for i := 0; i < warmup; i++ {
		if _, err := client.ExtractSignals(id, dlc, frame); err != nil {
			return nil, err
		}
	}

	latencies := make([]float64, 0, numOps)
	for i := 0; i < numOps; i++ {
		start := time.Now()
		if _, err := client.ExtractSignals(id, dlc, frame); err != nil {
			return nil, err
		}
		latencies = append(latencies, float64(time.Since(start).Nanoseconds())/1000.0)
	}
	return latencies, nil
}

func measureBuildLatencies(backend *aletheia.FFIBackend, dbc aletheia.DbcDefinition, id aletheia.CanID, signals []aletheia.SignalValue, dlc aletheia.DLC, numOps, warmup int) ([]float64, error) {
	client, err := aletheia.NewClient(backend)
	if err != nil {
		return nil, err
	}
	defer client.Close()

	if _, err := client.ParseDBC(dbc); err != nil {
		return nil, err
	}

	for i := 0; i < warmup; i++ {
		if _, err := client.BuildFrame(id, signals, dlc); err != nil {
			return nil, err
		}
	}

	latencies := make([]float64, 0, numOps)
	for i := 0; i < numOps; i++ {
		start := time.Now()
		if _, err := client.BuildFrame(id, signals, dlc); err != nil {
			return nil, err
		}
		latencies = append(latencies, float64(time.Since(start).Nanoseconds())/1000.0)
	}
	return latencies, nil
}

func analyzeLatencies(name string, raw []float64) latencyStats {
	sorted := make([]float64, len(raw))
	copy(sorted, raw)
	sort.Float64s(sorted)
	return latencyStats{
		Name:   name,
		Count:  len(raw),
		MeanUS: math.Round(mean(raw)*10) / 10,
		MinUS:  math.Round(minSlice(raw)*10) / 10,
		MaxUS:  math.Round(maxSlice(raw)*10) / 10,
		P50US:  math.Round(percentile(sorted, 50)*10) / 10,
		P90US:  math.Round(percentile(sorted, 90)*10) / 10,
		P99US:  math.Round(percentile(sorted, 99)*10) / 10,
		P999US: math.Round(percentile(sorted, 99.9)*10) / 10,
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

func runLatencySuite(backend *aletheia.FFIBackend, out *os.File, label string, dbc aletheia.DbcDefinition, id aletheia.CanID, dlc aletheia.DLC, frame aletheia.FramePayload, signals []aletheia.SignalValue, props []aletheia.Formula, numOps, warmup int) []latencyStats {
	var allStats []latencyStats

	// Streaming.
	fmt.Fprintf(out, "\nBenchmarking %s streaming...\n", label)
	lat, err := measureStreamLatencies(backend, dbc, id, dlc, frame, props, numOps, warmup)
	if err != nil {
		fmt.Fprintf(out, "  ERROR: %v\n", err)
	} else {
		s := analyzeLatencies(label+" Streaming LTL", lat)
		printLatencyStats(out, s)
		allStats = append(allStats, s)
	}

	// Extraction.
	fmt.Fprintf(out, "\nBenchmarking %s signal extraction...\n", label)
	lat, err = measureExtractionLatencies(backend, dbc, id, dlc, frame, numOps, warmup)
	if err != nil {
		fmt.Fprintf(out, "  ERROR: %v\n", err)
	} else {
		s := analyzeLatencies(label+" Signal Extraction", lat)
		printLatencyStats(out, s)
		allStats = append(allStats, s)
	}

	// Frame building.
	fmt.Fprintf(out, "\nBenchmarking %s frame building...\n", label)
	lat, err = measureBuildLatencies(backend, dbc, id, signals, dlc, numOps, warmup)
	if err != nil {
		fmt.Fprintf(out, "  ERROR: %v\n", err)
	} else {
		s := analyzeLatencies(label+" Frame Building", lat)
		printLatencyStats(out, s)
		allStats = append(allStats, s)
	}

	return allStats
}

func runLatency(backend *aletheia.FFIBackend, out *os.File, numOps, warmup int) []latencyStats {
	dbc20 := can20DBC()
	dbcFD := canfdDBC()

	stats := runLatencySuite(backend, out, "CAN 2.0B", dbc20, can20ID, can20DLC, can20Frame, can20Signals, can20Properties, numOps, warmup)
	stats = append(stats, runLatencySuite(backend, out, "CAN-FD", dbcFD, canfdID, canfdDLC, canfdFrame, canfdSignals, canfdProperties, numOps, warmup)...)

	// Summary table.
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

// ---------------------------------------------------------------------------
// Benchmark: Scaling (property count)
// ---------------------------------------------------------------------------

type scalingResult struct {
	Properties int     `json:"properties"`
	FPS        float64 `json:"fps"`
	USPerFrame float64 `json:"us_per_frame"`
	Relative   float64 `json:"relative"`
}

func makeProperties(count int) []aletheia.Formula {
	templates := []aletheia.Formula{
		aletheia.Always{Inner: aletheia.Atomic{Predicate: aletheia.Between{Signal: "EngineSpeed", Min: 0, Max: 8000}}},
		aletheia.Always{Inner: aletheia.Atomic{Predicate: aletheia.Between{Signal: "EngineTemp", Min: -40, Max: 215}}},
		aletheia.Always{Inner: aletheia.Atomic{Predicate: aletheia.LessThan{Signal: "BrakePressure", Value: 6553.5}}},
		aletheia.Always{Inner: aletheia.Atomic{Predicate: aletheia.LessThan{Signal: "EngineSpeed", Value: 7000}}},
		aletheia.Always{Inner: aletheia.Atomic{Predicate: aletheia.LessThan{Signal: "EngineTemp", Value: 200}}},
		aletheia.Always{Inner: aletheia.Atomic{Predicate: aletheia.LessThan{Signal: "BrakePressure", Value: 5000}}},
		aletheia.Always{Inner: aletheia.Atomic{Predicate: aletheia.Between{Signal: "EngineSpeed", Min: 500, Max: 7500}}},
		aletheia.Always{Inner: aletheia.Atomic{Predicate: aletheia.Between{Signal: "EngineTemp", Min: -20, Max: 180}}},
		aletheia.Always{Inner: aletheia.Atomic{Predicate: aletheia.Between{Signal: "BrakePressure", Min: 0, Max: 4000}}},
		aletheia.Always{Inner: aletheia.Atomic{Predicate: aletheia.LessThan{Signal: "EngineSpeed", Value: 6000}}},
	}
	props := make([]aletheia.Formula, count)
	for i := 0; i < count; i++ {
		props[i] = templates[i%len(templates)]
	}
	return props
}

func runScaling(backend *aletheia.FFIBackend, out *os.File, numFrames, numRuns int) []scalingResult {
	dbc20 := can20DBC()
	counts := []int{1, 2, 3, 5, 7, 10}

	fmt.Fprintf(out, "\n%s\n", strings.Repeat("=", 70))
	fmt.Fprintf(out, "Property Count Scaling (CAN 2.0B)\n")
	fmt.Fprintf(out, "%s\n", strings.Repeat("=", 70))
	fmt.Fprintf(out, "%10s %12s %10s %10s\n", "Properties", "Frames/sec", "us/frame", "Relative")
	fmt.Fprintf(out, "%s\n", strings.Repeat("-", 45))

	// Warmup.
	if _, err := benchmarkStreaming(backend, dbc20, can20ID, can20DLC, can20Frame, makeProperties(1), numFrames/10); err != nil {
		fmt.Fprintf(out, "Warmup error: %v\n", err)
	}

	var results []scalingResult
	var baselineFPS float64
	for _, count := range counts {
		props := makeProperties(count)
		var fpsList []float64
		for r := 0; r < numRuns; r++ {
			fps, err := benchmarkStreaming(backend, dbc20, can20ID, can20DLC, can20Frame, props, numFrames)
			if err != nil {
				fmt.Fprintf(out, "  Error with %d props: %v\n", count, err)
				continue
			}
			fpsList = append(fpsList, fps)
		}
		if len(fpsList) == 0 {
			continue
		}
		m := mean(fpsList)
		if baselineFPS == 0 {
			baselineFPS = m
		}
		relative := m / baselineFPS
		usPerFrame := 0.0
		if m > 0 {
			usPerFrame = 1_000_000 / m
		}
		fmt.Fprintf(out, "%10d %12.0f %10.1f %10.2fx\n", count, m, usPerFrame, relative)
		results = append(results, scalingResult{
			Properties: count,
			FPS:        math.Round(m*10) / 10,
			USPerFrame: math.Round(usPerFrame*10) / 10,
			Relative:   math.Round(relative*1000) / 1000,
		})
	}

	fmt.Fprintf(out, "\nExpected: Some degradation, but should be sub-linear\n")
	fmt.Fprintf(out, "%s\n", strings.Repeat("=", 70))
	return results
}

// ---------------------------------------------------------------------------
// JSON output
// ---------------------------------------------------------------------------

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
	enc.Encode(out)
}

// ---------------------------------------------------------------------------
// Main
// ---------------------------------------------------------------------------

func main() {
	fs := flag.NewFlagSet("bench", flag.ExitOnError)
	frames := fs.Int("frames", 10000, "Frames per run")
	runs := fs.Int("runs", 5, "Number of runs")
	warmup := fs.Int("warmup", 2, "Warmup runs (throughput) / warmup ops (latency)")
	ops := fs.Int("ops", 5000, "Operations to measure (latency)")
	jsonFlag := fs.Bool("json", false, "Emit JSON to stdout")

	// Parse: first positional arg is the mode.
	args := os.Args[1:]
	mode := "throughput"
	if len(args) > 0 && !strings.HasPrefix(args[0], "-") {
		mode = args[0]
		args = args[1:]
	}
	fs.Parse(args)

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
		fmt.Fprintf(os.Stderr, "Failed to load FFI backend: %v\n", err)
		os.Exit(1)
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
		fmt.Fprintf(out, "Frames per run: %d\n", *frames)
		fmt.Fprintf(out, "Runs: %d\n", *runs)
		results := runScaling(backend, out, *frames, *runs)
		if *jsonFlag {
			emitJSON("scaling", results)
		}

	default:
		fmt.Fprintf(os.Stderr, "Unknown mode: %s (use throughput, latency, or scaling)\n", mode)
		os.Exit(1)
	}
}
