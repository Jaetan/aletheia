// Microbenchmark: response parsing overhead on the Go side.
//
// Measures the cost of each step in the ack response path:
// 1. String comparison (current fast path)
// 2. json.Unmarshal (slow path / baseline)
// 3. Hypothetical binary: read status byte
//
// Run: cd benchmarks && go test -bench=. -benchmem response_overhead_test.go

package main

import (
	"encoding/json"
	"fmt"
	"runtime"
	"time"
	"unsafe"
)

const (
	iterations = 5_000_000
	warmup     = 500_000

	ackCompact = `{"status":"ack"}`
	ackSpaced  = `{"status": "ack"}`

	violationJSON = `{"type":"property","status":"fails","property_index":0,` +
		`"timestamp":1234567890,"reason":"Signal EngineSpeed exceeded 220"}`
)

func bench(name string, f func(), iters int) float64 {
	// Warmup
	for i := 0; i < warmup; i++ {
		f()
	}
	runtime.GC()

	start := time.Now()
	for i := 0; i < iters; i++ {
		f()
	}
	elapsed := time.Since(start)
	nsPerOp := float64(elapsed.Nanoseconds()) / float64(iters)
	fmt.Printf("  %-45s  %8.1f ns/op\n", name, nsPerOp)
	return nsPerOp
}

// noescape prevents the compiler from optimizing away allocations.
//
//go:noinline
func sink(v any) { _ = v }

func main() {
	fmt.Println("Response parsing overhead (Go)")
	fmt.Printf("Iterations: %d\n\n", iterations)

	ackStr := ackCompact
	violStr := violationJSON

	fmt.Println("=== Ack response (hot path, ~99% of frames) ===")

	// 1. String comparison (current fast path)
	tCmp := bench("string comparison", func() {
		is := (ackStr == ackCompact) || (ackStr == ackSpaced)
		sink(is)
	}, iterations)

	// 2. json.Unmarshal to map
	tJSON := bench("json.Unmarshal(ack)", func() {
		var m map[string]any
		_ = json.Unmarshal([]byte(ackStr), &m)
		sink(m)
	}, iterations)

	// 3. json.Unmarshal to struct
	type ackResp struct {
		Status string `json:"status"`
	}
	tJSONStruct := bench("json.Unmarshal(ack, struct)", func() {
		var r ackResp
		_ = json.Unmarshal([]byte(ackStr), &r)
		sink(r)
	}, iterations)

	// 4. Hypothetical binary: read status byte
	binaryAck := []byte{0x00}
	tBin := bench("binary: read status byte", func() {
		is := binaryAck[0] == 0x00
		sink(is)
	}, iterations)

	// 5. Simulated CString → Go string (unsafe, like cgo does)
	cBytes := []byte(ackCompact + "\x00")
	cPtr := unsafe.Pointer(&cBytes[0])
	tCgo := bench("C.GoString simulation (16 bytes)", func() {
		// Simulate what cgo's C.GoString does: find null, copy bytes
		p := (*[64]byte)(cPtr)
		n := 0
		for p[n] != 0 {
			n++
		}
		s := string(p[:n])
		sink(s)
	}, iterations)

	fmt.Println()
	budget := 1_000_000_000.0 / 48_000 // ~20.8 us at 48k fps
	fmt.Printf("  Fast path saves vs json.Unmarshal: %8.1f ns/frame\n", tJSON-tCmp)
	fmt.Printf("  Binary saves vs fast path:         %8.1f ns/frame\n", tCmp-tBin)
	fmt.Printf("  CString→Go string overhead:        %8.1f ns/frame\n", tCgo)
	fmt.Printf("\n=== Context ===\n")
	fmt.Printf("  Per-frame budget at 48k fps:       %8.0f ns\n", budget)
	fmt.Printf("  Fast path %% of budget:             %8.1f%%\n", tCmp/budget*100)
	fmt.Printf("  json.Unmarshal %% of budget:        %8.1f%%\n", tJSON/budget*100)
	fmt.Printf("  json struct %% of budget:           %8.1f%%\n", tJSONStruct/budget*100)
	fmt.Printf("  Binary %% of budget:                %8.1f%%\n", tBin/budget*100)

	// --- Violation path ---
	fmt.Println("\n=== Violation response (rare) ===")

	bench("json.Unmarshal(violation, map)", func() {
		var m map[string]any
		_ = json.Unmarshal([]byte(violStr), &m)
		sink(m)
	}, 1_000_000)

	bench("[]byte conversion (violation)", func() {
		b := []byte(violStr)
		sink(b)
	}, 1_000_000)
}
