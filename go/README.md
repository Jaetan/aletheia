# Aletheia Go Binding

Go interface for the Aletheia formally verified CAN frame analyzer.

## Installation

See [../docs/development/BUILDING.md](../docs/development/BUILDING.md) and [../docs/development/DISTRIBUTION.md](../docs/development/DISTRIBUTION.md) for build and integration instructions.

Quick start:
```bash
cabal run shake -- build       # Build Agda + Haskell + libaletheia-ffi.so
cd go && go test ./aletheia/ -count=1 -race
```

## Modules

- `go/aletheia/` — main binding (cgo + dlopen; FFI trampolines for Haskell RTS)
- `go/excel/` — separate Go module pulling `xuri/excelize` for the Excel loader; depend on it only when needed

## Usage

The binding wraps `libaletheia-ffi.so` via cgo + dlopen. `Backend` /
`MockBackend` / `FFIBackend` give the dependency-injection seam. The program
below runs under the doc-example harness (`go/aletheia/doc_examples_test.go`);
[../docs/reference/GO_API.md](../docs/reference/GO_API.md) covers the whole API.

```go
package main

import (
	"context"
	"fmt"

	"github.com/aletheia-automotive/aletheia-go/v5/aletheia"
)

func main() {
	// NewFFIBackend(path, ...) takes an explicit library path instead.
	backend, err := aletheia.NewFFIBackendFromEnv(aletheia.WithRTSCores(1))
	if err != nil {
		panic(err)
	}
	client, err := aletheia.NewClient(backend)
	if err != nil {
		panic(err)
	}
	defer client.Close()
	ctx := context.Background()

	const dbc = `VERSION ""

NS_ :

BS_:

BU_: ECU

BO_ 256 Engine: 8 ECU
 SG_ Speed : 0|16@1+ (0.1,0) [0|6553.5] "km/h" ECU
`
	if _, err := client.ParseDBCText(ctx, dbc); err != nil {
		panic(err)
	}

	// The property: the decoded Speed signal never exceeds 220 km/h.
	speedLimit := aletheia.Never(aletheia.Signal("Speed").GreaterThan(aletheia.IntRational(220)))
	if err := client.SetProperties(ctx, []aletheia.Formula{speedLimit}); err != nil {
		panic(err)
	}
	if err := client.StartStream(ctx); err != nil {
		panic(err)
	}

	id, _ := aletheia.NewStandardID(0x100)
	dlc, _ := aletheia.NewDLC(8)
	// Raw 0x0FA0 at factor 0.1 decodes to 400 km/h, so this frame violates the property.
	// The two nils are the CAN-FD BRS and ESI bits (ISO 11898-1:2015 §10.4.2 / §10.4.3),
	// absent on a CAN 2.0B frame.
	frame := aletheia.FramePayload{0xA0, 0x0F, 0, 0, 0, 0, 0, 0}
	resp, err := client.SendFrame(ctx, aletheia.Timestamp{Microseconds: 1000}, id, dlc, frame, nil, nil)
	if err != nil {
		panic(err)
	}
	if batch, ok := resp.(aletheia.PropertyBatch); ok {
		if v := batch.FirstViolation(); v != nil {
			fmt.Println("violation:", v.Reason)
		}
	}

	summary, err := client.EndStream(ctx)
	if err != nil {
		panic(err)
	}
	fmt.Println(len(summary.Results), "verdict(s) at end of stream")
}
```

## Concurrency

`Client` is goroutine-safe: its operations are serialised through a 1-deep
channel semaphore (`lockCh chan struct{}`) rather than a `sync.Mutex`, so a
goroutine waiting for the lock is cancelled by its `context.Context` without
ever acquiring it, which neither `Lock` nor `TryLock` can express (see
[../docs/architecture/CANCELLATION.md](../docs/architecture/CANCELLATION.md)
§ 2.2). Every call into the library runs on a pinned OS thread
(`runtime.LockOSThread`), and the GHC RTS is initialised once per process by
the first `FFIBackend`. See
[../docs/architecture/CGO_NOTES.md](../docs/architecture/CGO_NOTES.md) for the
cgo + dlopen rationale.

## Cancellation

`context.Context` is honored on all streaming entry points; see
[../docs/architecture/CANCELLATION.md](../docs/architecture/CANCELLATION.md)
for the cross-binding contract.

## Testing

```bash
cd go
go test ./aletheia/ -count=1 -race
go vet ./...
gofmt -l .   # expect empty
```

## See Also

- [Go API Reference](../docs/reference/GO_API.md)
- [Interface Guide](../docs/reference/INTERFACES.md) — Check API
- [Distribution Guide](../docs/development/DISTRIBUTION.md) — packaging the `.so`
- [cgo Notes](../docs/architecture/CGO_NOTES.md) — dlopen rationale, GHC RTS thread pinning
- [Cancellation Contract](../docs/architecture/CANCELLATION.md) — `context.Context` semantics
- [Mutation Testing](../docs/operations/MUTATION.md) — gremlins lane
