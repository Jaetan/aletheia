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
`MockBackend` / `FFIBackend` give the dependency-injection seam. See
[../docs/reference/INTERFACES.md](../docs/reference/INTERFACES.md) and the
doc-example tests in `go/aletheia/doc_examples_test.go` for tested, runnable
examples.

```go
import "github.com/anthropics/aletheia/go/aletheia"

backend, err := aletheia.NewFFIBackend(aletheia.WithRTSCores(1))
if err != nil { ... }

client, err := aletheia.NewClient(backend)
if err != nil { ... }
defer client.Close()

if err := client.ParseDBC(ctx, dbcJSON); err != nil { ... }
if err := client.SetProperties(ctx, properties); err != nil { ... }
if err := client.StartStream(ctx); err != nil { ... }

for _, f := range frames {
    resp, err := client.SendFrame(ctx, f.Timestamp, f.ID, f.DLC, f.Data)
    if err != nil { ... }
    if v, ok := resp.(aletheia.Violation); ok {
        // ...
    }
}

summary, err := client.EndStream(ctx)
```

## Concurrency

`Client` is goroutine-safe via `sync.Mutex`. The Haskell RTS init is
thread-pinned (`runtime.LockOSThread`) on first use. See
[../docs/architecture/CGO_NOTES.md](../docs/architecture/CGO_NOTES.md) for the
cgo + dlopen rationale and thread-pinning details.

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

- [Interface Guide](../docs/reference/INTERFACES.md) — Check API
- [Distribution Guide](../docs/development/DISTRIBUTION.md) — packaging the `.so`
- [cgo Notes](../docs/architecture/CGO_NOTES.md) — dlopen rationale, GHC RTS thread pinning
- [Cancellation Contract](../docs/architecture/CANCELLATION.md) — `context.Context` semantics
- [Mutation Testing](../docs/operations/MUTATION.md) — gremlins lane
