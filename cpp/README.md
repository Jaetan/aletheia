# Aletheia C++ Binding

C++23 interface for the Aletheia formally verified CAN frame analyzer.

## Installation

See [../docs/development/BUILDING.md](../docs/development/BUILDING.md) and [../docs/development/DISTRIBUTION.md](../docs/development/DISTRIBUTION.md) for build and integration instructions.

Quick start:
```bash
cabal run shake -- build      # Build Agda + Haskell + libaletheia-ffi.so
cd cpp && cmake -B build && cmake --build build && ctest --test-dir build
```

## Compilers

C++23, targeting **g++ ≥ 14** and **clang ≥ 21**. Use any C++23 feature both
support. Build settings: `.clang-format`, `.clang-tidy`, `CMakeLists.txt`.

## Usage

The binding wraps `libaletheia-ffi.so` via `dlopen` (no link-time dependency).
The `IBackend` interface is the seam used in tests; production code uses
`make_ffi_backend()`. See [../docs/reference/INTERFACES.md](../docs/reference/INTERFACES.md)
and the doc-example tests under `cpp/tests/doc_example_tests.cpp` for tested,
runnable examples.

```cpp
#include <aletheia/aletheia.hpp>

auto backend = aletheia::make_ffi_backend();
aletheia::Client client{std::move(backend)};

client.parse_dbc(dbc_json);
client.set_properties(properties_json);
client.start_stream();

for (auto const& [timestamp, can_id, dlc, data, extended] : frames) {
    auto resp = client.send_frame(timestamp, can_id, dlc, data, extended);
    if (std::holds_alternative<aletheia::PropertyViolationResponse>(resp)) {
        // ...
    }
}

auto summary = client.end_stream();
```

## Cancellation

`std::stop_token` is supported on the streaming entry points; see
[../docs/architecture/CANCELLATION.md](../docs/architecture/CANCELLATION.md)
for the cross-binding contract.

## Testing

```bash
cd cpp
cmake -B build && cmake --build build
ctest --test-dir build
```

## See Also

- [Interface Guide](../docs/reference/INTERFACES.md) — Check API
- [Distribution Guide](../docs/development/DISTRIBUTION.md) — packaging the `.so`
- [Cancellation Contract](../docs/architecture/CANCELLATION.md) — `std::stop_token` semantics
- [Mutation Testing](../docs/operations/MUTATION.md) — Mull-19 lane
