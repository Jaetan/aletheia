# Aletheia C++ Binding

C++23 interface for the Aletheia formally verified CAN frame analyzer.

## Installation

See [../docs/development/BUILDING.md](../docs/development/BUILDING.md) and [../docs/development/DISTRIBUTION.md](../docs/development/DISTRIBUTION.md) for build and integration instructions.

Quick start:
```bash
cabal run shake -- build      # Build Agda + Haskell + libaletheia-ffi.so
cd cpp && cmake -B build -DCMAKE_C_COMPILER=clang-19 -DCMAKE_CXX_COMPILER=clang++-19 && cmake --build build && ctest --test-dir build
```

## Compilers

C++23, **Clang ≥ 19 only** (g++ is not supported). Configure with
`-DCMAKE_CXX_COMPILER=clang++-19`; the toolchain's libstdc++/libc++ must
provide C++23 (`<expected>`, `<format>`). Build settings: `.clang-format`,
`.clang-tidy`, `CMakeLists.txt`.

## Usage

The binding wraps `libaletheia-ffi.so` via `dlopen` (no link-time dependency).
The `IBackend` interface is the seam used in tests; production code uses
`make_ffi_backend()`. See [../docs/reference/INTERFACES.md](../docs/reference/INTERFACES.md)
and the doc-example tests under `cpp/tests/doc_example_tests.cpp` for tested,
runnable examples.

```cpp
#include <aletheia/aletheia.hpp>
#include <stop_token>

auto backend = aletheia::make_ffi_backend();
aletheia::AletheiaClient client{std::move(backend)};

// std::stop_token{} never reports stop_requested — see CANCELLATION.md.
std::stop_token stop{};

client.parse_dbc_text(stop, dbc_text);
client.set_properties(stop, properties);
client.start_stream(stop);

for (auto const& f : frames) {  // aletheia::Frame { timestamp, id, dlc, data, brs, esi }
    auto resp = client.send_frame(stop, f);
    if (resp && std::holds_alternative<aletheia::PropertyBatch>(*resp)) {
        // ...
    }
}

auto summary = client.end_stream(stop);
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
