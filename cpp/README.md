# Aletheia C++ Binding

C++23 interface for the Aletheia formally verified CAN frame analyzer.

## Installation

See [../docs/development/BUILDING.md](../docs/development/BUILDING.md) and [../docs/development/DISTRIBUTION.md](../docs/development/DISTRIBUTION.md) for build and integration instructions.

Quick start (build the kernel, then configure, build and test the binding):
```bash
cabal run shake -- build      # Build Agda + Haskell + libaletheia-ffi.so
cd cpp && cmake -B build -DCMAKE_C_COMPILER=clang-22 -DCMAKE_CXX_COMPILER=clang++-22 && cmake --build build && ctest --test-dir build
```

## Compilers

C++23, built and tested with **Clang 22** — configure with
`-DCMAKE_CXX_COMPILER=clang++-22`. The toolchain's libstdc++/libc++ must provide
C++23 (`<expected>`, `<format>`). For the full support policy (why Clang 22, g++
dropped, older-Clang stance) see
[BUILDING.md § Toolchain support policy](../docs/development/BUILDING.md#toolchain-support-policy).
Build settings: `.clang-format`, `.clang-tidy`, `CMakeLists.txt`.

## Usage

The binding wraps `libaletheia-ffi.so` via `dlopen` (no link-time dependency).
The `IBackend` interface is the seam used in tests; production code uses
`make_ffi_backend_from_env()` (loads the library named by the `ALETHEIA_LIB`
environment variable) or `make_ffi_backend(path)` for an explicit path. See
[../docs/reference/INTERFACES.md](../docs/reference/INTERFACES.md) and the
doc-example tests under `cpp/tests/doc_example_tests.cpp` for tested, runnable
examples.

```cpp
#include <aletheia/aletheia.hpp>
#include <stop_token>
#include <string_view>
#include <variant>
#include <vector>

int main() {
    using namespace aletheia;
    auto backend = make_ffi_backend_from_env(); // loads $ALETHEIA_LIB
    AletheiaClient client{std::move(backend)};

    // std::stop_token{} never reports stop_requested; see CANCELLATION.md.
    std::stop_token stop{};

    constexpr std::string_view dbc_text = R"(VERSION ""

NS_ :

BS_:

BU_: ECU

BO_ 256 Engine: 8 ECU
 SG_ Speed : 0|16@1+ (0.1,0) [0|6553.5] "km/h" ECU
)";
    if (!client.parse_dbc_text(stop, dbc_text))
        return 1;

    // Every method returns std::expected; an error carries an AletheiaError.
    std::vector<LtlFormula> properties;
    properties.push_back(ltl::always(
        ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{Rational{220, 1}}))));
    if (!client.set_properties(stop, properties) || !client.start_stream(stop))
        return 1;

    std::vector<Frame> frames;
    frames.push_back(Frame{Timestamp{1000}, CanId{StandardId::create(0x100).value()},
                           Dlc::create(8).value(), FramePayload(8, std::byte{0}),
                           std::nullopt, std::nullopt});
    for (const auto& f : frames) {
        auto resp = client.send_frame(stop, f); // Result<FrameResponse>
        if (!resp)
            return 1;
        if (std::holds_alternative<PropertyBatch>(*resp)) {
            // a verdict changed on this frame
        }
    }

    auto summary = client.end_stream(stop); // Result<StreamResult>
    return summary ? 0 : 1;
}
```

## Cancellation

Every client method takes a `std::stop_token` as its first parameter; see
[../docs/architecture/CANCELLATION.md](../docs/architecture/CANCELLATION.md)
for the cross-binding contract.

## See Also

- [Interface Guide](../docs/reference/INTERFACES.md) — Check API
- [Distribution Guide](../docs/development/DISTRIBUTION.md) — packaging the `.so`
- [Cancellation Contract](../docs/architecture/CANCELLATION.md) — `std::stop_token` semantics
- [Mutation Testing](../docs/operations/MUTATION.md) — the Mull lane
