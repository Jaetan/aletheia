// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// Bundle-consumer fixture (C++): drives the shared release-bundle scenario
// through the bundled binding — env-constructor (the ALETHEIA_LIB seam set by
// the bundle's env.sh), parse_dbc_text of a real .dbc, an
// Always(VehicleSpeed < 100) LTL property, one conforming and one violating
// frame, exactly one violation on the expected property, end_stream.  Built
// and run by tools/bundle_validate.py against an unpacked release bundle.

#include <aletheia/client.hpp>

#include <array>
#include <cstddef>
#include <cstdio>
#include <fstream>
#include <iterator>
#include <span>
#include <stop_token>
#include <string>
#include <utility>
#include <variant>
#include <vector>

namespace {

auto fail(const std::string& message) -> int {
    std::fprintf(stderr, "BUNDLE-CONSUMER cpp: FAIL — %s\n", message.c_str());
    return 1;
}

} // namespace

auto main(int argc, char** argv) -> int {
    using namespace aletheia;

    if (argc != 2)
        return fail("usage: your_app <scenario-dbc-path>");
    std::ifstream dbc_file(argv[1]);
    if (!dbc_file)
        return fail(std::string("cannot open ") + argv[1]);
    std::string dbc_text{std::istreambuf_iterator<char>(dbc_file),
                         std::istreambuf_iterator<char>()};

    // Env-constructor: resolves the shared library through ALETHEIA_LIB.
    AletheiaClient client(make_ffi_backend_from_env());
    std::stop_token stop{};

    auto parsed = client.parse_dbc_text(stop, dbc_text);
    if (!parsed.has_value())
        return fail("parse_dbc_text: " + std::string(parsed.error().message()));
    if (parsed->dbc.messages.size() != 2)
        return fail("vehicle.dbc should carry the VehicleDynamics + BrakeStatus messages");

    // Always(VehicleSpeed < 100 kph).
    std::vector<LtlFormula> props;
    props.push_back(ltl::always(
        ltl::atomic(ltl::less_than(SignalName{"VehicleSpeed"}, PhysicalValue{Rational{100, 1}}))));
    if (auto r = client.set_properties(stop, props); !r.has_value())
        return fail("set_properties: " + std::string(r.error().message()));
    if (auto r = client.start_stream(stop); !r.has_value())
        return fail("start_stream: " + std::string(r.error().message()));

    auto sid = StandardId::create(256);
    auto dlc = Dlc::create(8);
    if (!sid.has_value() || !dlc.has_value())
        return fail("frame identity construction");
    CanId id{sid.value()};

    // Conforming frame: VehicleSpeed raw 0x1388 (5000) → 50.00 kph (factor 0.01).
    auto conforming = std::array<std::byte, 8>{std::byte{0x88}, std::byte{0x13}};
    auto ack = client.send_frame(stop, Timestamp{1000}, id, dlc.value(),
                                 std::span<const std::byte>{conforming});
    if (!ack.has_value())
        return fail("send_frame (conforming): " + std::string(ack.error().message()));
    if (!std::holds_alternative<Ack>(ack.value()))
        return fail("the conforming frame should be acknowledged without property events");

    // Violating frame: VehicleSpeed raw 0x4E20 (20000) → 200.00 kph, over the bound.
    auto violating = std::array<std::byte, 8>{std::byte{0x20}, std::byte{0x4E}};
    auto resp = client.send_frame(stop, Timestamp{2000}, id, dlc.value(),
                                  std::span<const std::byte>{violating});
    if (!resp.has_value())
        return fail("send_frame (violating): " + std::string(resp.error().message()));
    const auto* batch = std::get_if<PropertyBatch>(&resp.value());
    if (batch == nullptr)
        return fail("the violating frame should produce a property batch");
    std::size_t violations = 0;
    for (const auto& r : batch->results)
        if (r.verdict == Verdict::Fails)
            ++violations;
    if (violations != 1)
        return fail("expected exactly one violation from the violating frame");
    const auto* violation = std::as_const(*batch).first_violation();
    if (violation->property_index != PropertyIndex{0})
        return fail("the violation should name the single installed property");
    if (!violation->enrichment.has_value() ||
        !violation->enrichment->signals.contains(SignalName{"VehicleSpeed"}))
        return fail("the violation should be enriched with the VehicleSpeed value");

    if (auto ended = client.end_stream(stop); !ended.has_value())
        return fail("end_stream: " + std::string(ended.error().message()));

    std::printf("BUNDLE-CONSUMER cpp: OK — exactly one violation on the expected property\n");
    return 0;
}
