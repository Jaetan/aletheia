// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// Every reply reader accepts a broken place of a real reply or refuses it in
// the one form. Each case's reply is the real kernel's answer to a command;
// every place of it is broken in turn, its key deleted, its value replaced by
// another JSON kind, or an array's entry so replaced, and each broken copy is
// fed to the reader of that reply, which accepts it or refuses it as
// "reply <path>: expected <what>, got <what came>" naming the broken place.
// The cases and the breaks are those of the Python binding's
// test_reply_places_refused_where_broken.py.

#include <catch2/catch_message.hpp>
#include <catch2/catch_test_macros.hpp>

#include <aletheia/aletheia.hpp>

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <exception>
#include <format>
#include <initializer_list>
#include <iterator>
#include <map>
#include <optional>
#include <ranges>
#include <regex>
#include <set>
#include <sstream>
#include <string>
#include <string_view>
#include <utility>
#include <variant>
#include <vector>

#include "detail/json.hpp"
#include "detail/wide_json.hpp"
#include "kernel_session.hpp"
#include "repo_root.hpp"
#include "required.hpp"
#include "text_file.hpp"

using aletheia::detail::Json;
using aletheia::test::KernelSession;
using aletheia::test::required;

using namespace aletheia;

namespace {

// The reader of a kernel reply, named by the command whose reply it reads.
enum class Reader : std::uint8_t {
    ParseDbc,
    FormatDbc,
    FormatDbcText,
    ValidateDbc,
    Frame,
    EndStream,
    Extraction,
    Envelope,
};

} // namespace

static auto reader_name(Reader reader) -> std::string_view {
    switch (reader) {
    case Reader::ParseDbc:
        return "parseDBC";
    case Reader::FormatDbc:
        return "formatDBC";
    case Reader::FormatDbcText:
        return "formatDBCText";
    case Reader::ValidateDbc:
        return "validateDBC";
    case Reader::Frame:
        return "frame";
    case Reader::EndStream:
        return "endStream";
    case Reader::Extraction:
        return "extractAllSignals";
    case Reader::Envelope:
        return "error envelope";
    }
    return "unnamed reader";
}

// The scenarios a real reply comes from, beside the corpus and the envelopes.
constexpr std::string_view kitchen_sink = "kitchen_sink";
constexpr std::string_view unknown_target = "value_tables with an unknown VAL_ target";
constexpr std::string_view twin = "kitchen_sink with a twin message";
constexpr std::string_view five_properties = "kitchen_sink with five properties";
constexpr std::string_view mixed = "a value, an over-range error and an absent signal";

// The corpus DBCs every load case reads.
constexpr auto corpus = std::to_array<std::string_view>({
    kitchen_sink,
    "attributes",
    "comments_groups",
    "env_vars",
    "value_tables",
    "multiplexing",
    "extended_can",
});

namespace {

// One refused load: its fixture, the code its envelope carries, and the
// kitchen_sink text the kernel refuses.
struct Envelope {
    std::string_view fixture;
    std::string_view code;
    std::string (*text)(std::string const& base);
};

} // namespace

// Four kitchen_sink variants, each refused with its code.
static auto envelopes() -> std::array<Envelope, 4> {
    return {{
        {.fixture = "trailing input",
         .code = "text_trailing_input",
         .text = [](std::string const& base) { return base + "\nBO_ 1 X: 8\n"; }},
        {.fixture = "invalid character",
         .code = "dbc_invalid_character",
         .text = [](std::string const& base) { return base + "\nCM_ \"a\"\"b\";\n"; }},
        {.fixture = "identifier past its bound",
         .code = "input_bound_exceeded",
         .text =
             [](std::string const& base) {
                 auto out = base;
                 return out.replace(out.find("BU_: "), 5, "BU_: " + std::string(129, 'N') + " ");
             }},
        {.fixture = "validation failed",
         .code = "handler_validation_failed",
         .text =
             [](std::string const& base) {
                 return base +
                        "\nBO_ 256 Twin: 8 Engine\n SG_ D : 0|8@1+ (1,0) [0|255] \"\" Gateway\n";
             }},
    }};
}

namespace {

// A reader and the real reply it is fed broken copies of.
struct Case {
    Reader reader;
    std::string fixture;

    auto operator<=>(Case const&) const = default;
};

} // namespace

// Every case: each load and its formatted DBC, the text formatter and the
// validator on kitchen_sink and its twin, a frame's batch, the end of that
// stream, an extraction, and four refused loads.
static auto cases() -> std::vector<Case> {
    std::vector<Case> out;
    for (auto const reader : {Reader::ParseDbc, Reader::FormatDbc}) {
        for (auto const fixture : corpus)
            out.push_back({.reader = reader, .fixture = std::string{fixture}});
        out.push_back({.reader = reader, .fixture = std::string{unknown_target}});
    }
    for (auto const& [reader, fixture] : std::initializer_list<std::pair<Reader, std::string_view>>{
             {Reader::FormatDbcText, kitchen_sink},
             {Reader::FormatDbcText, twin},
             {Reader::ValidateDbc, kitchen_sink},
             {Reader::ValidateDbc, twin},
             {Reader::Frame, five_properties},
             {Reader::EndStream, five_properties},
             {Reader::Extraction, mixed},
         })
        out.push_back({.reader = reader, .fixture = std::string{fixture}});
    for (auto const& envelope : envelopes())
        out.push_back({.reader = Reader::Envelope, .fixture = std::string{envelope.fixture}});
    return out;
}

// Message 256 of the mixed DBC holds a selector, a halved value, a signal its
// selector leaves out and one whose value's numerator passes the wire's
// 128-bit bound.
constexpr std::string_view mixed_text =
    "VERSION \"\"\n\nNS_ :\n\nBS_:\n\nBU_: ECU\n\nBO_ 256 Mixed: 8 ECU\n"
    " SG_ Mode M : 0|4@1+ (1,0) [0|15] \"\" Vector__XXX\n"
    " SG_ Half m0 : 8|8@1+ (0.5,0) [0|127.5] \"\" Vector__XXX\n"
    " SG_ Other m1 : 8|8@1+ (1,0) [0|255] \"\" Vector__XXX\n"
    " SG_ Big : 16|17@1+ (0.12345678901234567890123456789012345678,0)"
    " [0|10000] \"\" Vector__XXX\n";

// The bytes of a frame payload.
static auto payload_of(std::initializer_list<std::uint8_t> bytes) -> FramePayload {
    FramePayload out;
    for (auto const byte : bytes)
        out.push_back(std::byte{byte});
    return out;
}

// Mode 0, Half 3/2, Big all ones over its low 16 bits.
static auto mixed_frame() -> FramePayload {
    return payload_of({0x00, 0x03, 0xFF, 0xFF, 0, 0, 0, 0});
}

// Speed 250 rpm and Temp 60 degC, then Speed 0: Temp holds, Speed under 100
// fails.
static auto first_frame() -> FramePayload {
    return payload_of({0xE8, 0x03, 100, 0, 0, 0, 0, 0});
}
static auto second_frame() -> FramePayload {
    return payload_of({0x00, 0x00, 100, 0, 0, 0, 0, 0});
}

// The standard identifier 256 and the eight-byte length.
static auto standard_256() -> CanId {
    return CanId{StandardId::create(256).value()};
}
static auto eight_bytes() -> Dlc {
    return Dlc::create(8).value();
}

// A corpus DBC's text.
static auto corpus_text(std::string_view name) -> std::string {
    return test::read_text_file(test::repo_root() / "python" / "tests" / "fixtures" / "dbc_corpus" /
                                (std::string{name} + ".dbc"));
}

// A reply, which the kernel writes as one JSON object, with every number
// kept exact.
static auto decoded(std::string const& raw) -> Json {
    auto reply = detail::parse_json(raw);
    INFO("a reply that is not one JSON object: " << raw);
    REQUIRE(reply.is_object());
    return reply;
}

// The kernel's reply to the JSON command `name` carrying `fields`.
static auto command(KernelSession const& session, std::string_view name, Json fields) -> Json {
    fields["type"] = "command";
    fields["command"] = std::string{name};
    return decoded(session.process(detail::dump_json(fields)));
}

// The kernel's parseDBCText reply for a DBC text.
static auto load(KernelSession const& session, std::string const& text) -> Json {
    return command(session, "parseDBCText", Json{{"text", text}});
}

// Holds that a reply's key holds the word given.
static auto require_word(Json const& reply, std::string_view key, std::string_view want) -> void {
    INFO("reply " << key << ", want \"" << want << "\": " << detail::dump_json(reply));
    auto const found = reply.find(key);
    REQUIRE(found != reply.end());
    REQUIRE(found->is_string());
    REQUIRE(found->get_ref<std::string const&>() == want);
}

// The DBC with a copy of its first message appended under another name,
// sharing its id.
static auto with_twin(Json const& dbc) -> Json {
    REQUIRE(dbc.is_object());
    auto out = dbc;
    auto& messages = out.at("messages");
    REQUIRE((messages.is_array() && !messages.empty()));
    auto copy = messages.at(0);
    copy["name"] = "Twin";
    messages.push_back(std::move(copy));
    return out;
}

using Replies = std::map<Case, Json>;

// Loads every corpus DBC and the variant with an unknown VAL_ target, then
// formats each back.
static auto load_replies(Replies& replies) -> void {
    std::map<std::string, std::string> texts;
    for (auto const name : corpus)
        texts.emplace(name, corpus_text(name));
    texts.emplace(unknown_target, corpus_text("value_tables") + "\nVAL_ 999 Ghost 0 \"Zero\" ;\n");
    for (auto const& [name, text] : texts) {
        KernelSession const session;
        replies.emplace(Case{.reader = Reader::ParseDbc, .fixture = name}, load(session, text));
        replies.emplace(Case{.reader = Reader::FormatDbc, .fixture = name},
                        decoded(required(session.backend().format_dbc_binary(session.state()))));
    }
}

// Formats and validates kitchen_sink's DBC and its twin-message variant.
static auto dbc_command_replies(Replies& replies) -> void {
    auto const& kitchen =
        replies.at(Case{.reader = Reader::ParseDbc, .fixture = std::string{kitchen_sink}})
            .at("dbc");
    auto const bodies = std::to_array<std::pair<std::string_view, Json>>({
        {kitchen_sink, kitchen},
        {twin, with_twin(kitchen)},
    });
    for (auto const& [name, body] : bodies) {
        KernelSession const session;
        replies.emplace(Case{.reader = Reader::FormatDbcText, .fixture = std::string{name}},
                        command(session, "formatDBCText", Json{{"dbc", body}}));
        replies.emplace(Case{.reader = Reader::ValidateDbc, .fixture = std::string{name}},
                        command(session, "validateDBC", Json{{"dbc", body}}));
    }
}

// Streams kitchen_sink under five properties: a batch on the first frame,
// then the end.
static auto stream_replies(Replies& replies) -> void {
    auto const above = [](std::string signal, std::int64_t value) {
        return ltl::eventually(
            ltl::atomic(GreaterThan{.signal = SignalName{std::move(signal)},
                                    .value = PhysicalValue{Rational::integer(value)}}));
    };
    auto const below = [](std::string signal, std::int64_t value) {
        return ltl::always(ltl::atomic(LessThan{.signal = SignalName{std::move(signal)},
                                                .value = PhysicalValue{Rational::integer(value)}}));
    };
    std::vector<LtlFormula> formulas;
    formulas.push_back(above("Temp", 0));
    formulas.push_back(below("Speed", 100));
    formulas.push_back(above("Pressure", 10));
    formulas.push_back(below("Pressure", 100));
    formulas.push_back(above("Speed", 5000));
    KernelSession const session;
    auto& backend = session.backend();
    auto const& state = session.state();
    require_word(load(session, corpus_text(kitchen_sink)), "status", "success");
    require_word(decoded(session.process(required(detail::serialize_set_properties(formulas)))),
                 "status", "success");
    static_cast<void>(required(backend.start_stream_binary(state)));
    auto const first = decoded(
        required(backend.send_frame_binary(state, Timestamp{1000}, standard_256(), eight_bytes(),
                                           first_frame(), std::nullopt, std::nullopt)));
    require_word(first, "type", "property_batch");
    static_cast<void>(decoded(
        required(backend.send_frame_binary(state, Timestamp{2000}, standard_256(), eight_bytes(),
                                           second_frame(), std::nullopt, std::nullopt))));
    replies.emplace(Case{.reader = Reader::Frame, .fixture = std::string{five_properties}}, first);
    replies.emplace(Case{.reader = Reader::EndStream, .fixture = std::string{five_properties}},
                    decoded(required(backend.end_stream_binary(state))));
}

// Extracts message 256 of the mixed DBC through the JSON-answering entry.
static auto extraction_reply(Replies& replies) -> void {
    KernelSession const session;
    require_word(load(session, std::string{mixed_text}), "status", "success");
    replies.emplace(Case{.reader = Reader::Extraction, .fixture = std::string{mixed}},
                    decoded(required(session.backend().extract_signals_binary(
                        session.state(), standard_256(), eight_bytes(), mixed_frame()))));
}

// Refuses the four kitchen_sink variants, each with the code its fixture
// names.
static auto envelope_replies(Replies& replies) -> void {
    auto const base = corpus_text(kitchen_sink);
    for (auto const& envelope : envelopes()) {
        KernelSession const session;
        auto reply = load(session, envelope.text(base));
        require_word(reply, "code", envelope.code);
        replies.emplace(Case{.reader = Reader::Envelope, .fixture = std::string{envelope.fixture}},
                        std::move(reply));
    }
}

// Every case's reply, answered by the real kernel.
static auto kernel_replies() -> Replies {
    Replies replies;
    load_replies(replies);
    dbc_command_replies(replies);
    stream_replies(replies);
    extraction_reply(replies);
    envelope_replies(replies);
    auto const all = cases();
    for (auto const& c : all) {
        INFO("no reply for " << reader_name(c.reader) << " on " << c.fixture);
        REQUIRE(replies.contains(c));
    }
    REQUIRE(replies.size() == all.size());
    return replies;
}

namespace {

// How a place is broken: its key deleted, its value or an array's entry
// replaced by another kind.
enum class Breakage : std::uint8_t { Deleted, Retyped, EntryRetyped };

} // namespace

static auto breakage_name(Breakage breakage) -> std::string_view {
    switch (breakage) {
    case Breakage::Deleted:
        return "deleted";
    case Breakage::Retyped:
        return "retyped";
    case Breakage::EntryRetyped:
        return "entry retyped";
    }
    return "unnamed breakage";
}

// One step from a value to one inside it: an object's key or an array's
// position.
using Step = std::variant<std::string, std::size_t>;

namespace {

// One broken copy: the place, as a refusal names it, the value's steps from
// the root, how it is broken and what replaces it.
struct Break {
    std::string path;
    std::vector<Step> where;
    Breakage breakage;
    Json replacement;
};

} // namespace

// Whether a value is the kernel's {numerator, denominator} object, a leaf of
// the reply proof.
static auto is_wire_rational(Json const& value) -> bool {
    return value.is_object() && value.size() == 2 && value.contains("numerator") &&
           value.contains("denominator");
}

// A value's replacements: "x" for a number, 0 for the rest, both for a
// rational. A negative number past -2^127 is held as a binary node.
static auto stand_ins(Json const& value) -> std::vector<Json> {
    if (is_wire_rational(value))
        return {Json(0U), Json("x")};
    if (value.is_number() || value.is_binary())
        return {Json("x")};
    return {Json(0U)};
}

// Adds a break of every place below `value` to `out`: each key deleted and
// retyped, each entry retyped, keys in their sorted order.
static auto add_breaks(Json const& value, std::string const& path, std::vector<Step> const& where,
                       std::vector<Break>& out) -> void {
    if (value.is_object() && !is_wire_rational(value)) {
        for (auto const& [key, inner] : value.get_ref<Json::object_t const&>()) {
            auto const here = path.empty() ? key : std::format("{}/{}", path, key);
            auto steps = where;
            steps.emplace_back(key);
            out.push_back({.path = here,
                           .where = steps,
                           .breakage = Breakage::Deleted,
                           .replacement = Json{}});
            for (auto& stand_in : stand_ins(inner))
                out.push_back({.path = here,
                               .where = steps,
                               .breakage = Breakage::Retyped,
                               .replacement = std::move(stand_in)});
            add_breaks(inner, here, steps, out);
        }
    } else if (value.is_array()) {
        for (auto const& [index, entry] :
             std::views::enumerate(value.get_ref<Json::array_t const&>())) {
            auto steps = where;
            steps.emplace_back(static_cast<std::size_t>(index));
            for (auto& stand_in : stand_ins(entry))
                out.push_back({.path = path,
                               .where = steps,
                               .breakage = Breakage::EntryRetyped,
                               .replacement = std::move(stand_in)});
            add_breaks(entry, path, steps, out);
        }
    }
}

// Every break of a reply.
static auto breaks_of(Json const& reply) -> std::vector<Break> {
    std::vector<Break> out;
    add_breaks(reply, "", {}, out);
    return out;
}

// The value at one step inside `value`.
static auto inside(Json& value, Step const& step) -> Json& {
    if (auto const* const key = std::get_if<std::string>(&step))
        return value.at(*key);
    return value.at(std::get<std::size_t>(step));
}

// `reply` with the place `change` names broken as it says.
static auto broken_copy(Json const& reply, Break const& change) -> Json {
    auto out = reply;
    auto* place = &out;
    for (auto const& step : change.where | std::views::take(change.where.size() - 1))
        place = &inside(*place, step);
    auto const& last = change.where.back();
    auto const* const key = std::get_if<std::string>(&last);
    if (key != nullptr && change.breakage == Breakage::Deleted)
        place->erase(*key);
    else
        inside(*place, last) = change.replacement;
    return out;
}

// What came at the broken place: nothing for a deleted key, else its kind.
static auto arrival(Break const& change) -> std::string_view {
    if (change.breakage == Breakage::Deleted)
        return "nothing";
    return change.replacement.is_string() ? "string" : "number";
}

// A value's steps spelled as dbc.messages[0].signals[1].factor.
static auto spelled(std::vector<Step> const& where) -> std::string {
    std::string out;
    for (auto const& step : where) {
        if (auto const* const key = std::get_if<std::string>(&step))
            out += (out.empty() ? "" : ".") + *key;
        else
            out += std::format("[{}]", std::get<std::size_t>(step));
    }
    return out;
}

// The error the reader of the case's reply answers for `raw`, nullopt for an
// acceptance: the reader the client applies to the command's answer, an error
// envelope read by the one the refused load's answer takes.
static auto read_broken(Reader reader, std::string const& raw) -> std::optional<AletheiaError> {
    auto const error_of = [](auto const& result) -> std::optional<AletheiaError> {
        if (result.has_value())
            return std::nullopt;
        return result.error();
    };
    switch (reader) {
    case Reader::ParseDbc:
    case Reader::Envelope:
        return error_of(detail::parse_parsed_dbc(raw));
    case Reader::FormatDbc:
        return error_of(detail::parse_dbc_response(raw));
    case Reader::FormatDbcText:
        return error_of(detail::parse_dbc_text_response(raw));
    case Reader::ValidateDbc:
        return error_of(detail::parse_validation(raw));
    case Reader::Frame:
        return error_of(detail::parse_frame_response(raw));
    case Reader::EndStream:
        return error_of(detail::parse_stream_result(raw));
    case Reader::Extraction:
        return error_of(detail::parse_extraction(raw));
    }
    return AletheiaError{ErrorKind::Validation, "no reader named"};
}

// How the case's reader took a broken copy: empty for an acceptance or the
// one form naming the broken place. An error envelope's reader accepts by
// answering the error the envelope carries.
static auto verdict(Reader reader, Break const& change, std::string const& raw) -> std::string {
    std::optional<AletheiaError> error;
    try {
        error = read_broken(reader, raw);
    } catch (std::exception const& e) {
        return std::format("threw {}", e.what());
    }
    if (!error)
        return {};
    if (error->kind() == ErrorKind::Protocol && error->code() == ErrorCode::Unknown) {
        auto const text = std::string{error->message()};
        if (text.starts_with(std::format("reply {}: expected ", change.path)) &&
            text.ends_with(std::format(", got {}", arrival(change))))
            return {};
        return std::format("refused as \"{}\"", text);
    }
    if (reader == Reader::Envelope)
        return {};
    return std::format("answered kind {}: {}", static_cast<int>(error->kind()), error->text());
}

namespace {

// A broken place a reader neither accepted nor refused in the one form.
struct Failure {
    std::string path;
    Breakage breakage;
    std::string verdict;

    auto operator<=>(Failure const&) const = default;
};

// Where a failure was first met, and how many broken copies it covers.
struct Seen {
    std::string first;
    std::size_t copies = 0;
};

} // namespace

// The broken copies of the case's reply its reader took out of the one form,
// one line for each path, breakage and verdict.
static auto out_of_form(Case const& c, Json const& reply) -> std::vector<std::string> {
    std::vector<Failure> order;
    std::map<Failure, Seen> seen;
    for (auto const& change : breaks_of(reply)) {
        auto said = verdict(c.reader, change, detail::dump_json(broken_copy(reply, change)));
        if (said.empty())
            continue;
        auto failure =
            Failure{.path = change.path, .breakage = change.breakage, .verdict = std::move(said)};
        auto const [at, fresh] = seen.try_emplace(failure, Seen{.first = spelled(change.where)});
        if (fresh)
            order.push_back(std::move(failure));
        ++at->second.copies;
    }
    std::vector<std::string> lines;
    for (auto const& failure : order) {
        auto const& where = seen.at(failure);
        lines.push_back(std::format("{} {} (at {}, x{}): {}", failure.path,
                                    breakage_name(failure.breakage), where.first, where.copies,
                                    failure.verdict));
    }
    return lines;
}

// The lines, one to a row.
static auto joined(std::vector<std::string> const& lines) -> std::string {
    std::string out;
    for (auto const& line : lines)
        out += "\n" + line;
    return out;
}

// The reply proof's table names and the paths each holds, read from its
// replyRange, replyText and replyNonEmpty clauses: a table, then its path as
// keys before [].
static auto proof_paths() -> std::map<std::string, std::set<std::string>> {
    // The cons of an Agda list, U+2237.
    constexpr std::string_view cons = "∷";
    static std::regex const clause{std::format(
        R"re(^(replyRange|replyText|replyNonEmpty) \(((?:"[^"]*" {} )+)\[\]\))re", cons)};
    static std::regex const clause_start{R"re(^(?:replyRange|replyText|replyNonEmpty) \()re"};
    static std::regex const key{R"re("([^"]*)")re"};
    std::map<std::string, std::set<std::string>> tables;
    std::istringstream source{test::read_text_file(test::repo_root() / "src" / "Aletheia" /
                                                   "Protocol" / "ReplyRange.agda")};
    for (std::string line; std::getline(source, line);) {
        if (!std::regex_search(line, clause_start))
            continue;
        std::smatch match;
        INFO("a clause the test cannot read: " << line);
        REQUIRE(std::regex_search(line, match, clause));
        auto const keys = match.str(2);
        std::string path;
        for (auto const& found : std::ranges::subrange(
                 std::sregex_iterator(keys.begin(), keys.end(), key), std::sregex_iterator{}))
            path += (path.empty() ? "" : "/") + found.str(1);
        tables[match.str(1)].insert(path);
    }
    return tables;
}

// A reader accepts each broken place of a real reply or refuses it as
// "reply <path>: expected ..., got ..." naming the place.
TEST_CASE("a broken reply place is accepted or refused in the one form",
          "[integration][reply_shape]") {
    auto const replies = kernel_replies();
    for (auto const& c : cases()) {
        auto const lines = out_of_form(c, replies.at(c));
        INFO(reader_name(c.reader) << " on " << c.fixture << ": " << lines.size()
                                   << " broken places out of the one form" << joined(lines));
        CHECK(lines.empty());
    }
}

// Each path of the reply proof's three tables is broken in some case's reply.
TEST_CASE("every place the reply proof names is broken by some case",
          "[integration][reply_shape]") {
    auto const tables = proof_paths();
    auto const names = tables | std::views::keys | std::ranges::to<std::vector<std::string>>();
    REQUIRE(names == std::vector<std::string>{"replyNonEmpty", "replyRange", "replyText"});
    auto const replies = kernel_replies();
    std::set<std::string> broken;
    for (auto const& c : cases())
        for (auto const& change : breaks_of(replies.at(c)))
            broken.insert(change.path);
    for (auto const& [table, paths] : tables) {
        std::vector<std::string> unbroken;
        std::ranges::copy_if(paths, std::back_inserter(unbroken),
                             [&broken](std::string const& path) { return !broken.contains(path); });
        INFO(table << " paths no case breaks:" << joined(unbroken));
        CHECK(unbroken.empty());
    }
}
