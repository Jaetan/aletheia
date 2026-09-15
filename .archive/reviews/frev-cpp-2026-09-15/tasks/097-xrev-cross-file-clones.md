# Task 097: directory review of clones and inconsistencies spanning files (XREV follow-up, opened from task 010)

- status: pending
- directory: `cpp/`
- round base: b222b613 (2026-09-15)
- origin: per-file tasks push every clone that spans two files here rather than widening themselves. Items so far:
  - `us_per_millisecond` is defined in `include/aletheia/check.hpp` (namespace detail) and again in `src/enrich.cpp`, each with a comment naming the other binding's twin; one definition in the Timestamp vocabulary (types.hpp) would serve both, from task 010
  - strong-type coverage of the DBC vocabulary is uneven: `DbcMessage::sender` is a NodeName while `DbcMessage::senders`, `DbcSignal::receivers`, `DbcNode::name` and the node fields of the comment and attribute targets are plain strings; the message targets carry an `id` plus an `extended` flag where the rest of the API uses CanId. The wire shape mirrors the Agda constructors, so any change runs through json_parse.cpp, json_serialize.cpp and the tests together, from task 011
  - DbcDefinition mirrors the Agda DBC record field for field except one name: the record's `unresolvedValueDescs` is `unresolved_value_descriptions` in C++ (the parity probe from task 011 lists this as the one named exception); decide whether the C++ member follows the record and the wire, which touches json_parse.cpp, json_serialize.cpp and the tests, from task 011
  - the format_dbc_text contract (strict, provable re-parse, TextRoundtrip refusal, advisory wfTextIssues) is spelled twice in prose, on the method in `include/aletheia/client.hpp` and on DbcText in `include/aletheia/validation.hpp`; one owner and a pointer from the other, from task 024
  - the kernel library is discovered four times over: `src/rational_renderer.cpp` (variable, registered path, three relative candidates), `src/cli/cli.cpp` (variable, four candidates including /usr/local/lib), `benchmarks/benchmark.cpp` (variable, two candidates relative to the executable) and `benchmarks/stability_bench.cpp` (variable, one candidate); each with its own order and its own empty-variable rule until tasks 005 and 006 aligned two of them; one discovery function in the library, with the renderer's order as the reference, from task 029
  - the CLI exit codes are constants in `src/cli/cli.cpp` (three) and again in `src/cli/main.cpp` (the error code), while `include/aletheia/cli.hpp` states them in prose only; one set of named constants in the header would serve both files and the CLI tests, from task 030
  - little-endian integer readers exist twice: `src/client.cpp` (read_le over a byte span, since task 031) and `src/detail/loader_utils.cpp` (load_le16 and load_le32 over char pointers into a vector); one reader in a detail header would serve the binary extraction layout and the ZIP walker, from task 036
  - `enrich.cpp` wraps `detail::format_rational_ffi` as `format_value(const Rational&)` and `check.hpp` wraps the same call as `detail::fmt_pv(PhysicalValue)`; the two comments promise byte-identical output, which one shared function would make structural, from task 010
  - `[[nodiscard]]` is spelled per file and missed in seven of them: a sweep of every value-returning declaration under `cpp/include` at this task finds 27 without it, against the many that carry it. The list is candidates, not verdicts, and splits into groups that want different answers: the three backend factories in `backend.hpp`, where a discarded `make_ffi_backend` brings the one-shot GHC runtime up and then destroys the backend; the validated-newtype `create` and `make` constructors in `types.hpp` plus `Strong::of`, where a discarded `std::expected` is a validation nobody read; `from_decimal` in `types.hpp`, the only value-returning member of that header without it; the private helpers in `client.hpp`; the comparator and hash `operator()`s and the key accessors in `detail/cache_keys.hpp`; the three `visit` overloads in `ltl.hpp`; and the two chaining setters plus `always()` in `check.hpp`, where chaining is the normal use and the answer may be no. One rule for the directory, applied file by file, with the whole tree rebuilt to prove no caller discards what the rule newly marks, from tasks 047 and 049


## Report

(filled when the task is worked)

## Contract (carried whole)

## XREV: the directory review contract

The cross-file view, where FREV is the file-at-a-time one: a per-file pass cannot see a rule spelled once per file, an interface that is awkward only from a call site, or a shape three files share. Each task carries:

- design, interfaces, patterns, idioms, modernization
- idioms that apply to the directory's shape: a type the files could share, an interface a newer idiom removes the need for; from the repository's catalogue or from the net, searched as a pattern and never with repo code, identifiers or paths, and treated as a candidate to check against the tree
- value semantics across the directory's interfaces unless performance is paramount, and paramount means measured. Ask it of the call sites: a reference, a pointer or a borrowed view crossing a boundary earns its place with a number, and an owner passed by handle through three files is a lifetime nobody in those files can see
- RAII for resource management, and what the directory releases by hand that one class could hold: a descriptor, mapping, lock, table entry or registration released in several files is the dedup point reached through lifetimes rather than through text
- consistency and compatibility within the directory, usability
- ease of use at the call sites
- memory leaks, UBSan, ASan
- coverage against the repository's floors, per file
- everything checked against ground truth instead of assumed: a candidate is a finding when its probe runs red, the probe is saved to the store, and the rules under the probe section below bind every task
- dryness: remove duplicates, and remove similar code present in several files; state which files a finding covers, since the dedup half is the one that most often spans a task boundary

## Probes subsist, for all six

A probe run once at the terminal and thrown away proves something to one session and nothing to the next. Every probe a task runs, to prove a finding, to dismiss a candidate, to measure a number in a report or to check a claim, is saved to the repository's probe store: a tracked directory the repository names (look for `probes/`, `scripts/probes/`, `tools/probes/` or their equivalents before acting), and `probes/` at the repository root where it names none. A repository without a store gets one, with its runner, at the opening of its first round.

One probe is one file, runnable from the repository root with the repository's own toolchain, with no network, no path outside the tree and no dependence on the shell it was written in. It opens with a header stating the claim it checks, the file or document it probes, and what a non-zero exit means. It exits zero when the property holds and non-zero when the defect is present. A probe that measures asserts against the value recorded inside it, with the tolerance stated beside the value. It is named by the file it probes and the property, never by a round, a task id or a date. A probe that can flake is a finding on the probe, fixed before it enters the store.

The store has one runner, which runs every probe, prints one line per probe with its path and pass or fail, and exits non-zero on any failure; the runner's output is the record and is kept beside the round's own. The runner runs: at the opening of every round, over every probe of every word, before the first task; at round end, diffed line by line against the opening run; after every edit that lands, over every probe naming the file; and on demand at any time, which is the point of keeping them.

A probe that runs red after a change is a regression finding for the task that made the change, fixed before that task's commit. A probe red because the thing it probed was removed on purpose is retired by the same commit, with the reason in the commit message. A probe is never edited to pass.

A probe and a test are not the same thing, and one does not retire the other. The test is the guard the suite runs on every build; the probe is the review's instrument, and it stays after a test carries its claim, so a test later weakened or deleted is caught at the next opening. The dismissed candidate is the case only the store covers: a probe that proved a suspected defect absent has no test, and it is exactly what the next round must re-run rather than re-suspect. The report cites each probe by path; a document under DREV never does.

## Evidence, for all six

Every finding is proven by a probe or a failing-first test, never reasoned, and the probe is in the store or it is not evidence; documents, comments and prior claims are not evidence; the review is adversarial, so a quality that cannot be demonstrated is treated as absent. A fix the suite cannot fail is not a fix: mutate it away and confirm a test dies. No repo code, identifier or path leaves the machine. Nothing written names a review round, a decision point by number, an alternative by letter, or an entry of the working task list; commit bodies name no assistant or vendor, and the attribution trailers the repository's commit workflow prescribes (a co-author line and a session link) are kept; no em-dash anywhere.
