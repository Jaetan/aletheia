# Task 097: directory review of clones and inconsistencies spanning files (XREV follow-up, opened from task 010)

- status: completed
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

  - the repository root is discovered two ways in the test tree: eight files read `ALETHEIA_REPO_ROOT`, which ctest sets per target through `set_tests_properties`, and three (`integration_tests.cpp`, `test_cross_binding_integration.cpp`, `dbc_corpus_parity_tests.cpp`) walk up from `__FILE__`, which bakes the build machine's source path into the binary and breaks when the tree is copied. One way for the directory, which for the three means a ctest ENVIRONMENT property each, from task 052

  - three test files now own a temp-path type each and a fourth removes by hand: `excel_tests.cpp` has `TempFile`, `cli_tests.cpp` a `TempDbc` that also writes the content, `doc_example_tests.cpp` a `ScratchDir` for a directory, and the fuzz and yaml suites write their own paths. One small owning type in a test header would serve all of them, and `test_helpers.hpp` is where the directory already puts shared test machinery, from tasks 051, 053 and 054

  - the fuzz build-and-run recipe is written twice, in the comment block above the fuzz section of `cpp/CMakeLists.txt` and in the header of `tests/fuzz/fuzz_parse_response.cpp`, which the other three harnesses point at as the owner; one owner and a pointer from the other, from task 058


## Report

Directory pass over twelve items pushed here by the per-file tasks. Nine are fixed, each in its own snapshot; three are rulings, each worked to the measurement and appended. Four follow-up tasks were opened by findings this pass turned up.

Fixed, one snapshot per finding.

The microsecond scale factor was defined twice and now sits once beside the Timestamp alias it scales into, in refs/frev/097a. The two wrappers that turn a Rational into text, each promising the other's output was byte-identical, are one shared function in refs/frev/097b. The CLI's three exit codes, spelled as constants in two files and as prose in the public header, are named constants in that header in refs/frev/097d, with the tests keeping their numeric literals so the constants have teeth from outside. The format_dbc_text strictness contract, written on the method and again on the struct it returns, has one owner in refs/frev/097e. The fuzz build-and-run recipe, written in the build file and in the harness the other three point at, has one owner in refs/frev/097f, and running it showed neither copy worked. The discard rule for the public headers is settled in refs/frev/097g: twenty-one declarations get the attribute, five do not, and the split is argued per group. The three scratch-path types are one in refs/frev/097h, which also fixed a destructor that removed its file through the throwing overloads. The two ways a test found the repository are one in refs/frev/097i, which also gave the mutation runner the variable its folded-in integration tests need.

Dismissed, with the reason recorded. The two multi-byte integer readers looked like a clone and are not: the binary extraction layout carries the host's byte order, which the kernel documents, and the ZIP records are little-endian whatever the host is. Merging them would be correct only under the assertion that forbids a big-endian build. The reader that read native order while being called read_le is renamed in refs/frev/097c, and a probe records the dismissal so a later round re-runs it rather than re-suspecting the clone.

Appended to the accumulator, each worked to the point the ruling gates: the four library searches, with a probe pinning how the four orders differ and the one property any unification must not break; the uneven strong-type coverage of the DBC vocabulary, with every field read; and the one member name that departs from the record and the wire, which the parity probe already carries as its single exception.

Opened as tasks: 107, because the feature-matrix gate read a C++ digit separator as a character literal and blanked live declarations out of its own search, found by adding one constant here; 108, the round's own em-dashes, twenty-nine lines measured against the tree the round started from; 109, because the build file's five recipes disagreed about the directory they are run from, found by running one of them; and 110, because the clang-tidy gate reads clean when run from a directory with no configuration in scope, which is how this round had been running it.

```
REPORT 2026-09-15 tree refs/frev/107 fixes in refs/frev/097a through refs/frev/097i
claims: 12 rows, 9 fixed with a guard each, 3 appended as rulings
design and interfaces: checked, the three shared types added (a scale factor, a scratch path, a repository root) each replace a per-file copy and none widens a public surface
idioms for the directory's shape: checked, the discard rule is now one rule applied per group rather than per file
value semantics: checked, the shared readers take their argument by value or const reference and return by value
raii: finding, three scratch-path types with three lifetimes became one that cannot throw from its destructor
consistency and compatibility: finding, the exit codes, the format contract and the fuzz recipe each had two spellings and now have one owner
ease of use at the call sites: checked, the temp-path and repository-root headers are light enough for every suite that needed them, which test_helpers.hpp was not
memory and sanitizers: n/a this pass, no allocation or lifetime changed except the scratch-path destructor, which now cannot throw
coverage: checked, every fix carries a guard that was read red, and the two that could not have one (a dismissed candidate, a directory convention) carry probes instead
ground truth: finding, four claims in comments were false and are corrected; one suspected clone was refuted by the kernel's own documentation
dryness: 9 duplications removed, each named above with the files it spanned
11 comments: 1885 to 1911, code 6917 to 6949 over the 27 files this pass touched
sweep: 61 mutations over the mutation binary, 60 KILLED and the one long-standing timeout in a test loop counter; fifteen suites green; eleven fast-tier steps green; the tidy gate clean over cpp/src, run from the directory task 110 established it must run from
probes: 8 added this pass, each read red before its fix or with its subject reverted
decision points: 3 appended
```

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
