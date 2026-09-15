# Task 048: file review of `cpp/src/rational_renderer.cpp`

- status: completed
- file: `cpp/src/rational_renderer.cpp`
- round base: 726198bb (2026-09-15)
- pass: full (no earlier round under this contract covers this directory, so there is no previous diff to read first)
- pushed-in findings: the file header says the renderer "throws (point 2) rather than self-initialising", a plan label the docs rule on plan labels in source forbids (from task 015)

## Report

Full pass. Fix in refs/frev/048 (signed later by the dribble).

Claims and guards: the renderer dlopens the library on first use and never initialises the GHC RTS, throwing while it is down (two cases in cpp/tests/rts_init_renderer_uninitialized_tests.cpp, one per entry point, each in its own process because the RTS is process-global); the library search order, ALETHEIA_LIB then a registered path then the loaded-image scan then the build-tree heuristics (probes/cpp_include_aletheia_detail_rational_renderer.hpp--library-search-order.sh); an interior NUL is a Validation fault (a case in cpp/tests/unit_tests_decimal.cpp); a null kernel return throws rather than fabricating a value (unreachable for a well-formed call, so the guard is the mutation at that comparison, KILLED); every render flows through the kernel with no local C++ fallback (cpp/src/enrich.cpp:27 holds the only formatter and it formats an already-rendered Rational). One claim had no guard and now has one, the order in which a runtime-down call and a malformed literal are refused, described under 3.

Findings fixed: (a) three plan labels reading "point 2" are gone, one in the file header and two on the RTS comments; (b) the two entry points carried the same five-step shape, load, refuse while the runtime is down, refuse a null return, own the returned string, copy it out, with the two refusal messages the only difference; they now share one `kernel_string` helper parameterised by those two messages, and the three comment blocks that each restated the vocal contract are one block. The fold's one risk was the refusal order: a naive fold lifts the interior-NUL check above the runtime gate, which would answer Validation where the runtime is down, while rust/src/backend.rs refuses a runtime-down parse before it constructs the CString. The check therefore sits inside the call, after the gate, and a new case in the uninitialised-runtime binary pins it; its teeth were proven by lifting the check out and reading the binary fail, then restoring it and reading it pass.

```
REPORT 2026-09-15 tree b222b613 fix in refs/frev/048
claims: 5 rows, 1 without a guard: test case "a runtime-down decimal parse answers on the runtime, not on the literal" added to cpp/tests/rts_init_renderer_uninitialized_tests.cpp, teeth proven by the naive fold
1 line per line: checked, all 219 lines read; the search order, the dlsym sequence, the once-flag and both entry points asked what they do and whether they need to
2 guidelines: checked, R.11 and R.20 hold (the dlopen handle is process-lifetime by design and the returned string is owned by a unique_ptr with the kernel's own deleter); the three reinterpret_casts are the dlsym boundary and keep their single-site suppressions
3 modernize: finding, the duplicated kernel-call shape is one template helper; the refusal order it could have moved is pinned by a new test that goes red under the naive fold
4 catalogue: checked, AGENTS/cpp.md category 13 (FFI lifecycle) is the category, and the RTS-first rule it states is what the new test pins
5 value semantics: checked, std::string_view in, std::string out, the state by reference because it is the process singleton
6 raii: checked, every kernel string is owned by a unique_ptr with the kernel's free function as its deleter, including through the fold
7 dedup: finding, two bodies became one helper and three comment blocks became one
8 ground truth: checked, format_value(const Rational&) resolves at cpp/src/enrich.cpp:27, and the null-return refusal is the same message in go/aletheia/renderer.go, go/aletheia/decimal.go and rust/src/backend.rs, so "as Go and Rust do" holds
9 history: checked, none; the three plan labels are the class of marker the repository bans and they are gone
10 simpler: checked, the helper is the simpler shape and nothing shorter preserves the two distinct messages
11 comments: 67 to 60, code 152 to 151
sweep: cxx_eq_to_ne at 132, cxx_ne_to_eq at 139, cxx_eq_to_ne at 146, 149, 152 and 191 KILLED; 7 mutants at base, 6 now, because the two null-return comparisons at the old 186 and 220 are one comparison at 191 after the fold. The one non-Killed mutant in the sweep is a Timeout at cpp/tests/integration_tests.cpp:400, which carries the same status in the base sweep and names another file
probes: search-order probe re-run green; store 46 run, 44 pass, 2 red on record (the installed-consumer loader and the public mock factory)
decision points: none
```

## Contract (carried whole)

## FREV: the file review contract

### The unit of review is the claim

Every guarantee the file states is a claim: a comment saying what a function refuses, holds or never does; a `[[nodiscard]]`; a `static_assert` and its message; an error enumerator; a documented row the file implements; an invariant a header spells. The task's required artifact is a table with one row per claim: the claim, and the guard that goes red without it (a test case, a mutation the repository's sweep names, a gate arm, a model-checker arm). A row whose guard column reads none is the finding, and the fix is the guard, a failing-first test and a sweep entry where the repository has one, never a sentence saying the claim is true.

### The eleven points, each answered in the report

1. Line per line: the whole file is read, whatever an earlier pass concluded, and each line is asked what it does and whether it needs to.
2. C++ Core Guidelines, C++23 best practices, idioms and patterns.
3. Modernize, idiom only: any change that could move behaviour needs a gate that goes red before it and green after. No `NOLINT` without a measured, single-site reason, no `#define`, no build-file edit to make a construct compile, `template <typename T>` and never `class`. A file that is not C++ (CMake, bash, YAML, Python, markdown) is brought to its own language's idiom under the same rule.
4. Idioms from a catalogue where the repository keeps one pinned to its toolchain; otherwise the net, searched for the pattern and never with repo code, identifiers or paths in the query. Each is a candidate checked against the file, never a verdict.
5. Value semantics unless performance is paramount, and paramount means measured: a reference, a pointer or a borrowed view earns its place with a number.
6. RAII for every resource: descriptor, mapping, lock, table entry, registration, handle. Every release outside a destructor is either a class's own release path or a finding, and the question is asked of the whole file rather than only of what already looks like a resource.
7. Dedup the code and the comments. A clone inside one file is that file's finding; one spanning files becomes an XREV task rather than widening this one.
8. Every comment against ground truth. An identifier, path or test name a comment cites that resolves nowhere is a finding before the file is read; a claim about behaviour is checked against the code and the tests, never against another comment.
9. No history: comments describe the current state, git holds the past.
10. A simpler, more performant or more idiomatic implementation that exists is used.
11. Precise, concise comments a reader with a short attention span can read, and the comment count is measured: see the next section.

### Compression has a number

The report states code lines and comment lines before and after. A task may not leave a file with more comment lines than it found unless the same task fixed a defect in that file. The round ends with the ratio table over the whole directory beside the table at its base.

### A comment block edited in two of the last three rounds is frozen

It is edited again only for falsity, with the source line that shows it false quoted in the commit; reading better is not a reason. The churn between rounds, each rewriting the last one's prose, is what this rule stops.

### Per task: the sweep, not the anchor check

After every edit that lands, run whatever the repository has that watches the file: the mutation sweep over every mutation naming the file, each of which must read KILLED; the model-checker gate where the file is one it compiles; a fresh configure where a member was renamed, a public header added or an include changed, because configure-time gates never run on an incremental build; and every probe in the store that names the file, since a probe is the one instrument that remembers what an earlier round proved. An anchor that still resolves is not a verdict: a reflowed line can leave the anchor resolving and the mutation equivalent, or the test no longer failing.

### Everything is truth-grounded: the claim, the finding, the replacement, the report, the commit message

Nothing enters or leaves a task on the strength of being plausible. A lens hit, a catalogue idiom, a guideline rule or a suspicion from reading is a candidate until a probe runs against the file: compile the block, run the test with the line mutated, run the sanitizer, read the standard or guideline the comment cites and print its clause, grep the tree for the identifier. A candidate the probe dismisses is recorded as dismissed with the probe, because the next round will suspect the same line. Measure every number in the report, code lines, comment lines, mutation identifiers and timings included, with the shell substituting the measurement rather than a number typed by hand.

The replacement is under the same rule, which is the half that gets skipped: every changed line of a fix is its own claim and owes its own guard, a test that fails without it or a probe that reads red without it, and a guard that cannot go red is not one. Re-read the replacement whole against the source the finding came from, never through `cut` or a diff hunk, before the commit. A guideline cited in a finding is cited by its number, with the clause printed, never from memory.

### Round start and round end

At round start, before the first task: the repository's gate audit over the component, its mutation sweep over the directory, the whole probe store, and every mechanical lens it offers over the directory, kept beside the round's record so the end of the round is diffed against it. At round end the same, plus a check that every completed task's report is in the shape below.

### The report shape

Every task ends with a report in this shape, in the task's own description, so "reviewed, no change" is auditable point by point. Each numbered line reads `checked` with the evidence, `n/a` with the reason, or `finding` with the commit.

```
REPORT <date> tree <commit> <commit of the fix | NO CHANGE>
claims: <rows> rows, <rows without a guard> without a guard: <what was added, or none>
1 line per line: ...
2 guidelines: ...
3 modernize: ...
4 catalogue: ...
5 value semantics: ...
6 raii: ...
7 dedup: ...
8 ground truth: ...
9 history: ...
10 simpler: ...
11 comments: <comment lines before> to <after>, code <before> to <after>
sweep: <mutation idents> KILLED | no mutation names this file
probes: <paths added> | <paths re-run, all green> | none
decision points: none | appended to the accumulator
```

### Repeat passes

The first read of every task is the previous round's own added lines to the file, `git diff <previous base>..<previous end> -- <file>`, because that is where the last rounds' findings were. A file untouched since the previous round over its directory, under the same contract, gets a lenses-and-diff pass: the lenses run, the diff since that round's end is read, and the file is read whole only where a lens fires or a neighbour's rename reaches it. Every other file gets the full pass, and the task says which of the two it is.

## Probes subsist, for all six

A probe run once at the terminal and thrown away proves something to one session and nothing to the next. Every probe a task runs, to prove a finding, to dismiss a candidate, to measure a number in a report or to check a claim, is saved to the repository's probe store: a tracked directory the repository names (look for `probes/`, `scripts/probes/`, `tools/probes/` or their equivalents before acting), and `probes/` at the repository root where it names none. A repository without a store gets one, with its runner, at the opening of its first round.

One probe is one file, runnable from the repository root with the repository's own toolchain, with no network, no path outside the tree and no dependence on the shell it was written in. It opens with a header stating the claim it checks, the file or document it probes, and what a non-zero exit means. It exits zero when the property holds and non-zero when the defect is present. A probe that measures asserts against the value recorded inside it, with the tolerance stated beside the value. It is named by the file it probes and the property, never by a round, a task id or a date. A probe that can flake is a finding on the probe, fixed before it enters the store.

The store has one runner, which runs every probe, prints one line per probe with its path and pass or fail, and exits non-zero on any failure; the runner's output is the record and is kept beside the round's own. The runner runs: at the opening of every round, over every probe of every word, before the first task; at round end, diffed line by line against the opening run; after every edit that lands, over every probe naming the file; and on demand at any time, which is the point of keeping them.

A probe that runs red after a change is a regression finding for the task that made the change, fixed before that task's commit. A probe red because the thing it probed was removed on purpose is retired by the same commit, with the reason in the commit message. A probe is never edited to pass.

A probe and a test are not the same thing, and one does not retire the other. The test is the guard the suite runs on every build; the probe is the review's instrument, and it stays after a test carries its claim, so a test later weakened or deleted is caught at the next opening. The dismissed candidate is the case only the store covers: a probe that proved a suspected defect absent has no test, and it is exactly what the next round must re-run rather than re-suspect. The report cites each probe by path; a document under DREV never does.

## Evidence, for all six

Every finding is proven by a probe or a failing-first test, never reasoned, and the probe is in the store or it is not evidence; documents, comments and prior claims are not evidence; the review is adversarial, so a quality that cannot be demonstrated is treated as absent. A fix the suite cannot fail is not a fix: mutate it away and confirm a test dies. No repo code, identifier or path leaves the machine. Nothing written names a review round, a decision point by number, an alternative by letter, or an entry of the working task list; commit bodies name no assistant or vendor, and the attribution trailers the repository's commit workflow prescribes (a co-author line and a session link) are kept; no em-dash anywhere.
