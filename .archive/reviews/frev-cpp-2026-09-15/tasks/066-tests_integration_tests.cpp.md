# Task 066: file review of `cpp/tests/integration_tests.cpp`

- status: completed
- file: `cpp/tests/integration_tests.cpp`
- round base: 726198bb (2026-09-15)
- pass: full (no earlier round under this contract covers this directory, so there is no previous diff to read first)
- pushed-in findings: clang-tidy lens over tests at round base reports 155 unique diagnostics in this file (the CI tidy gate excludes tests; details in base/clang_tidy_tests.txt); each is a candidate for points 2 and 3, checked against the file, never a verdict

## Report

Full pass. Fix in refs/frev/066 (signed later by the dribble).

Claims and guards: this is the binding's largest suite and its claims are its assertions, each read against what it names. The ones that carried a citation were checked against the cited source: the timestamp-monotonicity refusal is proven in the Agda module the comment now names; the payload guard the boundary cases exercise is one shared function in the FFI backend, not four inline comparisons; the acknowledgement wire the event tests pin is what the protocol module states; the geometry refusals each name a wire code the kernel emits. The binary extraction cases are the strongest guards in the file, crafting wire buffers by hand and pinning truncation, trailing bytes, a nonzero first offset, non-monotone offsets, a final offset that disagrees with the reason length, invalid encoding in a reason slice and a non-positive denominator, each as a Protocol error rather than a silent decode.

Findings fixed: (a) a helper that captures the process's error stream was dead, and the section comment above it described a test that captures the stream and reads the warning out of it, which no test does any more: the three tests read the recorded mismatch pair instead. The helper and the false description are gone, and with them four headers nothing else used. (b) Six citations pointed at line numbers in other files and every one had drifted: four claimed separate payload guards at four lines of the FFI backend, where one shared guard is called from four methods; one pointed into the JSON parser; one into the Go backend and one into the Python loader; and one into the protocol module. Each now names the thing rather than a number, which is the repository's own rule. (c) A comment cited an Agda file that does not state the property it cites; the property is in the Monotonic submodule. (d) Three comments dated the code: two section headings carrying a plan label and a date, one sentence saying what the verdicts collapsed to before that plan, and one calling a helper a wrapper that preserves an older signature. (e) One comment argued with itself in the source, reaching a conclusion, reversing it after the word "Wait" and ending on a verdict the test below it does not assert; it now states the reason the test's own verdict follows. (f) Three frames computed their raw value by dividing a physical value by the factor in double precision, in a binding whose whole contract is that no float appears on any surface; the raw values are written as the integers they are. (g) The library path from the environment was returned unchecked, so a stale value turned the skip this file's helper exists for into a mid-suite construction failure, the same defect the corpus parity suite carried.

```
REPORT 2026-09-15 tree b222b613 fix in refs/frev/066
claims: 9 rows, 0 without a guard: every row is asserted by a case, and the six that were cited wrongly now cite the thing rather than a line number
1 line per line: checked, all 2236 lines read
2 guidelines: checked; the delegating backend under test forwards every method deliberately, since the interface has no defaulted forwarding
3 modernize: checked, the doubles are gone from the frame construction and no behaviour moved: the raw values written are the ones the divisions produced, and the suite passes before and after
4 catalogue: checked, AGENTS/cpp.md category 14 (tests) and the float principle
5 value semantics: checked, payloads by value into the frame builders, definitions by value into the client
6 raii: checked, the only hand-managed resource in the file was the duplicated file descriptor in the dead helper, which is gone
7 dedup: checked; the per-test backend construction repeats but each case needs its own client, and the root discovery shared with two other files is the XREV item
8 ground truth: finding, six drifted line citations and one wrong module; checked true: the Agda property module, the payload guard's shape, the wire codes and the acknowledgement contract
9 history: finding, four datings and a plan label removed
10 simpler: checked
11 comments: 356 to 342, code 1580 to 1552
sweep: the mutation build folds this file into unit_tests, and it carries 4 mutants: cxx_lt_to_ge and cxx_lt_to_le at 400 and cxx_mul_to_div at 401 KILLED, and cxx_pre_inc_to_pre_dec at 400 a Timeout, which is how the sweep records a mutant that makes the byte-emitting loop run forever and is the status it carries in the base sweep too. Tidy over cpp/src 0 diagnostics, whole tree builds clean, ctest 15 of 15
probes: none name this file; store 47 run, 45 pass, 2 red on record
decision points: none new; the five approximate comparisons in this file are the callers the recorded to_double point names
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
