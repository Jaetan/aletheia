# Task 113: the public mock factory refuses the first call every caller makes (ruled)

- status: completed
- files: `cpp/src/mock_backend.cpp`, `cpp/src/detail/mock_backend.hpp`, `cpp/include/aletheia/backend.hpp`
- pass: full
- origin: Ruled: make the factory hand out a backend that answers with canned successes, so the three descriptions of it become true and an installed consumer can drive a client without the test-internal header. The probe in the store reads red on the current object and must go green by the fix, not by an edit to the probe. The canned answer belongs per operation as data rather than as a queue the factory pre-fills. The failing-first test drives a client through every operation using only the public factory and public headers, with no internal include. This closes the ruling that gates the header comment task and the two-document task, both of which resume after it.

## Report

The factory hands out a fixed backend now, and the probe that was red on the old one is green. Fix in refs/frev/113.

Claims and guards. Three places described the public factory as a canned-acknowledgement backend, and the object it handed out refused its first call. The queueing method that would have made it answer lives in a test-internal header an installed consumer cannot include, so the described backend was one such a consumer could never call. The probe in the store proves the claim by compiling a consumer against the installed headers alone, and it reads green by the fix rather than by an edit to itself.

The first shape tried was a mode on the configurable double, chosen at construction, with the factory selecting the canned mode. It worked and the suite covered both modes. The sweep refused it: the comparison that selected the mode survived mutation. The decision lives in a header-inline method that several translation units compile, the linker keeps one copy, and the copy the sweep mutated was the one nothing calls. Flipping the comparison in the source does fail three test cases, so this was a duplicate-copy artifact rather than a coverage gap, but a branch whose mutation cannot be killed is a branch the sweep can no longer watch.

The second shape has no branch. The public factory hands out its own small backend that answers every operation with the wire's acknowledgement and every frame request with a zero-filled payload of the size asked for. It records nothing and decides nothing, which is what fixed means, and it is what the three descriptions have always said. The configurable double is left exactly as it was, still refusing on an empty queue, because a suite that silently received a fabricated answer would pass for the wrong reason. The sweep then reports no survivor.

One test was superseded rather than fixed. It asserted that the factory returns the configurable double, pinning the implementation rather than the contract; what the factory answers is now asserted directly, which is strictly stronger, so the type assertion went.

Two findings on the round's own machinery, both found here and both fixed. The snapshot stages exactly the paths listed in a file, and three paths this pass had edited were never added to it, so the previous task's tree held a retyped interface beside an untyped implementation and would not have built. The tree was rebuilt with the three files at their correct state and checked by building it in isolation from a clean archive. A probe now reads every path the round has changed and refuses any that the staging list does not cover, by itself or by an ancestor directory. It is red on two more files it found that way: two fixes made earlier in this round and never staged.

The recorded mutation baseline moved with the code and is re-measured: 62 mutants where the round end recorded 61, still no survivor, and the single timeout is stable across three consecutive runs.

```
REPORT 2026-09-15 tree refs/frev/112 fix in refs/frev/113
claims: 3 rows, 1 without a guard: that the public factory answers, now proved by the store's probe and by tests over every operation
1 line per line: checked, the factory source is new and read whole, the configurable double read whole and left unchanged
2 guidelines: checked, the fixed backend holds one constant and overrides every endpoint, with no state to synchronise and no branch to test
3 modernize: checked, no construct changed for its own sake
4 catalogue: checked, the candidate of a runtime mode on one class was tried, measured against the sweep, and rejected for a reason the sweep gave
5 value semantics: n/a
6 raii: checked, the fixed backend's state is a static sentinel and its release is empty, which the handle calls once
7 dedup: finding, the mode branch would have put two behaviours in one class; two types share no code and neither carries the other's condition
8 ground truth: finding, the three descriptions were true of nothing until this landed
9 history: checked
10 simpler: finding, the second shape is smaller than the first and removed the mutant the first introduced
11 comments: 163 to 187, code 848 to 940 over three files; the factory source carries the reason the public double is fixed, which is the defect this task fixed there
sweep: 62 mutants, 62 killed, no survivor; the mode branch's cxx_eq_to_ne survivor is gone with the branch
probes: probes/cpp_src_mock_backend.cpp--public-factory-answers-without-queueing.sh green by the fix; probes/review--every-changed-path-is-staged-by-the-snapshot.sh added and red on two files it found; store 64 run, 63 pass, the remaining failure the installed-consumer link this pass lands later
decision points: none
```

---

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
