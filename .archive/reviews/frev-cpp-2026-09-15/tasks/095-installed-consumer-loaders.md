# Task 095: installed consumers and the loader dependencies (follow-up from task 007, gated by a ruling)

- status: completed
- worked to the ruling: the failure is reproduced and kept. The two probes in the store build an installed
  consumer and show the client-only program links while a program calling the YAML loader does not, with the
  undefined references named. The three alternatives and their costs are in the accumulator. Nothing here can be
  chosen by measurement: installing the dependency archives, building the library shared, and narrowing what the
  distribution guide promises are three different products.
- files: `cpp/CMakeLists.txt`, `cpp/cmake/aletheia-cpp-config.cmake.in`, `docs/development/DISTRIBUTION.md`
- round base: b222b613 (2026-09-15)
- pass: full on each file touched by the ruling
- origin: the installed-consumer probe for the package config template links a client-only program and fails to link one that calls the YAML loader (undefined references into yaml-cpp); the accumulator holds the alternatives. Work the ruling: install and export the dependency archives with find_dependency, or build the library shared, or document the restriction; then turn the red probe green (or retire it with the documented restriction, stating why in the commit).

## Report

The library is shared, an installed consumer links both loaders, and the probe that opened red at the start of the round is green. Fix in refs/frev/095.

Claims and guards. The distribution guide presents finding the package and linking it without restriction, and the installed archive could not honour that: its YAML and spreadsheet dependencies were linked privately behind a build-interface guard and neither installed nor exported, so the archive referenced symbols nothing supplied. A consumer could link a client-only program and nothing that called a loader. The probe was widened before the fix so both loaders are covered rather than only the YAML one, and it was red for both.

The shared library carries those dependencies inside it and publishes only this project's own symbols, which is why the ruling's shape works where installing the two archives would have exported someone else's build. The dependencies had to become position independent for that, set before they are made available because a target takes the value when it is created.

Three things broke, each a real consequence rather than a nuisance, and the third is the one that mattered.

The documentation-example harness compiled each fence against the library by path and ran it; a path satisfies the linker and not the loader, so every fence failed to start. The fences now carry the library's directory as a run-time search path, and they no longer link the two dependency archives at all, because the library carries them. That also answers, before it was asked, the harness change the dependency bump was expected to need.

Seventeen probes named the archive and the two dependency archives on their link lines. Each now links the one shared library with a run-time search path, and the archive lookups are gone. The whole store passes for the first time in this round.

The mutation lane collapsed, and silently. Built against the shared library the runner found 14 mutants where the same sources yield 62, and reported a hundred per cent over a quarter of the surface: a sweep that cannot see the code cannot fail on it, and nothing in its output said so. The lane links the library statically now, which is a link-time property no mutant can express, so it measures what it always did. A probe pins both the configuration and the count, with a floor below the recorded baseline, and reads red when the mutation branch is pointed back at the shared form.

One finding in a gate, found by running it. The licence-header check read every tracked path and crashed with a traceback on one whose file had been renamed but whose deletion was not yet staged. It now reports on what is there. The deletion is staged too, and the renamed probe is in the staging list.

```
REPORT 2026-09-15 tree refs/frev/117 fix in refs/frev/095
claims: 2 rows, 2 without a guard: that an installed consumer can use both loaders, and that the mutation lane sees the library; both now probed
1 line per line: checked, the library target, its install and export blocks, and the harness's compile and link command read whole
2 guidelines: n/a
3 modernize: checked, the link form is a build decision and the change is guarded by the suites, both sanitizer lanes and the fast tier rather than by inspection
4 catalogue: checked, the position-independent-code requirement for static dependencies of a shared library is the toolchain's rule, confirmed by building rather than by reading
5 value semantics: n/a
6 raii: n/a
7 dedup: finding, two compile definitions feeding the harness the dependency archives are gone, and seventeen probes lost the same pair of lookups
8 ground truth: finding, the distribution guide's find-and-link presentation was true only of a client-only consumer
9 history: checked
10 simpler: checked, a fence links one file where it linked three
11 comments: 366 to 389, code 956 to 963 over the three files; the added lines say why the mutation lane links differently and why a fence needs a search path, both of which cost a day to rediscover
sweep: 62 mutants, 62 killed, no survivor, measured after the lane was repaired; 14 before it, which is the finding
probes: probes/cpp_cmake_aletheia-cpp-config.cmake.in--installed-consumer-links-yaml-loader.sh renamed and widened to both loaders, red for both before the fix and green after; probes/cpp_CMakeLists.txt--the-mutation-lane-sees-the-whole-library.sh added and red when the lane is pointed back at the shared form; seventeen probes repointed at the shared library; store 70 run, 70 pass
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
