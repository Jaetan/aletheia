# Task 121: the test sources are outside the lint gate and five disables exist only for them (ruled)

- status: done
- files: `cpp/.clang-tidy`, a new configuration under `cpp/tests/`, the test sources, `AGENTS.md`, the orchestrator, the probe store
- pass: full, across the directory
- origin: Ruled: give the tests their own configuration and start linting them. The five disables in the root configuration produce zero findings over the library sources and every stated reason names test code, so they move to the tests' own configuration, which inherits the parent. The informational run counts tests and benchmarks together, so the two are separated before anything is decided about benchmarks. Every disable that stays in the tests' configuration carries its measured count and the reason it is inherent to test code; everything else is fixed rather than suppressed, and no suppression comment is added. The gate invocation widens, the coding standard's lint line and the orchestrator's step widen with it, and the teeth probe gains an arm that injects a violation into a test source.

## Report

The test tree is inside the lint gate and clean, and the five disables that only test code earned are in a configuration of its own. Fix in refs/frev/121.

Claims and guards. The root configuration disabled thirty-one checks, five of them with reasons that named test code. Re-enabled over the library those five report nothing; re-enabled over the tests they report 2018. That measurement is the whole finding, and it had no guard: nothing stopped a check disabled for the tests from hiding a library defect, and nothing stopped a disable outliving its cause. Both halves now have a probe.

The tests carry `cpp/tests/.clang-tidy`, inheriting the parent. It disables nine check names: three of the five that moved, and six the tests earn. Each carries the count measured with it enabled, and each reason names the construct that generates it rather than the inconvenience it causes. Two entries are worth naming. Cognitive complexity is a Catch2 artifact and not a long test: a case of five sections and eleven assertions, with no control flow its own author wrote, scores 77 against a threshold of 25, because the metric counts what the macros expand to. The optional-access check fires on the guarded pattern `REQUIRE(x.has_value())` followed by `x->field`, because the macro leaves the case by throwing and the check's flow analysis does not model it. The array-decay pair was in the first draft of this configuration and is not in the final one: after the sources were fixed it measured zero, so it no longer earned its place, which is the claim the second probe holds.

Everything else was fixed. Under the parent alone the tests reported 571 findings; with the child configuration 376 remained, and all 376 are gone. The substantial ones: sixty-six helper functions and variables moved out of anonymous namespaces, which is the convention the root configuration states and the library already follows, with types staying behind; sixty-one include repairs; the whole-file reader four executables had each written for themselves became one header; twenty-seven membership tests became `contains`; the discarded returns of sixteen setup calls became assertions, which is a stronger test rather than a quieter one; twenty-four bitwise operations on signed operands became unsigned; two `reinterpret_cast`s became a byte writer; a raw `execl` became `execv`; and four functions over the size threshold were split at their setup, three of them test cases whose fixtures are now named builders shared by the halves.

Three of those deserve their reason stated. The const-correctness fixes were applied by the tool and then read: four of them put `const` on an input stream that the next line writes through `rdbuf()`, which is a lie about a stream, so those four sites became the shared reader instead. The tool also writes `const` after the type; the tree writes it before, and the fifty-four insertions were moved to match. The include-cleaner fixes named `bits/chrono.h` and the C headers for the POSIX calls, so the ignore list gained the three patterns that keep a call site from having to name a standard library internal or a header the deprecated-headers check then rejects.

The gate itself moved in three places: the orchestrator step, the coverage guard, and the coding standard's lint line. The coverage guard matters most, because it is what makes a new test source fail CI rather than go unlinted, and it is now proven to do that. The four fuzz harnesses are the one part of the tree the widened step cannot reach, since they compile only under the fuzz configuration; they are clean under the same gate run against that tree, they have a configuration of their own for the three things libFuzzer's entry-point shape forces, and a probe holds them there.

Two probes went red on changes this task made and were fixed rather than edited to pass: the document-fence probe read a constant by a name the naming convention changed, and the staging check could not see a created file at all, because it diffed tracked paths against the base tree and a new file is in neither. That second one is the class of defect this round keeps finding: the check existed to catch an unstaged path and could not fail on the commonest kind. It now reads untracked paths against a recorded baseline, and both arms are proven red.

Rebuilding the mutation tree surfaced a flake in the probe that holds the mutation baseline. The sweep's score depends on an environment variable: with the library path exported, the integration suite's lookup returns before it reads the repository root, and that read's two mutants go uncovered. The probe inherited the caller's environment, so it was red for anyone who had sourced the environment script and green otherwise. It and the mutation runner now drop the variable, with the reason stated at both sites.

Rebuilding the mutation tree surfaced one more: the sanitizer ignorelist's comment described a vendored zip implementation that the bumped spreadsheet library no longer carries. Re-measured with the list withheld, two reports remain and both come from one file; the comment and the probe now name only that.

```
REPORT 2026-09-15 tree refs/frev/122 fix in refs/frev/121
claims: 5 rows, 5 without a guard: each of the five disables claimed a test-only cause, none was measured or held; two probes now hold the whole set, one that every disable is inert over the library and one that every disable still fires over the tests
1 line per line: checked, every test source the gate reported on was read at the site, and the four extracted functions were read whole after extraction
2 guidelines: checked, the anonymous-namespace move follows the convention the root configuration states, and the two checks that disagree about it now agree across the tree
3 modernize: checked, no behaviour moved; the suites pass deterministic and randomised, under both sanitizers, and the mutation sweep reads 62 killed of 62
4 catalogue: checked, that Catch2 registers a listener through an object of static storage duration and that its assertion macros expand to do-while are the library's own documented shapes, read in the vendored headers
5 value semantics: checked, the shared reader takes a path by reference and returns by value
6 raii: n/a, no resource changed hands
7 dedup: finding, the whole-file read was written four times and is written once; the Tier 2 fixture was written inside one test case and is now a builder two cases share
8 ground truth: finding, a comment described a temp-file helper that had moved to its own header, and the sanitizer ignorelist described a vendored file the bumped dependency no longer has
9 history: checked, the new header states what it is rather than what it replaced
10 simpler: checked, the long functions are shorter because their data moved out, not because their logic did
11 comments: 1921 to 2043 over the test sources, code 9174 to 9540; the growth is the reasons each disable carries and the comments the extracted builders needed, in files this task fixed defects in
sweep: 62 mutants, 62 KILLED, 0 survived, 0 timed out; the recorded baseline's timeout is gone and the record was corrected to the run
probes: probes/cpp_tests_.clang-tidy--every-disable-is-inert-over-the-library.sh, probes/cpp_tests_.clang-tidy--every-disable-earns-its-place.sh and probes/cpp_tests_fuzz_.clang-tidy--the-fuzz-harnesses-pass-the-gate.sh added, each proven red; probes/cpp_.clang-tidy--the-gate-fails-on-a-discarded-return.sh gained a test-source arm, red when the tests' configuration hides the check; probes/cpp_.clang-tidy--header-disable-list-matches-checks.sh and probes/review--every-changed-path-is-staged-by-the-snapshot.sh widened; probes/docs_reference_CPP_API.md--no-compiled-fence-hides-a-failure.sh and probes/cpp_sanitizer-ignorelist.txt--covers-the-vendored-tree-the-lane-compiles.sh re-grounded; probes/docs_MUTATION_BENCH.yaml--the-cpp-baseline-matches-a-run.sh no longer inherits the environment variable that changed its answer; store 76 run, 76 pass
decision points: two, recorded with the round
```

---

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
