# Task 124: the benchmark sources are in no gate (ruled)

- status: done
- files: `cpp/benchmarks/benchmark.cpp`, `cpp/benchmarks/stability_bench.cpp`, `cpp/.clang-tidy`, the orchestrator, the coding standard, the probe store
- pass: full, across the directory
- origin: Ruled, after the measurement the ruling on the tests asked for. The tests and the benchmarks were counted apart; the tests are at zero and the benchmarks report 94 findings over two sources. Widen the gate to the benchmarks and fix the 94 the way the tests were fixed, so every C++ source the repository compiles is under one gate. A disable is written only where the reason is inherent to measurement code, carries the count it was measured at, and is held by the same two probes the tests' configuration is held by; everything else is fixed rather than suppressed, and no suppression comment is added. The gate invocation, the coverage guard, the coding standard's lint line and the teeth probe widen with it.

## Report

Every C++ source the repository compiles is now under one gate, and the benchmarks needed no configuration of their own. Fix in refs/frev/124.

Claims and guards. The benchmarks were the last C++ outside every gate: 94 findings over two sources, with nothing holding them. All 94 are fixed. No entry was written for measurement code, because none of the 94 turned out to be inherent to it: the reasons the tests' configuration carries are about Catch2's macros and a documentation harness, and a benchmark has neither. So the root configuration alone covers the benchmarks, which is the smallest outcome the ruling allowed and the one the measurement supports.

The substantial fixes. The argument vector was read as a raw pointer and is a span. Four payload fixtures were containers at namespace scope, so their constructors ran before main where a throw cannot be caught; they are function-local now. Eight helper structs had external linkage and are in anonymous namespaces. Three `using namespace` directives are gone, replaced by the twenty-six declarations the harness actually uses, which also says at the top of the file which part of the API a benchmark touches. Results discarded with a cast are bound instead. Three functions past the size threshold were split at their sweeps: the six throughput measurements, the property-count sweep and the scaling payload are their own functions now, and the file reads as an orchestrator over them.

One fix the tool offered was refused. `boost-use-ranges` rewrote a fold to `boost::accumulate` and added `<boost/range/numeric.hpp>` to a source that then could not compile, because the project does not depend on Boost. That check and `llvm-use-ranges` are disabled in the root configuration for naming libraries the tree does not have, with the incident as the stated reason; `modernize-use-ranges` stays and asks for the standard library's own algorithms, which is what the three sites use now.

A benchmark edit owes a measurement, not an argument. Run against the committed baseline the six throughput lanes all read 8 to 11 percent low, which would have been alarming read alone. Built from the pre-edit source on the same machine at the same time, they read 5 to 12 percent low against that same baseline, so the gap is the machine and not the change. Against that pre-edit run the six lanes move between -2.8 and +5.3 percent, three up and three down, which is the platform's own variance and not a direction.

```
REPORT 2026-09-15 tree refs/frev/end-ruling fix in refs/frev/124
claims: 1 row, 1 without a guard: that the lint gate covers the C++ the repository compiles, which was false of two sources and is now measured over all 47 translation units
1 line per line: checked, every site the gate reported was read, and the five extracted functions were read whole after extraction
2 guidelines: checked, the fixes are the guidelines the root configuration already enforces on the library
3 modernize: checked, no behaviour moved; the suites pass, the benchmark runs, and the A/B above bounds the effect on what it measures
4 catalogue: checked, that the two refused checks name libraries outside the tree is their own documentation, read before disabling them
5 value semantics: checked, the extracted sweeps return their row vectors by value and take the fixtures by reference
6 raii: n/a
7 dedup: checked, the extraction removed no duplicate because there was none; the six measurements were already one helper applied six times
8 ground truth: finding, a fix-it added a dependency the project does not have, which is a claim about the tree the tool could not check and the build refuted
9 history: checked
10 simpler: checked, the two entry points are thin and the sweeps are named
11 comments: 170 to 200 over the two sources, code 1254 to 1331; the growth is the reasons the refused fix and the function-local fixtures carry, in files this task fixed defects in
sweep: no mutation names these files; the mutation binary links the tests, not the benchmarks
probes: probes/cpp_.clang-tidy--the-gate-fails-on-a-discarded-return.sh gained a benchmark arm, red when a configuration under cpp/benchmarks hides the check; probes/lens_file_probe_map--recorded-row-reproduces.sh was rewritten after it went red on an unrelated edit, because comparing a live tree against a frozen row makes a probe that reports the tree moving rather than a defect, and it now checks the lens against a second reading of its own definition; store 77 run, 77 pass
decision points: none
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
