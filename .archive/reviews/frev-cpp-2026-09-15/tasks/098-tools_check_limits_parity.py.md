# Task 098: file review of `tools/check_limits_parity.py` (follow-up from task 019)

- status: completed
- file: `tools/check_limits_parity.py`
- round base: b222b613 (2026-09-15)
- pass: full
- origin: the tool's docstring says the C++ binding does not mirror the Agda limits and so gates only the Go and Python mirrors; cpp/include/aletheia/limits.hpp mirrors them verbatim by its own header, and at the round it was missing four bounds and one kind that nobody caught (task 019 added them and left a probe, probes/cpp_include_aletheia_limits.hpp--mirrors-agda-limits-verbatim.sh). Extend the gate to the C++ mirror so the three surfaces are held by one tool, and correct the docstring; the probe then either retires into the gate or stays as the review's instrument.

## Report

Full pass. Fix in refs/frev/098 (signed later by the dribble).

Claims and guards: the tool's own docstring made a claim about the tree, that the C++ binding holds no mirror of the bounds and consumes only the typed error the kernel returns. The C++ header opens by saying the opposite, that it is the mirror and the values are copied verbatim, and it carries all sixteen constants and all nine wire codes. Nothing held it to that. What a missing gate costs was measured earlier in this round: the mirror was short four bounds and one kind and nobody noticed.

Finding fixed: the gate reads the C++ header the way it already reads the other two and compares both halves. The comparison machinery was already per binding, so the change is a parser, two tables and two calls. Every C++ constant is marked required, because the header promises a verbatim copy of the whole set rather than of the four bounds the binding enforces itself, and a mirror that drops one stops being what it says it is. The message that names a missing required constant used to assert the bound is refused at that binding's language boundary, which is true of the other two and not of this one, so each binding now carries its own reason for the category.

Staged on four arms. Changing a C++ value, changing a C++ wire string, deleting a C++ constant and adding one with no Agda peer each make the gate exit non-zero with a message naming the C++ mirror; restoring the header returns it to zero.

The same false sentence lived in the build rule that invokes the gate, saying Python and C++ have no local mirror and are out of scope. Python had been in scope for some time. Both are now described as they are.

The probe drives the gate over a drifted C++ constant and restores the header in the same step that edits it. Deleting the new arm makes it read "a drifted C++ value was accepted". The mirror's own probe stays: it reads the two files directly and is the review's instrument, where the gate is the build's.

```
REPORT 2026-09-15 tree refs/frev/093 fix in refs/frev/098
claims: 2 rows, 1 without a guard: the C++ mirror's verbatim promise, now held by the gate and by the new probe
1 line per line: checked, the whole tool read, and the build rule that invokes it
2 guidelines: n/a, not C++
3 modernize: checked, the summary and the mirror list are built from the per-binding table rather than spelled three times
4 catalogue: checked, the value parser reuses the shared arithmetic evaluator, widened for the apostrophe digit separator and the integer suffix C++ writes
5 value semantics: checked
6 raii: n/a
7 dedup: checked, the third binding adds a parser and two tables and reuses both comparison routines unchanged
8 ground truth: finding, the docstring and the build rule both said the C++ binding holds no mirror, and the build rule said the same of Python, which the gate had covered for some time
9 history: checked, the revert note is stated as what breaks the gate rather than as something once verified
10 simpler: checked
11 comments: the tool 41 to 50, code 472 to 557; the build file 753 to 748, code 1378 to 1378
sweep: no mutation names either file; the eleven fast-tier steps pass, the gate runs green through the build file, ruff and pylint are clean and the type checker reports nothing
probes: the new gate probe passes and read red with the arm deleted; the mirror's own probe still passes
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
