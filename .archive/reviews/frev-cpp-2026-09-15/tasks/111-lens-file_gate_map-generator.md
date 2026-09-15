# Task 111: the file-to-gate map has no saved generator

- status: completed
- files: `lens/`, `base/file_gate_map.tsv`, `end/file_gate_map.tsv`
- pass: write the generator, regenerate the base row from the base tree, make the two ends comparable
- origin: The round-end record states that the base map's generator was not kept under `lens/`, so its total of 10 cannot be reproduced and the two maps are not comparable row by row. A lens whose method is not saved is not a lens: it produces a number once and nothing can diff it. Write the generator under `lens/`, run it against the base tree taken from the round base commit, replace `base/file_gate_map.tsv` with its output, and re-run it over the worktree so `end/file_gate_map.tsv` comes from the same method. State in the report what the base total actually is once measured, rather than the number the unsaved run produced.

## Report

The lens now has a method, and the method is the lens. Fix in refs/frev/111.

Claims and guards. The round-end record claimed a file-to-gate map at both ends and a total at the base that no saved code produced. A number nothing can recompute is not a measurement, and the two maps had been built by different hands, so the rows were not comparable even where both files listed the same path. The claim now has a guard: a probe regenerates the base map from the base tree with the saved generator and diffs it against the recorded file, and it reads red when the record and the generator disagree.

The method, stated in the generator and reproducible from it. For every tracked file under the directory, three spellings are searched as literal strings across every other tracked file: the repository-relative path always, the include spelling for a header under an include root because C++ names a header that way and never by its repository path, and the bare file name only when no other tracked file in the repository shares it. The review's own archive and the probe store are excluded, the first because it names every file it reviews and the second because the file-to-probe map already covers it. A referring file counts as a gate when it is a workflow, a build-orchestration file, a tool, a test or a benchmark, wherever it lives.

Measured with that one method at both ends. The base tree carries 91 tracked files under the directory, 44 named by a gate and 12 named by nothing outside themselves. The worktree the round leaves carries 104, 43 named by a gate and 23 named by nothing. The thirteen new files are eleven fuzz seed inputs, which nothing names and nothing should, and the two shared test headers, both of which a gate names.

The row-by-row diff is the part a total hides, and it produced the one finding worth carrying. Three rows lost their gate: the foreign-function backend source, the JSON parser source and the logging test. In every case the referring line was a comment in another test naming the file, and the round deleted those comments as stale. No coverage moved. That is the lens's own limit and the generator now says so in its own words: naming is not coverage, a comment mention counts the same as an exercise, so a row that falls is attributed before it is called a loss.

One finding on the probe store itself, surfaced by running it. The em-dash probe scans every line the round added against the base tree and treats a line with no counterpart there as written by the round. A round's record also stores captured tool output verbatim, which the round did not write, and the linting capture under the end record quotes test sources that carry em-dashes of their own. The probe was reporting the tool's output as the round's prose. Fixed by scoping it: under a record's base and end directories only Markdown is prose and everything else is a capture. Teeth re-proved both ways, an em-dash injected into the end record's own summary is still caught, and the captures no longer fire.

```
REPORT 2026-09-15 tree refs/frev/111-open fix in refs/frev/111
claims: 2 rows, 2 without a guard: the base map's reproducibility, now probed; the em-dash rule's scope, now stated and re-probed
1 line per line: checked, the generator is new and read whole, and the em-dash probe was read whole before its scope was changed
2 guidelines: n/a, no C++ in this task
3 modernize: checked, the generator is Python and holds to the repository's tool style, no shebang, typed signatures, a module docstring that states the method
4 catalogue: checked, the candidate of matching a header by its include spelling rather than its repository path was tested against the tree and raised the gated count from 16 to 43, so it is the difference between a lens and a formality
5 value semantics: n/a
6 raii: n/a
7 dedup: checked, the file-to-probe map keeps its own generator and this one excludes the probe store rather than restating it
8 ground truth: finding, the recorded base total came from no saved method and is replaced by a measured one
9 history: checked, the generator describes what it does and carries no account of what it replaced
10 simpler: checked, three literal searches over the tracked set beat parsing includes, and the ambiguity rule is what keeps the bare name usable
11 comments: 0 to 17, code 0 to 156 across the two new files; the em-dash probe 10 to 13 comment and 40 to 50 code, which the scope fix earns
sweep: no mutation names these files
probes: probes/lens_file_gate_map--base-row-reproduces.sh added, probes/review--no-line-the-round-wrote-carries-an-em-dash.sh repaired; store 63 run, 61 pass, the two failures the red-by-design pair this pass lands
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
