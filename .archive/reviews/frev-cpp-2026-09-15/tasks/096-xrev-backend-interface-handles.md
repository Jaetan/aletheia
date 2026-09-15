# Task 096: directory review of the backend interface handles (XREV follow-up from task 009)

- status: completed
- directory: `cpp/` (the IBackend surface: `include/aletheia/backend.hpp`, `src/backend.cpp`, `src/ffi_backend.cpp`, `src/client.cpp`, `src/detail/mock_backend.hpp`, `src/mock_backend.cpp`, the tests that implement or call it)
- round base: b222b613 (2026-09-15)
- origin: SignalInjection carries a count and three raw parallel pointers whose equal length is stated in a comment only, where the catalogue asks for std::span over pointer-and-size pairs; and the backend state crosses the interface as void* (init returns it, process and close take it), a handle no type checks. Both shapes are shared by every backend and every caller, so a change is a directory-level interface change, not one file's. Design the end state (a span-based injection block, an opaque state type or an owning handle the client holds), measure the call sites, and either land it across the files or record why the current shape stays.

## Report

Directory pass over the backend interface. No change landed; both shapes are one ruling, appended to the accumulator with the measurement done.

What was measured. Four classes implement the interface in the tree, the production backend, the mock, and two test stubs, and the feature matrix presents the seam as available to an external consumer, so any signature change breaks beyond the repository. The injection block's equal-length invariant is already structural on the only production path, because the client's resolver holds three vectors and flattens them at the interface; the loose shape bites only where a caller builds a block by hand, which one test does, and where an external implementer reads one. The session state's lifetime is already handled, but by hand and in three places: a destructor, a move that exchanges the pointer, and a close helper that swallows an exception.

Why nothing landed. Both shapes appear in the same signatures, so they are one change, and that change is breaking against a seam the project advertises. The directory contract asks for the end state to be designed and the call sites measured, which is done, and for the change to land or the reason to be recorded. The reason is that the choice is between a break with a real gain in checkability and a header sentence that states what the producer already guarantees, and that is the user's to make rather than the review's.

```
REPORT 2026-09-15 tree refs/frev/097 NO CHANGE
claims: 2 rows, both appended as one ruling: the block's equal-length invariant, stated in a comment, and the state's ownership, spread over three places in one class
design and interfaces: finding, appended; the end state is described in the accumulator with both alternatives and their costs
idioms for the directory's shape: checked, the span-over-pointer-and-size idiom applies and is named in the ruling
value semantics: checked, the block is passed by value already and is four words; the state is a pointer the client owns
raii: finding, the state's lifetime is spelled in a destructor, a move and a close helper rather than held by a type; the cost of holding it is the coupling the ruling names
consistency and compatibility: checked, all four implementers take the same shapes, so the inconsistency is with the rest of the API rather than within the interface
ease of use at the call sites: finding, one test builds the block by hand with four named initialisers and nothing checks them against each other
memory and sanitizers: checked, no leak or lifetime fault found; the client's move leaves the source null and its destructor cannot throw
coverage: checked, the interface's every method is exercised by the mock-backed suites
ground truth: checked, the comment on the block is true today because of the producer, which is the fact that makes the ruling a choice rather than a fix
dryness: n/a, the shapes are declared once
11 comments: unchanged, no file edited
sweep: n/a, no change
probes: none added; the ruling's measurements are in the accumulator entry
decision points: 1 appended
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
