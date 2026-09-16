# Task 112: the backend interface passes a signal block as raw parallel pointers and the session state as an untyped pointer (ruled)

- status: completed
- files: `cpp/include/aletheia/backend.hpp` and every implementer and caller of the interface
- pass: full, across the directory
- origin: Ruled: land both typed shapes and take the break, with the four in-tree implementers updated. The injection block becomes three spans instead of a count and three raw pointers, so the type carries the equal-length invariant the comment states. The session state becomes a move-only handle that holds the close policy once, instead of an untyped pointer whose lifetime is spread across a destructor, a move that exchanges it and a close helper that swallows an exception. Two of the four implementers are tests. The feature matrix advertises this seam, so the change is breaking beyond the repository and owes a changelog entry. Re-run the mutation sweep: the mock is on the mutation surface. Grep the documentation guides for any fence that implements the interface, because the documentation-example harness compiles them.

## Report

Both typed shapes landed together, because both change the same signatures. Fix in refs/frev/112.

Claims and guards. The interface made two claims it could not keep. The injection block's three arrays "must all have length `count`", said in a comment and checked by nothing, with the count itself produced by a narrowing cast from a size. The state was an owning handle the caller "owns until it passes it to close", also said in a comment, with the owning spread across a destructor, a move that exchanged a pointer and a helper that swallowed. Both are now types.

The injection block is a class with three spans and a factory. `SignalInjection::create` refuses two shapes the boundary would otherwise read past: three arrays that are not the same length, and a length the wire's own 32-bit count cannot carry. The second was a live narrowing cast, not a hypothetical: the flattener cast a container size straight into the count. The client's resolver now returns a result rather than a block, and both call sites propagate the refusal instead of asserting it away.

The state is a move-only handle. `init` returns one, every other method takes it by const reference, and the release primitive moved behind the protected section with the handle as its only friend, so nothing in or out of the tree releases state by hand. The handle holds one release path that both its destructor and its move assignment use. Two orderings in the client are now load-bearing and both carry a comment where they are written: the handle is declared after the backend so it is destroyed first and closes through a backend still alive, and the move assignment assigns the handle before the backend for the same reason.

Four implementers, two of them tests, and one of those simplified rather than changed. The decorator in the integration suite used to forward `close` to its inner backend; the handle the inner backend hands out closes through that backend already, so the decorator now owns nothing. The two cancellation stubs shared one release definition instead of repeating an empty one each.

Guards, each proved by mutating the fix. Three sections cover the handle: a move transfers rather than closes, assigning over a client releases what it held exactly once, and self-assignment releases nothing. Three cover the factory's refusals. Removing the release call from the move assignment and disabling the length comparison kills four assertions across the two new cases, and restoring them brings both back. Six static assertions pin the shapes themselves: the handle is move-only with a non-throwing move, the block is trivially copyable and is neither default-constructible nor an aggregate, so no caller can route around the factory.

One finding outside the subject, carried to its own task. The format step lists its files from the binding directory, so two tracked C++ sources elsewhere in the tree have never been inside it, and both are unformatted. The round's claim that the gate covers every tracked source is true only of the directory it runs in.

```
REPORT 2026-09-15 tree refs/frev/111 fix in refs/frev/112
claims: 2 rows, 2 without a guard: the injection block's equal lengths and the state's single ownership, both now types with tests and static assertions
design and interfaces: finding, the two shapes named above are replaced; the wire under them is unchanged and the FFI still takes arrays and a count
value semantics: checked, three spans type a borrow that already existed at a boundary taking arrays, so nothing is copied that was not, and no number is owed; the handle is move-only by design because copying it would close twice
raii: finding, this is the whole task on the state side; the release that lived in three places at the call site lives in one destructor
consistency and compatibility: finding, breaking beyond the repository since the feature matrix advertises the seam, so the changelog carries it; every in-tree implementer is updated and one lost a method it never needed
ease of use at the call sites: checked, the client reads `if (!state_)` where it read a null comparison, and the two frame paths propagate a refusal they previously could not express
memory and sanitizers: checked, both sanitizer lanes are part of the gate audit this pass re-takes; the destruction order the handle depends on is asserted by the move tests as well
coverage: checked, the mutation sweep over the binding reports 62 mutants, 62 killed, no survivor
ground truth: finding, the two comments stating the invariants were the only thing holding them
dryness: checked, one release path replaces the client's own helper, and the cancellation stubs share one definition where each had its own
probes: probes/cpp_include_aletheia_backend.hpp--state-crosses-as-a-handle.sh added and red under three separate mutations of the header; probes/cpp_src_mock_backend.cpp--public-factory-answers-without-queueing.sh re-typed so it stays red for the defect it names rather than for a compile error; store 64 run, 62 pass, the two red-by-design
sweep: 62 mutants, 62 killed, no survivor, against 61 and one timeout at the round end
11 comments: 1120 to 1177, code 4015 to 4185 over the ten files; every file that gained comment lines is one this task fixed a defect in, and the two orderings that are now load-bearing are why the client's own count rose
decision points: none, the ruling this task carries out is already in the accumulator
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
