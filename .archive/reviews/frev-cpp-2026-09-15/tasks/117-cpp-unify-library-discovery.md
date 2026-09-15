# Task 117: the library is discovered four times over and the four orders disagree (ruled)

- status: pending
- files: the renderer, the command-line tool, the throughput benchmark and the stability benchmark, plus the probe store
- pass: full, across the directory
- origin: Ruled: unify on the renderer's order. That drops the system install directory from the command-line tool, which is user-visible, so the documentation naming that directory is corrected in the same task and the change owes a changelog entry. One property constrains the unification and is the reason the renderer consults the path the backend registered: the renderer and the backend must resolve to the same library, since a renderer that loaded a different build would format values through a different kernel than the one answering the queries. That property needs a guard that goes red if a caller bypasses the shared search. The probe that pins the four orders as differing until ruled is false by design once this lands: it is retired by the same commit with the reason in the message, never edited to pass, and replaced by one asserting the four callers share one order.

## Report

(to be written when the task is worked)

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
