# Task 094: document review of `docs/reference/CPP_API.md` (follow-up from task 004)

- status: completed
- file: `docs/reference/CPP_API.md`
- round base: b222b613 (2026-09-15)
- pass: full
- origin: the streaming example fence (the one that parses an inline DBC text, adds a check and starts a stream) returns 0 when parse_dbc_text fails, so the doc-example harness reports it green although the kernel rejects that DBC text at line 2 (task 004 reproduced the rejection with the same text: "DBC text parse failed at line 2, column 1"). The example therefore demonstrates nothing past the backend construction. Every fence in this document, and by extension every fence the harness compiles from the other listed documents, is checked for the same shape: an error path that exits 0 hides a failing example from the harness.

## Report

Full pass, all nine points at all three granularities. Fix in refs/frev/094 (signed later by the dribble).

Correctness. The streaming example answered a failed call by returning zero, and the harness judges a fence by its exit code, so the example reported green while the kernel refused its DBC text at the second line. Reproduced with the same text through the command-line validator, which answers "DBC text parse failed at line 2, column 1". The text is missing the two sections the grammar requires before the node list, and adding the colon the node line also lacks does not fix it; the minimal text that parses carries an empty version, the two required section headers, the node list, the message and its signal, and that is the text the fence now holds, checked by running the validator over it. Each step now reports the kernel's own message and stops with a non-zero status, so the harness sees the failure. Teeth: with the corrected guard and the old text, the harness fails and prints the kernel's message.

The same shape was swept over every fence the harness compiles, in all six documents it lists. No other fence answers a failure by exiting zero, swallows an exception, or discards a client call's result. That sweep is now a probe, so a reintroduction anywhere in those documents is caught.

Two enumerations were sized from and were short. The predicate list named five of eight and the temporal-operator list four of nine, and a reader takes the parenthesis for the whole set; both are now complete, with the lifting step that a formula needs and the shorthand that takes a predicate directly both named. The error-kind list named four of eight behind an "and so on"; all eight are named. A third enumeration, the sentence counting four bindings, linked three guides and omitted the Go one.

Redundancy. The float principle was stated twice, generally and then as an instruction; the two are one sentence carrying the instruction. The pointer to the client header for exact signatures restated the opening blockquote, and the closing link list repeated the same claim a third time; both are gone. The See Also section stays: all six reference guides carry one, so cutting it here alone would break the shape a reader moves between them with.

Every paragraph and list item is now one line. Every link and anchor resolves, and each cross-document anchor was checked against the target's own headings rather than for the file existing.

Compression, measured. Prose words 637 to 675. The pass cut about thirty-five words of restatement and added about seventy of enumeration, which is the one growth the contract allows, since a partial enumeration read as a whole set is the defect. Lines 254 to 225, because the reflow joins wrapped prose.

```
REPORT 2026-09-15 tree refs/frev/098 fix in refs/frev/094
correctness: finding, the streaming fence hid a failing example behind a zero exit and carried a DBC text the kernel refuses; both fixed and the text checked by running the validator over it
redundancy: finding, the float principle stated twice and the headers-are-the-contract claim three times; one statement each
clarity: checked, the guard now names the step that failed
checkability: finding, three enumerations were partial and read as complete; all three counted from the source and widened
implementability: checked, every symbol named resolves in the public headers
precis: prose words 637 to 675, the growth entirely the widened enumerations, against about thirty-five words of restatement cut
one line per paragraph: finding, the whole document was wrapped; every paragraph and list item is now one line
proof-read: checked, the finished file read whole, not the diff
diagrams: n/a, the document embeds none
sweep: the doc-example harness passes over all six documents; with the old text and the new guard it fails, naming the kernel's refusal
probes: the new fence-shape probe passes, and read red with the zero exit restored
decision points: none
```

## Contract (carried whole)

## DREV: the document review contract

Each task names one document and reviews it against nine points.

- **Correctness**: check every claim against a probe or against the standard it cites. Verify it that way; the probe is saved to the store and cited in the report, and its path is never written into the document. A sentence nothing backs is a finding.
- **Redundancy**: remove what the document already says elsewhere. One statement, one place.
- **Clarity**: terse and precise prose, written for a human to read.
- **Checkability**: make interfaces and requirements explicit, so a reader can test whether an implementation meets them.
- **Implementability**: every interface and requirement corresponds to an element of the language, not to an intention.
- **Précis mais concis**: every pass makes the file shorter. A shorter document beats a longer one carrying the same decisions.
- **One line per paragraph**: reflow so that each paragraph and each list item is a single line, however long.
- **Proof-read**: read the finished file before declaring done. Not the diff, the file.
- **Diagrams**: every figure the document embeds is reviewed like a section.

### Three granularities, none skipped

The reading is done three times: sentence by sentence, then paragraph by paragraph, then section by section. At each one, ask the same four questions, is it accurate, is it readable, is it relevant, is it brief, because each granularity answers them about a different thing and a defect at one is invisible from the others.

A **sentence** is checked against the source it claims from: a `<` where the code says `<=`, an answer left behind when the question it answered was reworded, a term used before the document defines it, a name introduced with nothing said about what kind of thing it is, a count spelled as a word, a qualifier or pronoun a reader binds to the nearest noun rather than the intended one, a default described in words where a number sits behind it.

A **paragraph** is checked for having one subject: an identity welded to a status by "and", three ideas joined by a pivot that reads as a contradiction, a long aside inside a dash pair, a bare paragraph among bolded neighbours that everyone scanning will skip. A paragraph carrying a second bold lead mid-line, or one far longer than its neighbours, is split at the subject change with no word changed.

A **section** is checked for being one, and for earning its place: two subjects under one heading, topics alternating so the reader switches four times, a heading naming terms the section never defines, a whole section restating what three others already said, a section whose purpose turns out to be a change list rather than a statement of what is, a lead that contradicts the figure the same section embeds.

### A diagram is part of the document and is read at all three granularities

Every box, edge, label and annotation is a claim the document makes, and each is checked the way a sentence is.

- **Accurate**: check each element against the source, not against what the figure was drawn to say. An arrow at the wrong box, a state carrying a transition the code refuses, a label naming a field that has moved, an edge asserting a dependency the build does not have. A figure is the easiest place for a stale claim to survive, because nothing compiles it and prose review does not look at it.
- **Relevant**: the figure earns its place by carrying a claim the prose beside it strains to make. A picture restating one sentence is redundancy in another medium and is cut; two figures making one claim are one figure. A caption that opens on a topic label and then lists what the picture shows is the commonest figure defect; the caption states the claim.
- **Readable, which means rendering it and looking**: an SVG that parses is not an SVG that reads. Text overflowing its box, an arrow crossing a label, a line off the canvas, two annotations landing on each other: none of that is visible from the markup. Render every figure the pass touched and read the image at the width a reader sees it at.
- **A missing edge is a finding, and the answer is to draw it**: a state a reader can reach in the system and not in the figure is a claim the figure denies. Route the new edge around the outside so the drawing stays planar, put its label under its own arrow, then render and read it.
- **Clear**: the title states the claim rather than the topic, the alt text and the SVG's own `<title>` are that same text, and every term in the figure is one the document already defines. A caption rewritten without its `<title>` is a silent mismatch; move both in one edit and re-render.

### Everything is truth-grounded: the finding, the replacement, the report, the commit message

Nothing enters or leaves a pass on the strength of being plausible. A defect noticed is a candidate: run the probe, read the specification, grep the tree, compile the block. Measure every number reported, word counts and paragraph counts included, with the shell substituting the measurement rather than a number typed by hand; a relative position ("four lines down", "the row above") is a count too. And the text that replaces a finding is under the same rule, which is the half that gets skipped: every clause of the replacement is its own claim and owes its own source. Re-read the replacement against the source the finding came from, whole and never through `cut`, before the commit.

A citation finding is not written until the target's own lines are printed: never infer a target's contents from a lead enumeration, a heading, or a grep whose range was chosen by hand. And sweep every link's text, not only the anchors that fail: an anchor that resolves can still name the wrong document.

### A repeat pass on a document already reviewed skips nothing

The whole file is read again, at all three granularities, against all nine points. Prior verification expires, because every pass edits text that other sentences rest on, and because each granularity reads with a lens the last one did not. The first read of a repeat pass is the previous pass's own added lines, because that is where the findings are; where the tree moved by a code change, list what moved (headers per component, rosters, test paths) and grep every spelling of the old state corpus-wide, the code's own comments included, before reading any document.

### No step is optional, and the one that gets skipped is compression

Every pass runs all nine, on that pass, not "this pass found facts, the next one will compress". Deferring it is how the rule fails while appearing to be followed: each pass finds real defects, adds prose to fix them, puts compression off, and the file grows under a contract whose whole point is that it must not. Announcing the deferral in the report does not license it. If a pass genuinely finds no redundancy, say so having looked, with per-section word counts measured, rather than by not looking.

**What compression cuts:** restatement of a rule already decided elsewhere; rhetorical emphasis, which competes with itself once every paragraph shouts; rejected alternatives argued at length where a sentence carries them; a sentence that links the section owning a claim and then states the claim as well, where nothing after it draws on the restatement; and any history at all.

**What it never cuts:** a decision, a measurement, an interface, a refusal, or a restatement the paragraph's own conclusion rests on. A measurement survives; the probe path beside it does not belong in a design document.

**How to look for redundancy, because a literal sweep reports clean on a document that is not:** match on similarity rather than on exact n-grams, run it over sentences and over list items (recap-style duplication lives in short bullets), strip link targets before believing a similarity score, read the document's bolded assertions as an index to compare claim against claim, and where two documents carry one fact, read the two spellings side by side and ask which the source supports. A cut is owed a reason the item does not earn its place, not merely that the words appear twice.

**A cut can break a cross-reference somewhere else.** Two sections citing each other look like mutual restatement, and trimming one half leaves the other pointing at a claim the target no longer makes, silently, because the link still resolves. So the check is not that the target exists but that it carries the claim the citing sentence attributes to it: grep the target for the words, per reference, after compressing. A direction word ("above", "below") beside a same-document link is checked by comparing line numbers.

**How to compress safely: inventory first, verify after.** Extract every decision the document makes into a checklist before rewriting, then check the compressed text against it. A batched replace that matches nothing is a silent no-op, so verify each edit landed.

**An enumeration is sized from, so count the source.** A prose list naming five of a checker's refusals reads as the whole set; read the checker, count, and check every downstream sentence that quantifies over the list. A sentence that partitions a set has a third group; list the code's own members and subtract. Widening a partial enumeration is allowed to grow the file.

**A number a later edit moves is a number not to write.** Prefer the name over the count and the position: no numbered headings, no relative positions, no totals a later edit adds to. Where a count is the claim it stays and is measured; where it is navigation, name the thing.

### What the reflow leaves alone

Headings, tables, code blocks, and any blockquote whose line breaks are the content: a listing, a loop, a sequence of separate statements. A blockquote can hold both kinds at once, so join only the lines that are wrapped prose, by hand if the two cannot be told apart mechanically. A line-length check retires with the reflow, the two rules being opposites.

### What the proof-read is for

The edits themselves introduce defects none of the axes looks at: prose left arguing for a field the code block above it no longer has, a clause duplicated by a replacement that ran twice, a sentence a rewrite cut in half, a dash the pass wrote into a sentence it rewrote. Reading the finished text is the only thing that finds them, and the task's own rules list is read back against every touched line before the commit.

### Where the repository keeps sweeps and gates

Run every lens it offers at the base and at the run end (word counts per section, similarity, cross-document n-grams, history and judgement-word markers, cited paths and identifiers, contents lists slugged against headings both ways, captions in one grep) and diff the two, row by row rather than by total: a total that falls can still hide a new row. A pair of documents whose shared text rose is attributed gram by gram before being called a fix written twice. A set the review corrects by hand is one the next round corrects again; where the repository can gate a set or pin a fact to one owner, add the gate and stage it by breaking it. A second identical false-positive judgment is an exemption in the repository's exemption file, never an edit. A paragraph edited in two of the last three rounds is frozen, falsity re-opens it. Nothing a round adds may be text an earlier round removed; a hit is a decision point.

Commit messages are part of the record: written with a heredoc, never through a quoting route that eats apostrophes, with every number shell-substituted.

## Probes subsist, for all six

A probe run once at the terminal and thrown away proves something to one session and nothing to the next. Every probe a task runs, to prove a finding, to dismiss a candidate, to measure a number in a report or to check a claim, is saved to the repository's probe store: a tracked directory the repository names (look for `probes/`, `scripts/probes/`, `tools/probes/` or their equivalents before acting), and `probes/` at the repository root where it names none. A repository without a store gets one, with its runner, at the opening of its first round.

One probe is one file, runnable from the repository root with the repository's own toolchain, with no network, no path outside the tree and no dependence on the shell it was written in. It opens with a header stating the claim it checks, the file or document it probes, and what a non-zero exit means. It exits zero when the property holds and non-zero when the defect is present. A probe that measures asserts against the value recorded inside it, with the tolerance stated beside the value. It is named by the file it probes and the property, never by a round, a task id or a date. A probe that can flake is a finding on the probe, fixed before it enters the store.

The store has one runner, which runs every probe, prints one line per probe with its path and pass or fail, and exits non-zero on any failure; the runner's output is the record and is kept beside the round's own. The runner runs: at the opening of every round, over every probe of every word, before the first task; at round end, diffed line by line against the opening run; after every edit that lands, over every probe naming the file; and on demand at any time, which is the point of keeping them.

A probe that runs red after a change is a regression finding for the task that made the change, fixed before that task's commit. A probe red because the thing it probed was removed on purpose is retired by the same commit, with the reason in the commit message. A probe is never edited to pass.

A probe and a test are not the same thing, and one does not retire the other. The test is the guard the suite runs on every build; the probe is the review's instrument, and it stays after a test carries its claim, so a test later weakened or deleted is caught at the next opening. The dismissed candidate is the case only the store covers: a probe that proved a suspected defect absent has no test, and it is exactly what the next round must re-run rather than re-suspect. The report cites each probe by path; a document under DREV never does.

## Evidence, for all six

Every finding is proven by a probe or a failing-first test, never reasoned, and the probe is in the store or it is not evidence; documents, comments and prior claims are not evidence; the review is adversarial, so a quality that cannot be demonstrated is treated as absent. A fix the suite cannot fail is not a fix: mutate it away and confirm a test dies. No repo code, identifier or path leaves the machine. Nothing written names a review round, a decision point by number, an alternative by letter, or an entry of the working task list; commit bodies name no assistant or vendor, and the attribution trailers the repository's commit workflow prescribes (a co-author line and a session link) are kept; no em-dash anywhere.
