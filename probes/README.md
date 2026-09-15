# Probes

Each file here is one probe: a bash script that checks one property of one file or document, exits zero when the property holds and non-zero when the defect it was written to find is present. The header of every probe states the claim it checks, the file it probes, and what a non-zero exit means. Probes run from the repository root with the repository's own toolchain, without network access, and never depend on anything outside the tree.

Probes are the review's instruments, kept so a later change that breaks what an earlier review proved is caught when the whole store is re-run. They are distinct from tests: a test guards the suite on every build, a probe records what a review measured or dismissed, and one does not retire the other.

Run them all with `./probes/run_all.sh`, or any one of them the same way. The runner prints one line per probe and exits non-zero when any probe fails. Every probe states its own interpreter in a shebang and carries the exec bit, so none of them depends on the caller's shell being the one it was written for.

Two probes read state the review store keeps outside the tree, under `.git/frev/`: the list of paths a round has touched, and a baseline of what was already untracked when the round opened. The baseline is captured once, at round open and before the round creates anything, with `git ls-files --others --exclude-standard`, and an entry ending in `/` stands for every path beneath it, which is how a corpus a tool fills as it runs is recorded without listing each file. Without it the staging probe cannot tell a file the round forgot to stage from one that was already there, and it says so rather than passing.

A probe is named `<subject>--<property>.sh`, where the subject is the probed file's path with `/` replaced by `_`. A probe that fails after a change is a regression to fix before that change is committed. A probe whose subject was removed on purpose is retired in the same commit that removes the subject, with the reason in the commit message. A probe is never edited to pass.
