#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes probes/run_all.sh.
# Claim: a passing probe prints one line however much it says, and a failing
# probe's line carries its exit status and is followed by its own output, the
# last lines inline and the whole of it in a file the line names, so a probe
# that crashed reads differently from one that refused its claim. The record
# directory holds only the latest run's failures, and the runner still exits
# non-zero and counts every probe. A probe that writes a tracked file and puts
# its bytes back, exiting zero, fails all the same, its line counting the
# files it moved and its log naming them, because the runner reads every
# tracked file's mtime, size and mode before and after each probe; and a store
# with no git work tree around it is refused rather than run unwatched.
# Non-zero exit: a failure's reason is lost, a passing probe's chatter reaches
# the record, a stale failure survives a run, the runner no longer reports the
# failure, a restored write passes, or a store outside git runs.
set -u
cd "$(dirname "$0")/.." || exit 2
command -v python3 > /dev/null || { echo "python3 is needed to stage a crashing probe"; exit 2; }
work=$(mktemp -d) || exit 2
trap 'rm -rf "$work"' EXIT
mkdir -p "$work/probes" "$work/tools/ci-output/probes" || exit 2
cp probes/run_all.sh "$work/probes/run_all.sh" || exit 2
# A store outside a work tree is refused before any probe runs.
out=$(bash "$work/probes/run_all.sh" 2>&1); rc=$?
[ "$rc" -eq 2 ] || { echo "a store with no git work tree ran, exit $rc"; exit 1; }
grep -q 'tracked file' <<< "$out" || { echo "the refusal does not say what it cannot see: $out"; exit 1; }
# The tracked file the restoring probe below writes and puts back.
git init -q "$work" || exit 2
printf 'tracked\n' > "$work/tracked.txt"
git -C "$work" add tracked.txt || exit 2
echo "left by an earlier run" > "$work/tools/ci-output/probes/stale.log"

cat > "$work/probes/a--passes-loudly.sh" <<'SH'
#!/usr/bin/env bash
for i in $(seq 1 40); do echo "chatter $i"; done
exit 0
SH
cat > "$work/probes/b--refuses.sh" <<'SH'
#!/usr/bin/env bash
echo "the claim does not hold: reason-b"
exit 1
SH
cat > "$work/probes/c--crashes.sh" <<'SH'
#!/usr/bin/env bash
set -e
python3 -c 'import no_such_module_c'
echo "unreached"
SH
cat > "$work/probes/d--talks-then-refuses.sh" <<'SH'
#!/usr/bin/env bash
for i in $(seq 1 40); do echo "line $i"; done
echo "the last word: reason-d"
exit 2
SH

cat > "$work/probes/e--restores-what-it-wrote.sh" <<'SH'
#!/usr/bin/env bash
printf 'tracked\n' > tracked.txt
exit 0
SH

out=$(bash "$work/probes/run_all.sh")
rc=$?
logs="$work/tools/ci-output/probes"
status=0
fail() { echo "$1"; status=1; }

[ "$rc" -ne 0 ] || fail "the runner exited zero over a store with failures"
grep -qx 'probes: 5 run, exit 1' <<< "$out" || fail "the summary line does not count the five probes"

[ "$(grep -c '^PASS probes/a--passes-loudly.sh$' <<< "$out")" -eq 1 ] || fail "the passing probe is not one PASS line"
grep -q 'chatter' <<< "$out" && fail "a passing probe's output reached the record"
[ ! -e "$logs/a--passes-loudly.log" ] || fail "a passing probe's output was kept"

grep -q '^FAIL probes/b--refuses.sh exit 1, 1 lines kept in tools/ci-output/probes/b--refuses.log$' <<< "$out" \
    || fail "the refusing probe's line does not carry its exit status and its file"
grep -qx '    the claim does not hold: reason-b' <<< "$out" || fail "the refusal's reason is not inline"
grep -qx 'the claim does not hold: reason-b' "$logs/b--refuses.log" 2> /dev/null || fail "the refusal's reason is not in the named file"

grep -q '^FAIL probes/c--crashes.sh exit 1, ' <<< "$out" || fail "the crashing probe's line does not carry its exit status"
grep -q "^    .*No module named 'no_such_module_c'" <<< "$out" || fail "the crash's last line is not inline"
grep -q 'unreached' <<< "$out" && fail "the crashing probe ran past its crash"

grep -q '^FAIL probes/d--talks-then-refuses.sh exit 2, 41 lines kept in ' <<< "$out" || fail "the talkative probe's line does not carry its exit status and line count"
grep -qx '    the last word: reason-d' <<< "$out" || fail "the talkative probe's last line is not inline"
grep -qx '    line 1' <<< "$out" && fail "the talkative probe's whole output reached the record"
grep -qx 'line 1' "$logs/d--talks-then-refuses.log" 2> /dev/null || fail "the talkative probe's whole output is not in the named file"

grep -q '^FAIL probes/e--restores-what-it-wrote.sh exit 0, moved 1 tracked file(s), ' <<< "$out" \
    || fail "the probe that wrote a tracked file and restored it did not fail by count"
grep -qx '    tracked.txt' <<< "$out" || fail "the moved file is not named inline"
grep -qx 'tracked.txt' "$logs/e--restores-what-it-wrote.log" 2> /dev/null || fail "the moved file is not named in the kept log"
[ ! -e "$logs/tracked.before" ] && [ ! -e "$logs/tracked.after" ] || fail "the runner left its snapshots in the record"

[ ! -e "$logs/stale.log" ] || fail "a failure from an earlier run survived"

[ "$status" -eq 0 ] && echo "PASS: a failing probe says why, a passing one says nothing, and a restored write fails"
exit $status
