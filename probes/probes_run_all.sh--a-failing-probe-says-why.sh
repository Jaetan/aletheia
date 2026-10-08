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
# non-zero and counts every probe. A probe's write to a tracked file is
# refused in the probe that made it, and the file keeps its bytes. A probe
# that moves a tracked file's mtime or mode, which the sandbox does not
# govern, fails whatever it exited, its line counting the files it moved and
# its log naming them, because the runner reads every tracked file's mtime,
# size and mode whenever a probe starts or ends; and a store with no git work
# tree around it is refused rather than run unwatched. Every line carries the
# probe's wall time after its path, and the run's times are kept beside its
# failures, one row per probe with its verdict, the record of the latest run
# only. Run one probe at a time or eight, the record is the same once its
# times are taken out; and two workers run two probes at once.
# Non-zero exit: a failure's reason is lost, a passing probe's chatter reaches
# the record, a stale failure survives a run, the runner no longer reports the
# failure, a write to a tracked file is taken, a moved time or mode passes, a
# store outside git runs, a probe's time is missing, shorter than the probe
# ran, or kept from an earlier run, the record depends on how many probes
# run at once, or two workers do not run two probes at once.
set -u
cd "$(dirname "$0")/.." || exit 2
command -v python3 > /dev/null || { echo "python3 is needed to stage a crashing probe"; exit 2; }
work=$(mktemp -d) || exit 2
trap 'chmod -R u+rwx "$work" 2> /dev/null; rm -rf "$work"' EXIT

# stage <directory>: a store of eight probes in a git work tree of its own,
# holding one tracked file, and a record an earlier run left.
stage() {
    mkdir -p "$1/probes" "$1/tools/ci-output/probes" || return 1
    cp probes/run_all.sh "$1/probes/run_all.sh" || return 1
    git init -q "$1" || return 1
    printf 'tracked\n' > "$1/tracked.txt"
    chmod 644 "$1/tracked.txt"
    git -C "$1" add tracked.txt || return 1
    echo "left by an earlier run" > "$1/tools/ci-output/probes/stale.log"
    printf 'probes/z--gone.sh\tPASS\t9.9\n' > "$1/tools/ci-output/probes/timings.tsv"
    cat > "$1/probes/a--passes-loudly.sh" <<'SH'
#!/usr/bin/env bash
for i in $(seq 1 40); do echo "chatter $i"; done
exit 0
SH
    cat > "$1/probes/b--refuses.sh" <<'SH'
#!/usr/bin/env bash
echo "the claim does not hold: reason-b"
exit 1
SH
    cat > "$1/probes/c--crashes.sh" <<'SH'
#!/usr/bin/env bash
set -e
python3 -c 'import no_such_module_c'
echo "unreached"
SH
    cat > "$1/probes/d--talks-then-refuses.sh" <<'SH'
#!/usr/bin/env bash
for i in $(seq 1 40); do echo "line $i"; done
echo "the last word: reason-d"
exit 2
SH
    cat > "$1/probes/e--writes-a-tracked-file.sh" <<'SH'
#!/usr/bin/env bash
if (printf 'changed\n' > tracked.txt) 2> /dev/null; then
    echo "the write to tracked.txt was taken"
    exit 0
fi
echo "the write to tracked.txt was refused"
exit 1
SH
    # Sleeping only ever overshoots, so its time has a floor whatever the machine.
    cat > "$1/probes/f--takes-its-time.sh" <<'SH'
#!/usr/bin/env bash
sleep 0.3
exit 0
SH
    cat > "$1/probes/g--touches-a-tracked-file.sh" <<'SH'
#!/usr/bin/env bash
touch tracked.txt
exit 0
SH
    # Each run flips the mode, so a run of it alone moves the file again.
    cat > "$1/probes/h--flips-a-tracked-mode.sh" <<'SH'
#!/usr/bin/env bash
if [ "$(stat -c %a tracked.txt)" = 644 ]; then chmod 664 tracked.txt; else chmod 644 tracked.txt; fi
exit 0
SH
    chmod +x "$1"/probes/*.sh
}

# A store outside a work tree is refused before any probe runs.
mkdir -p "$work/bare/probes" || exit 2
cp probes/run_all.sh "$work/bare/probes/run_all.sh" || exit 2
out=$(bash "$work/bare/probes/run_all.sh" 2>&1); rc=$?
[ "$rc" -eq 2 ] || { echo "a store with no git work tree ran, exit $rc"; exit 1; }
grep -q 'tracked file' <<< "$out" || { echo "the refusal does not say what it cannot see: $out"; exit 1; }

# Two probes that each wait to see the other running: two workers run both
# at once, and a runner holding them to one at a time fails both. Each waits
# in steps of a tenth of a second, at most thirty seconds, so only a runner
# that does not run them together pays the wait.
mkdir -p "$work/pair/probes" || exit 2
cp probes/run_all.sh "$work/pair/probes/run_all.sh" || exit 2
git init -q "$work/pair" || exit 2
cat > "$work/pair/probes/i--meets-j.sh" <<'SH'
#!/usr/bin/env bash
# On seeing j, says so with a process named for it, and stays until j has
# seen that and gone.
for _ in $(seq 1 300); do
    if pgrep -f 'probes/j--meets-i[.]sh' > /dev/null; then
        (exec -a i-has-seen-j sleep 60) > /dev/null 2>&1 &
        marker=$!
        for _ in $(seq 1 300); do
            pgrep -f 'probes/j--meets-i[.]sh' > /dev/null || { kill "$marker"; exit 0; }
            sleep 0.1
        done
        kill "$marker"
        echo "j did not end"
        exit 1
    fi
    sleep 0.1
done
echo "j never ran alongside i"
exit 1
SH
cat > "$work/pair/probes/j--meets-i.sh" <<'SH'
#!/usr/bin/env bash
for _ in $(seq 1 300); do
    pgrep -f '^i-has-seen-[j] ' > /dev/null && exit 0
    sleep 0.1
done
echo "i never saw j running"
exit 1
SH
chmod +x "$work/pair/probes"/*.sh
pair=$(PROBE_WORKERS=2 bash "$work/pair/probes/run_all.sh" 2>&1)
grep -qx 'probes: 2 run, exit 0' <<< "$pair" || { echo "two workers did not run two probes at once:"; sed 's/^/  /' <<< "$pair"; exit 1; }

stage "$work/one" || exit 2
stage "$work/eight" || exit 2
out=$(PROBE_WORKERS=1 bash "$work/one/probes/run_all.sh")
rc=$?
eight=$(PROBE_WORKERS=8 bash "$work/eight/probes/run_all.sh")
logs="$work/one/tools/ci-output/probes"
status=0
fail() { echo "$1"; status=1; }

[ "$rc" -ne 0 ] || fail "the runner exited zero over a store with failures"
grep -qx 'probes: 8 run, exit 1' <<< "$out" || fail "the summary line does not count the eight probes"

time='[0-9]+\.[0-9]s'
[ "$(grep -cE "^PASS probes/a--passes-loudly.sh $time$" <<< "$out")" -eq 1 ] || fail "the passing probe is not one PASS line with its time"
grep -q 'chatter' <<< "$out" && fail "a passing probe's output reached the record"
[ ! -e "$logs/a--passes-loudly.log" ] || fail "a passing probe's output was kept"

grep -qE "^FAIL probes/b--refuses.sh $time exit 1, 1 lines kept in tools/ci-output/probes/b--refuses.log$" <<< "$out" \
    || fail "the refusing probe's line does not carry its exit status and its file"
grep -qx '    the claim does not hold: reason-b' <<< "$out" || fail "the refusal's reason is not inline"
grep -qx 'the claim does not hold: reason-b' "$logs/b--refuses.log" 2> /dev/null || fail "the refusal's reason is not in the named file"

grep -qE "^FAIL probes/c--crashes.sh $time exit 1, " <<< "$out" || fail "the crashing probe's line does not carry its exit status"
grep -q "^    .*No module named 'no_such_module_c'" <<< "$out" || fail "the crash's last line is not inline"
grep -q 'unreached' <<< "$out" && fail "the crashing probe ran past its crash"

grep -qE "^FAIL probes/d--talks-then-refuses.sh $time exit 2, 41 lines kept in " <<< "$out" || fail "the talkative probe's line does not carry its exit status and line count"
grep -qx '    the last word: reason-d' <<< "$out" || fail "the talkative probe's last line is not inline"
grep -qx '    line 1' <<< "$out" && fail "the talkative probe's whole output reached the record"
grep -qx 'line 1' "$logs/d--talks-then-refuses.log" 2> /dev/null || fail "the talkative probe's whole output is not in the named file"

grep -qE "^FAIL probes/e--writes-a-tracked-file.sh $time exit 1, 1 lines kept in " <<< "$out" \
    || fail "the probe whose write to a tracked file was refused does not fail by its own exit status alone"
grep -qx '    the write to tracked.txt was refused' <<< "$out" || fail "the write to a tracked file was not refused"
[ "$(cat "$work/one/tracked.txt")" = tracked ] || fail "the tracked file lost its bytes"

for mover in g--touches-a-tracked-file h--flips-a-tracked-mode; do
    grep -qE "^FAIL probes/$mover.sh $time exit 0, moved 1 tracked file\\(s\\), " <<< "$out" \
        || fail "$mover moved a tracked file and did not fail by count"
    grep -qx 'tracked.txt' "$logs/$mover.log" 2> /dev/null || fail "the file $mover moved is not named in its kept log"
done
grep -qx '    tracked.txt' <<< "$out" || fail "a moved file is not named inline"
leftovers=$(find "$logs" -maxdepth 1 \( -name '*.reading' -o -name '*.result' -o -name '*.moved' \))
[ -z "$leftovers" ] || fail "the runner left its working files in the record: $leftovers"

[ ! -e "$logs/stale.log" ] || fail "a failure from an earlier run survived"

slept=$(sed -nE "s/^PASS probes\/f--takes-its-time.sh ([0-9]+\.[0-9])s$/\1/p" <<< "$out")
[ -n "$slept" ] || fail "the sleeping probe's line carries no time"
if [ -n "$slept" ] && ! awk -v s="$slept" 'BEGIN { exit !(s >= 0.3) }'; then
    fail "the sleeping probe's time $slept s is shorter than its sleep"
fi
grep -q 'z--gone' "$logs/timings.tsv" 2> /dev/null && fail "a time from an earlier run survived"
expected=$(printf 'probe\tverdict\tseconds\n'; while read -r verdict path seconds _; do printf '%s\t%s\t%s\n' "$path" "$verdict" "${seconds%s}"; done < <(grep -E '^(PASS|FAIL) ' <<< "$out"))
[ "$(cat "$logs/timings.tsv" 2> /dev/null)" = "$expected" ] || fail "the kept times are not the run's, one row per probe in its order"

# The two runs' records, their times taken out.
untimed() { sed -E 's/ [0-9]+\.[0-9]s( |$)/ \1/'; }
record() {
    untimed <<< "$2"
    cut -f1,2 "$1/tools/ci-output/probes/timings.tsv"
    (cd "$1/tools/ci-output/probes" && for log in *.log; do echo "== $log"; cat "$log"; done)
}
if ! difference=$(diff <(record "$work/one" "$out") <(record "$work/eight" "$eight")); then
    fail "one probe at a time and eight at once keep different records:
$difference"
fi

[ "$status" -eq 0 ] && echo "PASS: a failing probe says why, a passing one says nothing, a write to a tracked file is refused, a moved time or mode fails, every probe's time is printed and kept, the record is the same at one worker or eight, and two workers run two probes at once"
exit $status
