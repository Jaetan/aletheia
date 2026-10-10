#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Runs every probe in this directory from the repository root, PROBE_WORKERS
# of them at once (4 unless the caller says otherwise), each one as
# soon as a worker is free. A passing probe prints one line, PASS and its
# path, whatever it said. A failing probe prints FAIL, its path and its exit
# status, then the last lines of its own output indented beneath, and the
# whole output is kept in tools/ci-output/probes/, in a file the FAIL line
# names, so a probe that crashed reads differently from one that refused its
# claim. Every line carries the probe's wall time after its path, and the
# run's times are kept in timings.tsv beside the failures, one row per probe
# with its verdict. Lines and rows are in path order whatever order the
# probes finish in, so two runs' records compare line by line. The directory
# holds only the failures and the times of the latest run.
# Probes share nothing they write. Each runs under a Landlock ruleset that
# lets it read the whole file system and write only beneath a directory of
# its own outside the tree, which is its TMPDIR and is removed when it ends,
# beneath the caches that lock themselves (the tool caches in the home
# directory with ccache's temporary directory, and the git directory), and to
# /dev/null, /dev/zero, /dev/full and /dev/tty: a write anywhere else, a
# tracked file or another probe's directory, is refused in the probe that
# made it. A probe starts with SIGINT and SIGQUIT at their defaults, as
# one run by hand does, though the runner starts it in the background.
# A probe starts with PYTHON_CPU_COUNT at the runner's CPUs divided by
# PROBE_WORKERS, at least one: a tool that sizes its jobs from
# multiprocessing.cpu_count() (run-clang-tidy does) otherwise starts one per
# CPU of the machine, whatever CPUs the runner was given, in every probe at
# once.
# Landlock does not govern a file's times or mode, so every tracked file's
# mtime, size and mode are read whenever a probe starts or ends, and a change
# makes the probes running since the previous reading suspects; each suspect
# runs again alone, and the one that moves a file then fails whatever it
# exited, its line naming the count and its log the paths.
# Exits non-zero when any probe fails, and 2 where the tracked files cannot be
# listed, the shell cannot read its clock to the microsecond or wait on one
# probe at a time (bash 5.1), Landlock is not to be had, or PROBE_WORKERS is
# not a positive count. A probe is a bash script named
# <subject>--<property>.sh that exits zero when the property it states in its
# header holds. Each one names its own interpreter and is executable, so it
# runs the same whether this runner invokes it or a reader does.
set -u
root=$(cd "$(dirname "$0")/.." && pwd)
cd "$root" || exit 2
logs=tools/ci-output/probes
timings=$logs/timings.tsv
shown=12
workers=${PROBE_WORKERS:-4}
case $workers in
    '' | *[!0-9]* | 0*) echo "run_all: PROBE_WORKERS is '$workers', not a positive count of probes to run at once"; exit 2 ;;
esac
share=$(($(nproc) / workers))
export PYTHON_CPU_COUNT=$((share ? share : 1))
[ -n "${EPOCHREALTIME:-}" ] || { echo "run_all: this shell has no EPOCHREALTIME (bash 5), so a probe's time cannot be read"; exit 2; }
((BASH_VERSINFO[0] > 5 || (BASH_VERSINFO[0] == 5 && BASH_VERSINFO[1] >= 1))) \
    || { echo "run_all: bash $BASH_VERSION cannot wait on one probe at a time (5.1 can)"; exit 2; }
setpriv --landlock-access fs:write-file true 2> /dev/null \
    || { echo "run_all: setpriv or the kernel offers no Landlock, so a probe's writes cannot be kept to its own directory"; exit 2; }
git ls-files > /dev/null || { echo "run_all: not in a git work tree, so a write to a tracked file cannot be seen"; exit 2; }
mkdir -p "$logs" || exit 2
rm -f "$logs"/*.log "$logs"/*.result "$logs"/*.reading
own_root=$(mktemp -d -t probes.XXXXXX) || exit 2
trap 'chmod -R u+rwx "$own_root" 2> /dev/null; rm -rf "$own_root"' EXIT
printf 'probe\tverdict\tseconds\n' > "$timings" || exit 2
# Microseconds since the epoch, whatever separator the locale puts in the clock.
now() { echo "${EPOCHREALTIME//[^0-9]/}"; }
tracked() { git ls-files -z | xargs -0 stat -c '%n %.9Y %s %a' 2> /dev/null; }
moved() { diff "$1" "$2" | sed -n 's/^[<>] \(.*\) [0-9.]* [0-9]* [0-9]*$/\1/p' | sort -u; }

# Every right Landlock governs on a file system, granted beneath the places a
# probe may write; everywhere else it may read and execute only.
file_rights=execute,write-file,read-file,truncate,ioctl-dev
rights=$file_rights,read-dir,remove-dir,remove-file,make-char,make-dir,make-reg,make-sock,make-fifo,make-block,make-sym,refer
shared=("$HOME/.cache" "$HOME/.cargo" "$HOME/.rustup" "$HOME/go" "$root/.git" /dev/null /dev/zero /dev/full /dev/tty)
# ccache writes its temporary files outside its cache, in a directory of its own.
if ccache_temporary=$(ccache -k temporary_dir 2> /dev/null) && mkdir -p "$ccache_temporary"; then
    shared+=("$ccache_temporary")
fi

# Run probe number $1 in its own directory under the ruleset, its output in
# its log and its exit status and time beside it.
run_one() {
    local probe=${probes[$1]} name own log start rc end place
    name=$(basename "$probe" .sh)
    own=$own_root/$name
    log=$logs/$name.log
    mkdir -p "$own" || { echo "2 0.0" > "$log.result"; return; }
    local rules=(--landlock-access fs --landlock-rule "path-beneath:execute,read-file,read-dir:/")
    for place in "$own" "${shared[@]}"; do
        if [ -d "$place" ]; then
            rules+=(--landlock-rule "path-beneath:$rights:$place")
        elif [ -e "$place" ]; then
            rules+=(--landlock-rule "path-beneath:$file_rights:$place")
        fi
    done
    start=$(now)
    # A background job of a shell without job control ignores both signals.
    TMPDIR=$own env --default-signal=INT,QUIT setpriv "${rules[@]}" -- bash "$probe" > "$log" 2>&1
    rc=$?
    end=$(now)
    chmod -R u+rwx "$own" 2> /dev/null
    rm -rf "$own"
    echo "$rc $(((end - start) / 1000000)).$(((end - start) / 100000 % 10))" > "$log.result"
}

# Print probe number $1's line from its result and keep its time; the files
# named in $2 are the tracked files it moved.
status=0
count=0
report() {
    local probe=${probes[$1]} moved=$2 name log rc took lines verdict
    name=$(basename "$probe" .sh)
    log=$logs/$name.log
    read -r rc took < "$log.result"
    rm -f "$log.result"
    count=$((count + 1))
    if [ -n "$moved" ]; then
        {
            echo "the probe moved these tracked files, whatever it wrote back:"
            echo "$moved"
        } >> "$log"
        lines=$(grep -c '' "$log")
        echo "FAIL $probe ${took}s exit $rc, moved $(echo "$moved" | grep -c '') tracked file(s), $lines lines kept in $log"
        tail -n "$shown" "$log" | sed 's/^/    /'
        status=1
        verdict=FAIL
    elif [ "$rc" -eq 0 ]; then
        echo "PASS $probe ${took}s"
        rm -f "$log"
        verdict=PASS
    else
        lines=$(grep -c '' "$log")
        echo "FAIL $probe ${took}s exit $rc, $lines lines kept in $log"
        tail -n "$shown" "$log" | sed 's/^/    /'
        status=1
        verdict=FAIL
    fi
    printf '%s\t%s\t%s\n' "$probe" "$verdict" "$took" >> "$timings"
}

# Read the tracked files again; on a change since the last reading, every
# probe running since then (those still running and those just ended, named
# in the arguments) is a suspect.
declare -A running=()
declare -A suspect=()
check() {
    local index
    tracked > "$logs/now.reading"
    if [ -n "$(moved "$logs/last.reading" "$logs/now.reading")" ]; then
        for index in "${running[@]}" "$@"; do
            suspect[$index]=1
        done
    fi
    mv "$logs/now.reading" "$logs/last.reading"
}

# Print every finished probe in path order up to the first one not finished
# or under suspicion.
printed=0
print_ready() {
    while [ "$printed" -lt "${#probes[@]}" ] \
        && [ -e "$logs/$(basename "${probes[$printed]}" .sh).log.result" ] \
        && [ -z "${suspect[$printed]:-}" ]; do
        report "$printed" ""
        printed=$((printed + 1))
    done
}

mapfile -t probes < <(find probes -name '*.sh' ! -name run_all.sh | sort)
tracked > "$logs/last.reading"
next=0
while [ "$next" -lt "${#probes[@]}" ] || [ "${#running[@]}" -gt 0 ]; do
    while [ "$next" -lt "${#probes[@]}" ] && [ "${#running[@]}" -lt "$workers" ]; do
        check
        run_one "$next" &
        running[$!]=$next
        next=$((next + 1))
    done
    wait -n -p finished
    index=${running[$finished]}
    unset "running[$finished]"
    check "$index"
    print_ready
done

# Each suspect runs again alone between two readings of the tracked files;
# the one that moves a file is the one that fails for it.
for index in $(printf '%s\n' "${!suspect[@]}" | sort -n); do
    rm -f "$logs/$(basename "${probes[$index]}" .sh).log.result"
    tracked > "$logs/last.reading"
    run_one "$index"
    tracked > "$logs/now.reading"
    moved "$logs/last.reading" "$logs/now.reading" > "$logs/$index.moved"
done
suspects=$(for index in $(printf '%s\n' "${!suspect[@]}" | sort -n); do
    echo "${probes[$index]}"
done)
unnamed=
if [ -n "$suspects" ] && [ -z "$(cat "$logs"/*.moved 2> /dev/null)" ]; then
    unnamed=$suspects
fi
moved_by=()
while [ "$printed" -lt "${#probes[@]}" ]; do
    if [ -e "$logs/$printed.moved" ]; then
        moved_by[printed]=$(cat "$logs/$printed.moved")
        rm -f "$logs/$printed.moved"
    fi
    report "$printed" "${moved_by[$printed]:-}"
    printed=$((printed + 1))
done
if [ -n "$unnamed" ]; then
    echo "FAIL a tracked file moved while these probes ran, and none of them moved one alone:"
    while IFS= read -r suspect_path; do echo "    $suspect_path"; done <<< "$unnamed"
    status=1
fi
rm -f "$logs/last.reading" "$logs/now.reading"
echo "probes: $count run, exit $status"
exit $status
