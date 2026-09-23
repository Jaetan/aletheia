#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes the four benchmark harnesses benchmarks/run_all.sh drives:
# python/benchmarks/throughput.py and latency.py, go/benchmarks/main.go,
# cpp/benchmarks/benchmark.cpp with measure.hpp, rust/examples/benchmark.rs.
# Claim: every warmup loop aborts the lane on a failed operation the way the
# measured loop does. A harness whose warmup failed ran against a client it
# could not drive, and its measured runs then measure something else or fail
# later for the same cause with the warmup's message gone. Per warmup loop:
# the operation it calls is the one the measured loop times, it is guarded as
# the measured call is (an error arm that returns, a require, an expect, or
# a bare call in a language where the error is an exception), and the
# function around it catches nothing.
# Non-zero exit: a warmup loop is missing, calls something the measured loop
# does not, swallows its error, or sits inside a catching construct. Exits 2
# without the Python venv.
set -u
cd "$(dirname "$0")/.." || exit 2
py=python/.venv/bin/python
[ -x "$py" ] || exit 2

"$py" - <<'EOF'
import re
import sys
from pathlib import Path

findings: list[str] = []


def braced(text: str, start: int) -> str:
    """The text from the first '{' at or after start to its matching '}'."""
    depth = 0
    i = text.index("{", start)
    for j in range(i, len(text)):
        if text[j] == "{":
            depth += 1
        elif text[j] == "}":
            depth -= 1
            if depth == 0:
                return text[i : j + 1]
    raise ValueError("unbalanced braces")


def indented(text: str, start: int) -> str:
    """A Python block: the line at start and every deeper-indented line after it."""
    lines = text[start:].splitlines()
    head = len(lines[0]) - len(lines[0].lstrip())
    body = [lines[0]]
    for line in lines[1:]:
        if line.strip() and len(line) - len(line.lstrip()) <= head:
            break
        body.append(line)
    return "\n".join(body)


def block(text: str, m: re.Match[str], lang: str) -> str:
    """The loop body: an indented block, a braced one, or the one statement a
    brace-less C++ for carries."""
    if lang == "python":
        return indented(text, m.start())
    brace = text.find("{", m.start())
    semicolon = text.find(";", m.end())
    if semicolon != -1 and (brace == -1 or semicolon < brace):
        return text[m.start() : semicolon + 1]
    return braced(text, m.start())


HEADS = {"go": r"^func ", "cpp": r"^(?:static )?auto ", "rust": r"^(?:pub )?fn ", "python": r"^def "}


def enclosing(text: str, pos: int, lang: str) -> str:
    heads = [m for m in re.finditer(HEADS[lang], text, re.M) if m.start() <= pos]
    if not heads:
        return ""
    start = heads[-1].start()
    return indented(text, start) if lang == "python" else braced(text, start)


FORBID = {
    "go": r"recover\(|Warmup error",
    "cpp": r"\btry\b|\bcatch\b",
    "rust": r"catch_unwind|\.ok\(\)|unwrap_or|if let Err|Err\(_\)",
    "python": r"\btry\b|\bexcept\b|suppress\(",
}

# One row per warmup loop: the file, the language, the loop's head, how many
# such loops the file holds, the guard the loop body must carry, and the call
# it makes with the measured call the file must make with the same callee.
SITES = [
    # Go throughput: the error arm returns, and the callee is measured below.
    ("go/benchmarks/main.go", "go", r"for w := 0; w < warmupRuns; w\+\+ \{", 1,
     r"err != nil \{\s*(?:return\b|die\()", (r"(?P<callee>[\w.]+)\(numFrames / 10\)", "{callee}(numFrames)")),
    # Go latency: one loop, the error arm returns, op() on both sides.
    ("go/benchmarks/main.go", "go", r"for i := 0; i < warmup; i\+\+ \{", 1,
     r"err != nil \{\s*return\b", (r"(?P<callee>\w+)\(\)", "start := time.Now()\n\t\tif err := {callee}(); err != nil {{\n\t\t\treturn")),
    # C++ throughput: the warmup calls the measured function, which throws.
    ("cpp/benchmarks/benchmark.cpp", "cpp", r"std::views::repeat\(0, warmup_runs\)", 1,
     None, (r"(?P<callee>\w+)\(num_frames / 10\)", "{callee}(num_frames)")),
    # C++ latency: require() on both sides.
    ("cpp/benchmarks/measure.hpp", "cpp", r"for \(auto const i : std::views::iota\(0, warmup\)\)", 1,
     r"require\(op\(i\), step\)", None),
    # Rust throughput: the lane is Fn(u64) -> f64, so a failure is a panic
    # inside it; the warmup calls the same closure the measured loop does.
    ("rust/examples/benchmark.rs", "rust", r"for _ in 0\.\.warmup \{\s*let _ = ", 1,
     None, (r"(?P<callee>\w+)\(frames / 10\)", "{callee}(frames)")),
    # Rust latency: three loops, expect() on the warmup call, and the same
    # method timed under Instant::now().
    ("rust/examples/benchmark.rs", "rust", r"for i in 0\.\.warmup \{", 1,
     r"\.expect\(", (r"client\s*\.(?P<callee>\w+)\(", "Instant::now();\n        client\n            .{callee}(")),
    ("rust/examples/benchmark.rs", "rust", r"for _ in 0\.\.warmup \{\s*client", 2,
     r"\.expect\(", (r"client\s*\.(?P<callee>\w+)\(", "Instant::now();\n        client\n            .{callee}(")),
    # Python throughput: the warmup calls the measured function, which raises.
    ("python/benchmarks/throughput.py", "python", r"for _ in range\(cfg\.warmup_runs\):", 1,
     None, (r"(?P<callee>\w+)\(cfg\.num_frames // 10\)", "{callee}(cfg.num_frames)")),
    # Python latency: three loops, each calling the method timed under
    # perf_counter() in its _measure_ function.
    ("python/benchmarks/latency.py", "python", r"for \w+ in range\(ctx\.warmup\):", 3,
     None, (r"client\.(?P<callee>\w+)\(", "start = time.perf_counter()\n        client.{callee}(")),
]


def check(path: str, lang: str, loop_re: str, expected: int, guard: str | None, call) -> None:
    text = Path(path).read_text(encoding="utf-8")
    loops = list(re.finditer(loop_re, text))
    if len(loops) != expected:
        findings.append(f"{path}: {len(loops)} warmup loops match {loop_re!r}, expected {expected}")
        return
    for m in loops:
        line = text.count("\n", 0, m.start()) + 1
        body = block(text, m, lang)
        where = f"{path}:{line}"
        if guard and not re.search(guard, body):
            findings.append(f"{where}: the warmup loop does not guard its call with {guard!r}")
        if call:
            warm_re, measured_tmpl = call
            wm = re.search(warm_re, body)
            if not wm:
                findings.append(f"{where}: the warmup loop makes no call matching {warm_re!r}")
            else:
                measured = measured_tmpl.format(callee=wm.group("callee"))
                if measured not in text:
                    findings.append(f"{where}: warmup calls {wm.group('callee')!r} but nothing times {measured!r}")
        fn = enclosing(text, m.start(), lang)
        if not fn:
            findings.append(f"{where}: no enclosing function found")
        elif (hit := re.search(FORBID[lang], fn)):
            findings.append(f"{where}: the function around the warmup loop catches: {hit.group(0)!r}")


for site in SITES:
    check(*site)

# The Rust lane yields a bare number, so its failure can only be a panic inside
# it; a lane returning a Result would make `let _ =` a discard.
if "type Lane<'a> = (&'static str, Box<dyn Fn(u64) -> f64 + 'a>);" not in Path("rust/examples/benchmark.rs").read_text(encoding="utf-8"):
    findings.append("rust/examples/benchmark.rs: the throughput lane is not spelled Fn(u64) -> f64")

if findings:
    print("\n".join(findings))
    sys.exit(1)
print(f"PASS: {sum(s[3] for s in SITES)} warmup loops across four harnesses abort on a failed operation")
EOF
