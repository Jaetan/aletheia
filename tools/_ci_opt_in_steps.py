# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The sweep's lanes beyond its always-on gates.

The two sanitizer lanes, then the reproducible-build, stability, mutation and
coverage lanes, each enabled by its option or variable (``tools/run_ci.py``).
They share the step counter of the always-on steps, which ``tools/_ci_steps.py``
registers, and are registered after them by its ``register_all_steps``.
"""

from __future__ import annotations

import shlex
from typing import TYPE_CHECKING

from tools._common import BUILD_STEP, CPP_COMPILERS

if TYPE_CHECKING:
    from tools._run_ci_options import OptInOptions
    from tools.run_ci import Runner


def register_opt_in_steps(runner: Runner, opts: OptInOptions) -> None:
    """Run the sanitizer lanes, then the enabled repro, stability, mutation and coverage lanes."""
    # ─── Opt-in lanes (off by default) ──────────────────────────
    # The opt-in lanes share the same step counter as the always-on steps and are
    # tallied by main()'s counting pass too (step() runs in both passes), so
    # total_steps and the "ALL N STEPS PASSED" line in finalize() already reflect
    # whichever lanes are enabled — no separate per-lane bookkeeping here.

    # The two always-on sanitizer lanes (Cat 33a), each building the whole ctest
    # battery in its own tree and asserting every test passes.  UBSan reads
    # undefined behaviour; ASan reads memory the program does not own, which
    # includes the lifetime of a reference, the one class libstdc++'s debug mode
    # in the mutation trees cannot see.  Both are always-on rather than opt-in: a
    # sanitizer lane nobody runs reads nothing, and each of them was opened by a
    # defect that shipped under a green suite.
    # Vendored zippy.hpp UB is filtered via cpp/sanitizer-ignorelist.txt, which
    # applies to every sanitizer; clang is required for that flag (g++ has no
    # equivalent).  ALETHEIA_LIB pins the .so (the same Haskell .so the regular
    # ctest step uses), so the render tests resolve it deterministically rather
    # than via the renderer's cwd-relative probe.  Defined locally — this is a
    # separate function from the core ctest step, so its `cpp_lib` is out of
    # scope here.
    cpp_lib = shlex.quote(str(runner.repo_root / "build" / "libaletheia-ffi.so"))
    runner.step(
        "ubsan ctest",
        sanitizer_ctest_cmd("undefined", cpp_lib),
        cwd=runner.repo_root / "cpp",
        # Own lane (not "cpp"): each sanitizer uses a SEPARATE build tree, so it
        # runs concurrently with the cpp lane's ctest on build/ —
        # splitting the local C++ bottleneck (~305s → ~180s, measured 2026-06-14).
        lane="ubsan",
        needs=(BUILD_STEP,),
    )
    runner.step(
        "asan ctest",
        # detect_stack_use_after_return is asked for by name rather than taken
        # from the sanitizer runtime's default, so the lane reads the same
        # whatever that default is.  What it then reports of that class is what
        # the run reaches: a fake frame is poisoned until the runtime hands the
        # slot to another frame, so a read of a returned frame is certain to be
        # reported only while the slot is still poisoned.  The probe store holds
        # the one such claim the tree has proven, by running that test alone.
        sanitizer_ctest_cmd("address", cpp_lib, env="ASAN_OPTIONS=detect_stack_use_after_return=1"),
        cwd=runner.repo_root / "cpp",
        lane="asan",
        needs=(BUILD_STEP,),
    )

    # Opt-in: reproducible-build gate ────────────────────────────
    if opts.lanes.repro:
        runner.step(
            "check-reproducible-build",
            [runner.python, "-m", "tools.check_reproducible_build"],
            cwd=runner.repo_root,
        )
    else:
        runner.announce_skip(
            "check-reproducible-build",
            "set ALETHEIA_REPRO_CHECK=1 or pass --repro to enable",
        )

    # Opt-in: long-run stability bench ───────────────────────────
    # Agda cat 16 + Python cat 25 + C++ cat 26 + Go cat 27.
    if opts.lanes.stability:
        runner.step(
            "stability bench",
            [runner.python, "-m", "tools.stability_run"],
            cwd=runner.repo_root,
            needs=(BUILD_STEP,),
        )
    else:
        runner.announce_skip(
            "stability bench",
            "set ALETHEIA_STABILITY_CHECK=1 or pass --stability to enable",
        )

    # Opt-in: mutation testing across all 4 bindings ─────────────
    # Cat 14g.  AGENTS.md: "Mutation testing runs as a separate CI lane
    # (cost is high) — once per PR is sufficient; per-commit is overkill."
    # Default OFF.  See docs/operations/MUTATION.md.
    if opts.lanes.mutation:
        runner.step(
            "mutation testing",
            [runner.python, "-m", "tools.mutation_run"],
            cwd=runner.repo_root,
            needs=(BUILD_STEP,),
        )
    else:
        runner.announce_skip(
            "mutation testing",
            "set ALETHEIA_MUTATION_CHECK=1 or pass --mutation to enable",
        )

    # Opt-in: the coverage floors, one step per binding ─────────
    # AGENTS.md § Universal Rules: each binding's suite covers 80 percent of
    # its lines and 60 percent of its branches by its own tool.  One step per
    # binding in that binding's lane, so each runs beside its own suite and
    # the four run concurrently under --parallel; the C++ step builds an
    # instrumented tree of its own (cpp/build-coverage) and the Rust step
    # rebuilds under cargo-llvm-cov's target directory, which is why the lane
    # is opt-in rather than always-on.  See docs/operations/COVERAGE.md.
    if opts.lanes.coverage:
        for binding in ("python", "go", "cpp", "rust"):
            runner.step(
                f"coverage {binding}",
                [runner.python, "-m", "tools.coverage_run", "--binding", binding],
                cwd=runner.repo_root,
                lane=binding,
                needs=(BUILD_STEP,),
            )
    else:
        runner.announce_skip(
            "coverage floors",
            "set ALETHEIA_COVERAGE_CHECK=1 or pass --coverage to enable",
        )


def sanitizer_ctest_cmd(sanitizer: str, cpp_lib: str, *, env: str = "") -> str:
    """Build one sanitizer lane's shell: configure, assert the tree, build, run.

    The assertion between the configure and the build is the lane's own gate on
    itself.  CMake drops a cache whose compiler has changed and configures the
    tree afresh, and a tree configured without ``ALETHEIA_SANITIZER`` builds
    every target with no instrumentation, runs the battery green and reports as
    a sanitizer lane: measured on ``build-asan`` 2026-09-21, where the suite ran
    the 373 cases of an uninstrumented tree rather than the 359 a sanitizer tree
    holds.  Reading the value back from the cache refuses that tree at the point
    it is built rather than at the point somebody trusts it.

    ``sanitizer`` is what ``-DALETHEIA_SANITIZER`` takes and names the tree
    (``build-<name>``, with ``asan``/``ubsan`` the established directory names);
    ``env`` is prefixed to the ctest invocation for a lane whose runtime takes
    options.  clang-23 is pinned for both lanes: a sanitizer lane exercises the
    shipped compiler's codegen, not the runner's older clang, which also fails
    to compile the <expected> libstdc++ ships (std::expected, C++23).
    """
    tree = f"build-{'asan' if sanitizer == 'address' else 'ubsan'}"
    prefix = f"{env} " if env else ""
    return (
        f"cmake -B {tree} -DALETHEIA_SANITIZER={sanitizer} {CPP_COMPILERS} > /dev/null"
        f" && {{ grep -qx 'ALETHEIA_SANITIZER:STRING={sanitizer}' {tree}/CMakeCache.txt"
        f" || {{ echo '{tree} is configured without the {sanitizer} sanitizer'; exit 1; }}; }}"
        f" && cmake --build {tree}"
        f" && ALETHEIA_LIB={cpp_lib} {prefix}ctest --test-dir {tree}"
    )
