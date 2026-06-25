# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Step catalog for the offline CI sweep (``tools/run_ci.py``).

This module owns *which gates exist* — the registration helpers that populate a
:class:`~tools.run_ci.Runner`'s toolchain lanes, plus the constants that classify
them (``AGDA_SHAKE_TARGETS``, ``HEAVY_STEPS``) and the ``build`` prereq command.
It is the part of the sweep that *grows*: every new gate adds a ``runner.step(...)``
here, so keeping it separate from the orchestration core (``run_ci.py``) lets that
core stay a stable, small file.

The single public entry point is :func:`register_all_steps`; ``run_ci.main`` calls
it once to fill the runner, then ``Runner.run`` drives execution.  The per-lane
``_run_*`` helpers are private to this module.  The dependency runs one way at
runtime (``run_ci`` imports this module); the ``Runner`` / ``OptInOptions`` types
are needed only as annotations, so they are imported under ``TYPE_CHECKING`` to
avoid an import cycle.
"""

from __future__ import annotations

import shlex
import shutil
from pathlib import Path
from typing import TYPE_CHECKING

from tools._common import find_executable, run_capture

if TYPE_CHECKING:
    from tools.run_ci import OptInOptions, Runner

# The combined Agda-gate step: every cabal-shake gate folded into ONE
# `cabal run shake -- <targets>` invocation.  Shake (shakeThreads=0, all-core)
# overlaps the two heavy proof checks — measured concurrent peak ~2.3 GiB, ~14%
# of a 16 GB GHA runner, so memory does not bind and no Shake-internal gate is
# needed — and the single process pays cabal/shake startup + build-graph
# re-validation ONCE instead of once per gate (the dominant GHA cost).  `build`
# stays a separate prereq (preserves the build-fail short-circuit); `iwyu` stays
# separate (it reads the .agdai that check-properties writes).  Pinned as a
# tuple so the regression test can assert no gate is silently dropped on edit.
AGDA_GATES_STEP = "agda gates"
AGDA_SHAKE_TARGETS: tuple[str, ...] = (
    "check-properties",
    "check-invariants",
    "check-no-properties-in-runtime",
    "check-erasure",
    "check-fidelity",
    "check-ffi-exports",
    "count-modules",
    "check-changelog",
    "check-gate-claim",
    "check-runbook",
    "check-limits-parity",
    "check-stability-bench",
    "check-mutation-setup",
)

# Big-memory steps gated by the OOM semaphore in --parallel mode.  Centralizing
# the classification (vs. a heavy= flag on every step() call) keeps it reviewable
# in one place.  Chosen from real GHA timings: the combined Agda gates (folds the
# -M16G warm proc + the cabal-test fidelity build), the C++ clang builds, the
# race detector, the FFI pytest lane, and the opt-in lanes.  See .session-state
# Stage B notes.
HEAVY_STEPS: frozenset[str] = frozenset(
    {
        "build",
        AGDA_GATES_STEP,
        "pytest",
        "go test -race",
        "go test -race (excel module)",
        "ctest",
        "ubsan ctest",
        "check-reproducible-build",
        "stability bench",
        "mutation testing",
    }
)


def build_prereq_cmd(python: str) -> list[str]:
    """Return the staleness-gate command (``tools.check_build_incremental``).

    This is the ``build`` step's command only when the staleness gate is
    scheduled (see :func:`should_run_staleness`); otherwise the step runs a
    plain ``cabal run shake -- build``.
    """
    return [python, "-m", "tools.check_build_incremental"]


# Build-graph files: a change to one of these can alter HOW the .so is built —
# the dependency graph the staleness gate verifies — so editing one re-arms the
# gate.  Plain source edits (src/**.agda) do NOT: they exercise the graph, they
# don't change its shape (and `-Werror=missing-home-modules` already catches an
# added-but-unlisted module on every build).  Matched as path prefixes against
# `git diff --name-only` output (repo-relative).
_BUILD_GRAPH_PATHS: tuple[str, ...] = (
    "Shakefile.hs",
    "shake.cabal",
    "aletheia.agda-lib",
    "haskell-shim/",
    "tools/check_build_incremental.py",
    "tools/_warm.py",
)


def _build_graph_changed(repo_root: Path) -> bool:
    """Return True iff the diff vs ``main`` touches a build-graph file.

    Diffs the local ``main`` ref — the repo convention (``tools/_warm.py``'s IWYU
    scope uses ``main...HEAD``; CI's workflow has an "Ensure a local ``main`` ref"
    step for exactly this), not ``origin/main`` (a remote-tracking ref that
    ``actions/checkout`` is not guaranteed to create).  Fails SAFE: if the diff
    can't be computed (e.g. no ``main`` ref), run the staleness gate rather than
    silently skip a safety check.
    """
    result = run_capture(
        [find_executable("git"), "-C", str(repo_root), "diff", "--name-only", "main...HEAD"],
    )
    if result.returncode != 0:
        return True
    return any(line.startswith(_BUILD_GRAPH_PATHS) for line in result.stdout.splitlines())


def should_run_staleness(mode: str, *, build_graph_changed: bool) -> bool:
    """Decide whether the ``build`` step runs the staleness gate vs a plain build.

    ``always`` (the push:main backstop) and ``never`` (escape hatch) are
    unconditional; ``auto`` (the default) runs the gate only when a build-graph
    file changed — re-verifying the build GRAPH on every code PR's two ``.so``
    relinks was pure cost, since only build-graph files change the graph.
    """
    return mode == "always" or (mode == "auto" and build_graph_changed)


def _run_agda_gates(runner: Runner, cabal: list[str]) -> None:
    """Run the build, the Agda gate sweep, and the two branch-scoped IWYU gates."""
    # ─── build (first, alone) ───────────────────────────────────
    # `build` produces the .so / .agdai every other lane needs; run() special-cases
    # it to run FIRST and ALONE (a build failure short-circuits the whole sweep
    # before the parallel lanes spawn).
    #
    # Its COMMAND is chosen by build-staleness scheduling.  When a build-graph file
    # changed (or --build-staleness=always, the push:main backstop) the step IS the
    # staleness gate (check_build_incremental — an edit and its revert must each
    # reach the .so; ~2 .so relinks, slow on a 4-core runner).  Otherwise it is a
    # plain `cabal run shake -- build` (a warm build-tree cache makes it ~a no-op).
    # The staleness PROPERTY is about the build GRAPH, which only build-graph files
    # change — so re-verifying it on every code PR's 2 relinks was pure cost.  Both
    # commands mutate only the shared .so, so this stays the single isolated
    # pre-lane step (no race with the .so-consuming test lanes).
    # Detail: tools/check_build_incremental.py, memory/project_build_so_idempotency.md.
    mode = runner.opts.build_staleness
    graph_changed = mode == "auto" and _build_graph_changed(runner.repo_root)
    if should_run_staleness(mode, build_graph_changed=graph_changed):
        build_cmd: list[str] = build_prereq_cmd(runner.python)
    else:
        build_cmd = [*cabal, "build"]
    runner.step("build", build_cmd, cwd=runner.repo_root, lane="agda")
    # All remaining cabal-shake gates fold into ONE invocation (the Agda-gate
    # fan-in): Shake
    # parallelizes the independent phony rules internally (shakeThreads=0) and
    # the per-process cabal/shake startup + build-graph re-validation is paid
    # once, not once per gate.  Shake fails fast on the first failing target and
    # names it on stderr — surfaced in the failure tail — so attribution
    # survives the fan-in.  AGDA_SHAKE_TARGETS is the single source of truth.
    runner.step(AGDA_GATES_STEP, [*cabal, *AGDA_SHAKE_TARGETS], lane="agda")

    # ─── IWYU gate (one tool) ───────────────────────────────
    # iwyu --check judges BOTH named imports (DEAD/UNRESOLVED) and
    # wildcard `open import M` (DEAD/REDUNDANT/NARROWABLE) via the scope-aware
    # `.agdai` reader in one warm process — no recompile-confirm.  Scope is
    # branch-diff by default (`--diff`: git diff main...HEAD -- src/; empty diff
    # ⇒ no-op — local pre-push-hook parity), or the whole tree (`--all`) under
    # `--iwyu-all` / ALETHEIA_IWYU_ALL=1 — airtight against cross-file deadness,
    # which is what the server-side PR merge gate runs.  iwyu-self-test
    # (`iwyu --self-test`) validates that reader against the synthetic fixture
    # matrix (its correctness gate).  Reference: memory/project_agda_iwyu.md.
    iwyu_scope = "--all" if runner.opts.iwyu_all else "--diff"
    runner.step(
        "iwyu",
        [runner.python, "-m", "tools.iwyu", "--check", iwyu_scope],
        cwd=runner.repo_root,
        lane="agda",
    )
    runner.step(
        "iwyu-self-test",
        [runner.python, "-m", "tools.iwyu", "--self-test"],
        cwd=runner.repo_root,
        lane="agda",
    )


def _run_binding_tests(runner: Runner) -> None:
    """Run the Python / Go / C++ / Rust binding test lanes."""
    # ─── Binding tests ────────────────────────────────────────
    # Deterministic pytest lane.
    runner.step(
        "pytest",
        [runner.python, "-m", "pytest", "tests/"],
        cwd=runner.repo_root / "python",
    )
    # Doc-example fence harness.  Runs from the repo root (cwd=repo_root → would
    # infer the "misc" lane), but it is a pytest invocation sharing the Python
    # toolchain, so pin it to the "python" lane explicitly to keep all pytest
    # runs serial within one lane (the lane invariant; cwd-based inference can't
    # see that a repo-root `python -m pytest` belongs with the python/ steps).
    runner.step(
        "pytest --markdown-docs",
        [
            runner.python,
            "-m",
            "pytest",
            "--markdown-docs",
            "--rootdir",
            str(runner.repo_root),
            "README.md",
            "docs/",
            "python/README.md",
            "examples/README.md",
        ],
        cwd=runner.repo_root,
        lane="python",
    )
    # Python -X dev mode (Cat 34a).
    runner.step(
        "pytest -X dev",
        [runner.python, "-X", "dev", "-m", "pytest", "tests/"],
        cwd=runner.repo_root / "python",
    )
    # Random-order test isolation (Cat 14f).
    runner.step(
        "pytest --random-order",
        [
            runner.python,
            "-m",
            "pytest",
            "--random-order",
            "--random-order-bucket=package",
            "tests/",
        ],
        cwd=runner.repo_root / "python",
    )
    # Cover EVERY Go package, not just ./aletheia/: the core module's packages
    # (aletheia + cmd/aletheia) AND the separate excel module (its own go.mod, so
    # `./...` from go/ stops at the module boundary — it needs its own run).
    # ALETHEIA_LIB pins the .so explicitly so no package depends on
    # findFFILibrary's relative probe: cmd/aletheia's test cwd is too deep for it
    # (its `../../build` resolves to go/build, not the repo root), and setting the
    # env keeps every package's resolution uniform rather than cwd-dependent.
    go_lib = shlex.quote(str(runner.repo_root / "build" / "libaletheia-ffi.so"))
    runner.step(
        "go test -race",
        f"ALETHEIA_LIB={go_lib} go test ./... -count=1 -race",
        cwd=runner.repo_root / "go",
    )
    runner.step(
        "go test -race (excel module)",
        f"ALETHEIA_LIB={go_lib} go test ./... -count=1 -race",
        cwd=runner.repo_root / "go" / "excel",
    )
    runner.step(
        "ctest",
        # Pin to clang-22 — the supported toolchain (latest stable), the SAME
        # compiler the sanitizer + mutation lanes use, so unit tests sanitize the
        # same compilation we ship. Bare `clang`/default cc resolves to the
        # runner's clang-18 / g++ (clang < 19 mis-handles libstdc++-14's C++23
        # <expected>); clang-22 is version-pinned + installed by the workflow via
        # apt.llvm.org (no update-alternatives roulette).
        "cmake -B build -DCMAKE_C_COMPILER=clang-22 -DCMAKE_CXX_COMPILER=clang++-22 "
        + "> /dev/null && cmake --build build && ctest --test-dir build",
        cwd=runner.repo_root / "cpp",
    )
    # Rust binding — loads libaletheia-ffi.so at runtime (like Go / C++). The
    # tracer-bullet slice proves the FFI lifecycle + GHC-allocated-memory
    # ownership; ALETHEIA_LIB points cargo's test at the freshly built .so.
    rust_lib = shlex.quote(str(runner.repo_root / "build" / "libaletheia-ffi.so"))
    # --all-features so the optional `yaml` and `async` features are exercised
    # ("all API languages test everything"); the async-client tests load the .so
    # via the worker thread.
    runner.step(
        "cargo test",
        f"ALETHEIA_LIB={rust_lib} cargo test --all-features",
        cwd=runner.repo_root / "rust",
    )
    # Optional aletheia-excel crate (separate Cargo manifest at rust/excel/, like
    # go/excel/): the main `cargo test` at rust/ does not reach it. Its tests load
    # only the pure-Rust check/DBC API (no .so), so no ALETHEIA_LIB is needed.
    runner.step(
        "cargo test (excel crate)",
        "cargo test",
        cwd=runner.repo_root / "rust" / "excel",
    )


def _run_lints(runner: Runner) -> None:
    """Run the Python / Go / C++ / Rust lint gates."""
    # ─── Lints ────────────────────────────────────────────────
    # ruff (`select=["ALL"]`, config in ruff.toml) over the WHOLE Python tree
    # INCLUDING tools/ (repo-root gate scripts) — both `check` and
    # `format --check`.  `python/mutants` (mutmut output) is excluded in
    # ruff.toml.  Run from the repo root so the root ruff.toml is the config.
    # `--no-cache`: ruff's result cache is keyed on mtime, not file mode, so a
    # cached run silently passes file-mode rules like EXE001 ("shebang present
    # but file not executable") that a fresh CI run catches — making the local
    # sweep / pre-push hook give a false green.  ruff is sub-second, so running
    # cache-free here costs nothing and keeps local == CI.  See
    # memory/feedback_no_shebang_in_tools.md.
    ruff_cmd = (
        f"{shlex.quote(runner.python)} -m ruff check --no-cache tools examples python conftest.py "
        f"&& {shlex.quote(runner.python)} -m ruff format --check tools examples python conftest.py"
    )
    runner.step("ruff", ruff_cmd, cwd=runner.repo_root)

    # ``benchmarks/`` joined the basedpyright gate 2026-05-09, ``tests/`` on
    # 2026-05-31, and ``../tools/`` on 2026-06-06 (pyproject has a strict
    # executionEnvironment for ../tools); pylint covers the same set, so the
    # two stay symmetric (feedback_no_subsumption_asymmetry.md).
    #
    # Invoke via ``runner.python -m basedpyright`` (not the bare ``basedpyright``
    # console script) for the same reason as ruff/pylint — CI launches this sweep
    # as ``python/.venv/bin/python3 -m tools.run_ci``, which does NOT activate
    # the venv, so the venv's ``bin/`` is not on PATH and a bare ``basedpyright``
    # raises FileNotFoundError. ``-m`` runs the venv-installed package directly.
    runner.step(
        "basedpyright",
        [runner.python, "-m", "basedpyright", "aletheia/", "benchmarks/", "tests/", "../tools/"],
        cwd=runner.repo_root / "python",
    )

    # pylint SCORE-based gate per AGENTS.md L611 + feedback_pylint_10_mandatory.md.
    # Covers aletheia/ tests/ benchmarks/ + ../tools/ (the repo-root gate scripts,
    # held to the same 10.00 bar per feedback_tools_lint_standard.md); ``..`` is on
    # the path via python/pyproject's pylint init-hook so tools' imports resolve.
    pylint_cmd = (
        f"{shlex.quote(runner.python)} -m pylint aletheia/ tests/ benchmarks/ ../tools/ "
        "> /tmp/aletheia-pylint.out 2>&1; "
        "rc=$?; cat /tmp/aletheia-pylint.out; "
        "grep -q 'rated at 10\\.00/10' /tmp/aletheia-pylint.out"
    )
    runner.step("pylint", pylint_cmd, cwd=runner.repo_root / "python")

    # gofmt -l (LIST mode): stdout non-empty == files need reformatting. `gofmt -l .`
    # walks every .go file under go/ (it ignores module boundaries, so the excel
    # submodule is covered too); `go vet` does respect them, so excel needs its own
    # invocation alongside the core module's `./...`.
    gofmt_cmd = (
        "gofmt -l . > /tmp/aletheia-gofmt.out 2>&1; rc=$?; "
        "cat /tmp/aletheia-gofmt.out; "
        "test $rc -eq 0 && test ! -s /tmp/aletheia-gofmt.out "
        "&& go vet ./... && (cd excel && go vet ./...)"
    )
    runner.step("gofmt + go vet", gofmt_cmd, cwd=runner.repo_root / "go")

    # clang-format: exclude generated / third-party trees + sanitizer/mutation
    # build trees.
    #
    # Route through the venv-pinned clang-format (the ``clang-format`` pip pkg in
    # [dev]) instead of a bare PATH lookup.  clang-format output is
    # version-specific (trailing-return signatures wrap differently across
    # 18/19), and the system clang-format on a CI runner is whatever
    # update-alternatives selected — often NOT the version apt installs — so an
    # unpinned binary makes the gate non-reproducible.  The venv binary is
    # byte-identical on every contributor + CI; fall back to a PATH lookup only
    # if the venv lacks it (e.g. a non-[dev] environment).
    _clang_format = Path(runner.python).parent / "clang-format"
    clang_format_bin = str(_clang_format) if _clang_format.exists() else "clang-format"
    clang_format_cmd = (
        "find . \\( -path ./build -o -path ./build-tidy "
        "-o -path ./build-asan -o -path ./build-ubsan "
        "-o -path ./build-mutation "
        "-o -path ./_deps -o -path './*/_deps' \\) -prune -o "
        "\\( -name '*.cpp' -o -name '*.hpp' \\) -print | "
        f"xargs {shlex.quote(clang_format_bin)} --dry-run --Werror"
    )
    runner.step("clang-format", clang_format_cmd, cwd=runner.repo_root / "cpp")

    # clang-tidy (AGENTS.md § lint gates, mandatory): lint every C++ TU under
    # cpp/src via run-clang-tidy driven by compile_commands.json.  The compile
    # database is the single source of truth for coverage, so no subdirectory
    # (e.g. src/detail/) can be silently dropped the way the old hand-maintained
    # `src/*.cpp` glob dropped it.  The `cpp/src/` path regex scopes the run to
    # our sources — third-party `_deps`, tests, and benchmarks are excluded.
    runner.step(
        "clang-tidy",
        "run-clang-tidy-22 -quiet -p build cpp/src/",
        cwd=runner.repo_root / "cpp",
    )
    # Coverage guard: every cpp/src/**/*.cpp must appear in the compile DB, so a
    # source someone forgets to wire into a CMake target fails CI rather than
    # being silently unbuilt + unlinted (run-clang-tidy only lints compiled TUs).
    runner.step(
        "check-clang-tidy-coverage",
        [runner.python, "-m", "tools.check_clang_tidy_coverage"],
        cwd=runner.repo_root,
    )

    # Rust lints: rustfmt (check) + clippy (deny warnings) + rustdoc (deny
    # warnings) — the cargo equivalents of gofmt+vet / clang-format+clang-tidy.
    # cargo doc catches broken/redundant intra-doc links (--document-private-items
    # so internal docs are checked too; --all-features so the `async` items the docs
    # link to resolve). It needs no .so — `--no-deps` documents only this crate and
    # does not run doctests.
    runner.step(
        "cargo fmt + clippy",
        "cargo fmt --check && cargo clippy --all-targets --all-features -- -D warnings",
        cwd=runner.repo_root / "rust",
    )
    runner.step(
        "cargo doc (warnings = errors)",
        'RUSTDOCFLAGS="-D warnings" cargo doc --no-deps --document-private-items --all-features',
        cwd=runner.repo_root / "rust",
    )
    runner.step(
        "cargo fmt + clippy (excel crate)",
        "cargo fmt --check && cargo clippy --all-targets -- -D warnings",
        cwd=runner.repo_root / "rust" / "excel",
    )
    runner.step(
        "cargo doc (excel crate, warnings = errors)",
        'RUSTDOCFLAGS="-D warnings" cargo doc --no-deps --document-private-items',
        cwd=runner.repo_root / "rust" / "excel",
    )


def _run_gha_checks(runner: Runner) -> None:
    """Run the GitHub-Actions workflow meta-checks plus the SPDX-header gate."""
    # ─── GHA meta-checks + SPDX header gate ──────────────────────────────────────
    if shutil.which("actionlint"):
        if (runner.repo_root / ".github" / "workflows").is_dir():
            runner.step("actionlint", ["actionlint", "-color"])
        else:
            runner.announce_skip("actionlint", "no .github/workflows/ directory")
    else:
        runner.announce_skip(
            "actionlint",
            "binary not installed; see docs/development/CI_LOCAL.md",
        )

    runner.step(
        "check-action-pins",
        [runner.python, "-m", "tools.check_action_pins"],
        cwd=runner.repo_root,
    )
    runner.step(
        "check-workflow-permissions",
        [runner.python, "-m", "tools.check_workflow_permissions"],
        cwd=runner.repo_root,
    )
    runner.step(
        "check-spdx-headers",
        [runner.python, "-m", "tools.check_spdx_headers"],
        cwd=runner.repo_root,
    )
    runner.step(
        "check-venv-convention",
        [runner.python, "-m", "tools.check_venv_convention"],
        cwd=runner.repo_root,
    )


def _run_opt_in_lanes(runner: Runner, opts: OptInOptions) -> None:
    """Run the always-on UBSan lane then the enabled repro / stability / mutation lanes."""
    # ─── Opt-in lanes (off by default) ──────────────────────────
    # The opt-in lanes share the same step counter as the always-on steps and are
    # tallied by main()'s counting pass too (step() runs in both passes), so
    # total_steps and the "ALL N STEPS PASSED" line in finalize() already reflect
    # whichever lanes are enabled — no separate per-lane bookkeeping here.

    # Always-on UBSan lane (Cat 33a; promoted from opt-in to
    # always-on after UB in Rational::from_double had previously shipped
    # undetected exactly because the lane was opt-in).  Builds the full
    # ctest battery against -DALETHEIA_SANITIZER=undefined and asserts
    # every test passes.  Vendored zippy.hpp UB filtered via
    # cpp/sanitizer-ignorelist.txt; clang required (g++ has no equivalent).
    runner.step(
        "ubsan ctest",
        # clang-22 (the supported toolchain — matches the regular ctest + mutation
        # lanes).  UB can differ between compiler versions, so the sanitizer lane
        # MUST exercise the shipped compiler's codegen, not an older clang; bare
        # `clang++` also resolves to the runner's clang-18, which fails to compile
        # libstdc++-14's <expected> (std::expected, C++23).
        "cmake -B build-ubsan -DALETHEIA_SANITIZER=undefined "
        + "-DCMAKE_C_COMPILER=clang-22 -DCMAKE_CXX_COMPILER=clang++-22 > /dev/null"
        + " && cmake --build build-ubsan && ctest --test-dir build-ubsan",
        cwd=runner.repo_root / "cpp",
        # Own lane (not "cpp"): ubsan uses a SEPARATE build-ubsan/ dir, so it runs
        # concurrently with the cpp lane's ctest→clang-tidy on build/ — splitting
        # the local C++ bottleneck (~305s → ~180s, measured 2026-06-14).
        lane="ubsan",
    )

    # Opt-in: reproducible-build gate ────────────────────────────
    if opts.repro:
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
    if opts.stability:
        runner.step(
            "stability bench",
            [runner.python, "-m", "tools.stability_run"],
            cwd=runner.repo_root,
        )
    else:
        runner.announce_skip(
            "stability bench",
            "set ALETHEIA_STABILITY_CHECK=1 or pass --stability to enable",
        )

    # Opt-in: mutation testing across all 3 bindings ─────────────
    # Cat 14g.  AGENTS.md: "Mutation testing runs as a separate CI lane
    # (cost is high) — once per PR is sufficient; per-commit is overkill."
    # Default OFF.  See docs/operations/MUTATION.md.
    if opts.mutation:
        runner.step(
            "mutation testing",
            [runner.python, "-m", "tools.mutation_run"],
            cwd=runner.repo_root,
        )
    else:
        runner.announce_skip(
            "mutation testing",
            "set ALETHEIA_MUTATION_CHECK=1 or pass --mutation to enable",
        )


def register_all_steps(runner: Runner, cabal: list[str], opts: OptInOptions) -> None:
    """Register every phase's steps into the runner (no execution; run() drives them)."""
    _run_agda_gates(runner, cabal)
    _run_binding_tests(runner)
    _run_lints(runner)
    _run_gha_checks(runner)
    _run_opt_in_lanes(runner, opts)
