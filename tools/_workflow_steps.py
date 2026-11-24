# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""What a workflow's ``run:`` step runs, as the watchdog judges it: watched, or exempt and why.

Every ``run:`` step of a job that checks out the tree runs under ``tools.watch_step``, which
asks :func:`declared_for` what the step's script is; a job that checks out nothing runs
GitHub's own ``bash -e`` and only exempt steps.  A script matching one watched declaration is
watched, its declaration carrying the step's progress (``tools._watchdog``).  A script matching
no watched declaration is exempt by the first exempt one it matches (a tool's install, a cache,
the setup of a runner, the packaging, signing or publishing of a release, a tally of the jobs
it needs, or the printing of what the job found): no deadline holds it, and its output still
reaches the job log as it comes.  A script matching no declaration, or more than one watched
one, is refused, so a step added to a job that checks out the tree is declared before it runs.
"""

from __future__ import annotations

import re
from dataclasses import dataclass
from typing import NewType

from tools._ci_progress import (
    ALLOWANCE_FLOOR,
    COVERAGE_OF_EVERY_BINDING,
    LONGEST_STEP_ALLOWANCE,
    either,
    progress_of,
)
from tools._common import GateName
from tools._watchdog import PatternText, Progress, Seconds

from aletheia.common_types import Prose

# A step's ``run:`` text, as the workflow spells it or as GitHub hands it to the shell with its
# expressions filled in.
ScriptText = NewType("ScriptText", str)

# The reason a watched step carries, which needs none.
_NO_REASON = Prose("")


@dataclass(frozen=True)
class WorkflowStep:
    """A kind of workflow step: the script lines that are it, and its progress or why it is exempt.

    ``runs`` is searched in the script, a line at a time; ``progress`` is
    ``None`` for an exempt step, which ``why`` explains.
    """

    runs: PatternText
    progress: Progress | None
    why: Prose = _NO_REASON

    def names(self, script: ScriptText) -> bool:
        """Answer whether ``runs`` matches a line of ``script``.

        :func:`declared_for` decides which matching kind the step is.
        """
        return any(re.search(self.runs, line) is not None for line in script.splitlines())


def _watched(runs: PatternText, progress: Progress) -> WorkflowStep:
    """Declare a watched step: the lines that are it, and how it reports its progress."""
    return WorkflowStep(runs, progress)


# How the steps that are not the sweep's report: the sweep's own lines as each of its steps starts,
# passes a quarter of a count, or ends; the benchmark runner's line as each binding starts and
# ends; ours.  The sweep run as one step outlasts the longest allowance of a step it runs by the
# floor, so the sweep's own watchdog stops and names a stuck step first when that step's last
# report came less than the floor after the sweep's last line.  The benchmark runner's longest
# stretch measured without a report on GitHub's runners, 103 s, puts it on the floor.
_SWEEP = Progress(PatternText(r"^(▶|✓|✗|⊘|⋯) "), Seconds(LONGEST_STEP_ALLOWANCE + ALLOWANCE_FLOOR))
_BENCHMARKS = Progress(PatternText(r"^>>> Running |^Saved: "), ALLOWANCE_FLOOR)
_OURS = progress_of(GateName("check-action-pins"))
# The sweep steps whose tools a workflow step also runs, reporting as they do there.
_ACTIONLINT = progress_of(GateName("actionlint"))
_BUILD = progress_of(GateName("build"))
_CHECK_CARGO_MUTANTS_SHARDS = progress_of(GateName("check-cargo-mutants-shards"))
_CHECK_CPP_SLICES_CENSUS = progress_of(GateName("check-cpp-slices-census"))
_CHECK_CPP_SLICES_CENSUS_BUILD = progress_of(GateName("check-cpp-slices-census-build"))
_CHECK_MULL_PLUGIN_FACTS = progress_of(GateName("check-mull-plugin-facts"))
_CHECK_MUTMUT_OPERATORS = progress_of(GateName("check-mutmut-operators"))
_CHECK_MUTMUT_WITNESS = progress_of(GateName("check-mutmut-witness"))
_CHECK_REPRODUCIBLE_BUILD = progress_of(GateName("check-reproducible-build"))
_CPP_BUILD = progress_of(GateName("cpp build"))
_GO_BUILD_NO_CGO = progress_of(GateName("go build (no cgo)"))
_MUTATION_TESTING = progress_of(GateName("mutation testing"))
_STABILITY_BENCH = progress_of(GateName("stability bench"))
# A dist builds the kernel and checks its proofs, reporting as the build and the proof gates do.
_DIST = either(_BUILD, progress_of(GateName("agda gates")))
# The schema step builds the Rust benchmark, then checks every binding's report.
_BENCH_SCHEMA = either(
    progress_of(GateName("cargo build (tests)")), progress_of(GateName("check-bench-schema"))
)


def _exempt(runs: PatternText, why: Prose) -> WorkflowStep:
    """Declare a step only GitHub runs, which no deadline holds."""
    return WorkflowStep(runs, None, why)


# The watched steps, each its own declaration so each gets its own progress.
WATCHED: tuple[WorkflowStep, ...] = (
    _watched(PatternText(r"-m tools\.run_ci\b"), _SWEEP),
    _watched(PatternText(r"cabal run shake -- build\b"), _BUILD),
    _watched(PatternText(r"cabal run shake -- --keep-going dist\b"), _DIST),
    _watched(PatternText(r"-m tools\.mutation_scope\b"), _OURS),
    _watched(PatternText(r"-m tools\.mutation_run\b"), _MUTATION_TESTING),
    _watched(
        PatternText(r"-m tools\.check_mutmut_operators\b"),
        _CHECK_MUTMUT_OPERATORS,
    ),
    _watched(
        PatternText(r"-m tools\.check_mutmut_witness\b"),
        _CHECK_MUTMUT_WITNESS,
    ),
    _watched(
        PatternText(r"-m tools\.check_cargo_mutants_shards\b"),
        _CHECK_CARGO_MUTANTS_SHARDS,
    ),
    _watched(
        PatternText(r"-m tools\.check_mull_plugin_facts\b"),
        _CHECK_MULL_PLUGIN_FACTS,
    ),
    _watched(
        PatternText(r"-m tools\.check_cpp_slices_census --census\b"),
        _CHECK_CPP_SLICES_CENSUS_BUILD,
    ),
    _watched(
        PatternText(r"-m tools\.check_cpp_slices_census --compare\b"),
        _CHECK_CPP_SLICES_CENSUS,
    ),
    _watched(PatternText(r"-m tools\.benchmark_scope\b"), _OURS),
    _watched(PatternText(r"-m tools\.benchmark_instructions\b"), _OURS),
    _watched(PatternText(r"-m tools\.benchmark_gate\b"), _OURS),
    _watched(PatternText(r"benchmarks/run_all\.sh\b"), _BENCHMARKS),
    _watched(PatternText(r"cmake -S cpp -B cpp/build\b"), _CPP_BUILD),
    _watched(
        PatternText(r"go build -o benchmarks/benchmark\b"),
        _GO_BUILD_NO_CGO,
    ),
    _watched(PatternText(r"-m tools\.check_bench_schema\b"), _BENCH_SCHEMA),
    _watched(PatternText(r"-m tools\.coverage_run\b"), COVERAGE_OF_EVERY_BINDING),
    _watched(PatternText(r"-m tools\.stability_run\b"), _STABILITY_BENCH),
    _watched(
        PatternText(r"-m tools\.check_reproducible_build\b"),
        _CHECK_REPRODUCIBLE_BUILD,
    ),
    _watched(PatternText(r"-m tools\.licence_audit\b"), _OURS),
    _watched(PatternText(r"-m tools\.check_action_pins\b"), _OURS),
    _watched(PatternText(r"-m tools\.check_workflow_permissions\b"), _OURS),
    _watched(PatternText(r"-m tools\.check_pr_title\b"), _OURS),
    _watched(PatternText(r"^\s*\./actionlint\b"), _ACTIONLINT),
)

# Why a step only GitHub runs is exempt.
_SETUP = Prose("sets up the runner, which a local run already is")
_INSTALL = Prose("installs a tool on the runner, which a local run already has")
_CACHE = Prose("keeps GitHub's caches")
_RELEASE = Prose("packages, signs or publishes a release, which only GitHub does")
_TALLY = Prose("reads the result of the jobs it needs, which only GitHub has")
_LOG = Prose("prints what the job found into its log, which only GitHub has")

# Steps only GitHub runs.
EXEMPT: tuple[WorkflowStep, ...] = (
    _exempt(PatternText(r"^\s*git fetch --no-tags origin\b"), _SETUP),
    _exempt(PatternText(r"^\s*python(3(\.14)?)? -m venv python/\.venv\b"), _SETUP),
    _exempt(PatternText(r"\bexport CABAL_DIR="), _SETUP),
    _exempt(PatternText(r"^\s*ghcup install\b"), _INSTALL),
    _exempt(PatternText(r"^\s*cabal update\b"), _SETUP),
    _exempt(PatternText(r'^\s*cabal install "Agda-'), _INSTALL),
    _exempt(PatternText(r"\bcabal build --only-dependencies\b"), _CACHE),
    _exempt(PatternText(r"^\s*mkdir -p ~/\.agda\b"), _INSTALL),
    _exempt(PatternText(r"^\s*rustup toolchain install\b"), _INSTALL),
    _exempt(PatternText(r"\bcpp/toolchain/install\.sh\b"), _INSTALL),
    _exempt(PatternText(r'^\s*echo "CCACHE_DIR='), _SETUP),
    _exempt(PatternText(r"^\s*ccache --(zero|show)-stats\b"), _CACHE),
    _exempt(PatternText(r"\bsudo apt-get\b"), _INSTALL),
    _exempt(PatternText(r"\bcpp/toolchain/apt_without_toolchain\.sh\b"), _INSTALL),
    _exempt(PatternText(r"^\s*curl -fsSL\b"), _INSTALL),
    _exempt(PatternText(r"^\s*go install github\.com/go-gremlins/"), _INSTALL),
    _exempt(PatternText(r"^\s*cargo install\b"), _INSTALL),
    _exempt(PatternText(r"\btools/build_mull\.sh\b"), _INSTALL),
    _exempt(PatternText(r'^\s*mkdir -p "\$\{HOME\}/\.local/bin"'), _INSTALL),
    _exempt(PatternText(r"\btools/mutation_ccache_evict\.sh\b"), _CACHE),
    _exempt(PatternText(r"\bpip install pyyaml\b"), _INSTALL),
    _exempt(PatternText(r"\bif \[ -f build/libaletheia-ffi\.so \]"), _CACHE),
    _exempt(PatternText(r'^\s*test "\$\{RESULT\}" = success$'), _TALLY),
    _exempt(PatternText(r"^\s*printf 'mutation lanes: "), _TALLY),
    _exempt(PatternText(r'^\s*if \[ -n "\$\{CLOSED_PR_NUMBER\}" \]'), _CACHE),
    _exempt(PatternText(r'^\s*case "\$\{BENCH\}" in$'), _SETUP),
    _exempt(PatternText(r"^\s*for f in benchmarks/results/\*_"), _LOG),
    _exempt(PatternText(r'^\s*echo "This diff moves no binding'), _LOG),
    _exempt(PatternText(r'^\s*mkdir -p "\$\{RUNNER_TEMP\}/(tarballs|release)"'), _SETUP),
    _exempt(PatternText(r'^\s*cd "\$\{RUNNER_TEMP\}/release"'), _RELEASE),
    _exempt(PatternText(r"-m tools\.bundle_(validate|c_example)\b"), _RELEASE),
    _exempt(PatternText(r"\bcabal run shake -- --keep-going packages\b"), _RELEASE),
    _exempt(PatternText(r"^\s*cosign verify-blob\b"), _RELEASE),
    _exempt(PatternText(r'^\s*work="\$\(mktemp -d\)"'), _RELEASE),
    _exempt(PatternText(r"^\s*shopt -s nullglob\b"), _RELEASE),
    _exempt(PatternText(r"^\s*sudo dpkg -i dist/"), _RELEASE),
    _exempt(PatternText(r'^\s*listing="\$\(rpm -qlp'), _RELEASE),
    _exempt(PatternText(r"^\s*docker build\b"), _RELEASE),
    _exempt(PatternText(r"^\s*assets=\("), _RELEASE),
    _exempt(PatternText(r'^\s*image="ghcr\.io/'), _RELEASE),
)


def declared_for(script: ScriptText) -> WorkflowStep | Prose:
    """Return the declaration of what ``script`` runs, or why it is refused."""
    watched = [step for step in WATCHED if step.names(script)]
    if len(watched) > 1:
        both = " and ".join(step.runs for step in watched)
        return Prose(f"the step runs more than one watched tool ({both}): split it")
    if watched:
        return watched[0]
    exempt = next((step for step in EXEMPT if step.names(script)), None)
    if exempt is None:
        first = next((line for line in script.splitlines() if line.strip()), "")
        return Prose(f"no declaration in tools/_workflow_steps.py names the step ({first.strip()})")
    return exempt
