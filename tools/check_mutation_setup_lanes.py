# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The mutation-setup gate's checks of each lane's own configuration, and the reading of its inputs.

``tools/check_mutation_setup.py`` runs these beside its checks of the record
and of the Python tests: that no lane's per-mutant run reaches its binding's
doc-example harness, that the Go lane turns on every mutator gremlins ships
off, and that the mutation build links the C++ library statically, its
invariants 6, 8 and 9, which its module docstring states.  A file any of the
gate's checks reads and cannot read, or TOML or CMake it cannot parse, stops
the gate with exit 2; a ``go/.gremlins.yaml`` gremlins' reader refuses is
invariant 8's own refusal.
"""

from __future__ import annotations

import collections
import datetime as dt
import fnmatch
import os
import re
import shlex
import sys
import tomllib
from pathlib import Path
from typing import Literal, NamedTuple, NewType, NoReturn, TypedDict, cast

import yaml
from cmakelang import lex

from tools.bundle_licences import mapping_keys, repeated_key
from tools.mutation_cpp import CPP_TEST_TARGET
from tools.mutation_go import GO_CONFIG
from tools.mutation_run import GO_DOC_HARNESS, GoFlags, go_sweep_goflags

from aletheia.common_types import Prose

REPO_ROOT = Path(__file__).resolve().parent.parent
PYPROJECT_PATH = REPO_ROOT / "python" / "pyproject.toml"

# The text of a file the gate reads.
FileText = NewType("FileText", str)


def exit_unreadable(path: Path, reason: Prose) -> NoReturn:
    """Stop the gate with exit 2, naming the input it cannot read and why."""
    _ = sys.stderr.write(f"ERROR: cannot read {path}: {reason}\n")
    sys.exit(2)


def read_or_exit(path: Path) -> FileText:
    """Return the text of ``path``, or stop the gate with exit 2 naming why there is none."""
    try:
        return FileText(path.read_text(encoding="utf-8"))
    except OSError as exc:
        exit_unreadable(path, Prose(exc.strerror or str(exc)))
    except UnicodeDecodeError as exc:
        exit_unreadable(path, Prose(str(exc)))


# What a TOML document holds at a key, as tomllib hands it back: a string, a
# number, a boolean, a date or time, an array or a table, nested without bound.
TomlString = NewType("TomlString", str)
TomlInteger = NewType("TomlInteger", int)
TomlFloat = NewType("TomlFloat", float)
type TomlValue = (
    TomlString
    | TomlInteger
    | TomlFloat
    | bool
    | dt.datetime
    | dt.date
    | dt.time
    | list[TomlValue]
    | dict[TomlString, TomlValue]
)
type TomlTable = dict[TomlString, TomlValue]


def toml_or_exit(path: Path) -> TomlTable:
    """Return the TOML document at ``path``, or stop the gate with exit 2."""
    try:
        return cast("TomlTable", tomllib.loads(read_or_exit(path)))
    except tomllib.TOMLDecodeError as exc:
        exit_unreadable(path, Prose(str(exc)))


def table_or_exit(path: Path, value: TomlValue, what: Prose) -> TomlTable:
    """Return ``value``, the entry ``what`` of ``path``, held to a table, or exit 2."""
    if not isinstance(value, dict):
        exit_unreadable(path, Prose(f"its {what} is not a mapping"))
    return value


def strings_or_exit(path: Path, value: TomlValue, what: Prose) -> list[TomlString]:
    """Return ``value``, the entry ``what`` of ``path``, held to a list of strings, or exit 2."""
    if not isinstance(value, list) or not all(isinstance(item, str) for item in value):
        exit_unreadable(path, Prose(f"its {what} is not a list of strings"))
    return cast("list[TomlString]", value)


# A file-name pattern as ``fnmatch`` reads it.
Glob = NewType("Glob", str)


def listed_or_exit(directory: Path, pattern: Glob) -> list[Path]:
    """Return the files of ``directory`` named like ``pattern``, sorted, or exit 2.

    A directory that cannot be listed stops the gate rather than listing
    nothing, which would pass every check of it.
    """
    try:
        entries = list(directory.iterdir())
    except OSError as exc:
        exit_unreadable(directory, Prose(exc.strerror or str(exc)))
    return sorted(entry for entry in entries if fnmatch.fnmatch(entry.name, pattern))


def walked_or_exit(directory: Path, pattern: Glob) -> list[Path]:
    """Return the files under ``directory`` named like ``pattern``, sorted, or exit 2."""

    def refuse(exc: OSError) -> NoReturn:
        exit_unreadable(Path(exc.filename or directory), Prose(exc.strerror or str(exc)))

    return sorted(
        Path(root, name)
        for root, _, names in os.walk(directory, onerror=refuse)
        for name in fnmatch.filter(names, pattern)
    )


# One argument of a command line the lane runs its tests with.
PytestArg = NewType("PytestArg", str)
# A test as its runner selects it by name.
TestName = NewType("TestName", str)

# Each binding's doc-example harness, as the lane that must not run it would
# name it; Go's is the runner's own ``GO_DOC_HARNESS``.
PYTHON_DOC_HARNESS = PytestArg("--markdown-docs")
RUST_DOC_HARNESS = TestName("every_rust_fence_of_the_listed_documents_builds_and_runs")
CPP_DOC_HARNESS = "tests/doc_example_tests.cpp"
# The tests that build the benchmark example with a cargo of their own and run
# it, every test of this file; the Rust lane skips them beside its harness.
RUST_PROGRAM_TESTS = REPO_ROOT / "rust" / "tests" / "benchmark_program.rs"

MUTANTS_TOML_PATH = REPO_ROOT / "rust" / ".cargo" / "mutants.toml"
CMAKE_PATH = REPO_ROOT / "cpp" / "CMakeLists.txt"

# A Go test as the go command finds one: a top-level function taking a
# ``*testing.T``, its parameter list on one line or broken across lines as
# gofmt keeps it, and named ``Test`` followed by no lowercase letter, which the
# check reading this filters for; ``TestMain`` takes a ``*testing.M``.
_GO_TEST_RE = re.compile(r"^func (Test\w*)\(\s*(?:\w+\s+)?\*testing\.T,?\s*\)", re.MULTILINE)
# The pattern of a ``-skip`` flag in GOFLAGS.
_GO_SKIP_RE = re.compile(r"(?:^|\s)-skip=(\S+)")
# A Rust test: a function under ``#[test]``, whatever attributes (their
# strings holding any character) or comment lines sit between; a ``const`` or
# ``extern`` fn is one too, as rustc lists them.
_RUST_TEST_RE = re.compile(
    r"#\[test\]\s*(?:#\[(?:[^\]\"]|\"[^\"]*\")*\]\s*|//[^\n]*\n\s*)*"
    + r"(?:pub(?:\([^)]*\))?\s+)?(?:const\s+|extern\s+\"[^\"]*\"\s+)?fn\s+(\w+)"
)

# A word of CMake source: a command's name, lowercased as CMake matches it, or
# an argument's value.
CMakeWord = NewType("CMakeWord", str)
# A mutator as gremlins' configuration names it.
GremlinsMutator = NewType("GremlinsMutator", str)


class _CMakeCommand(NamedTuple):
    """One command of a listfile, as CMake runs it."""

    name: CMakeWord
    args: tuple[CMakeWord, ...]


# The tokens between a command's parts, which CMake reads as no argument.
_CMAKE_SEPARATORS = frozenset(
    {
        lex.TokenType.WHITESPACE,
        lex.TokenType.NEWLINE,
        lex.TokenType.COMMENT,
        lex.TokenType.BRACKET_COMMENT,
        lex.TokenType.FORMAT_OFF,
        lex.TokenType.FORMAT_ON,
        lex.TokenType.BYTEORDER_MARK,
    }
)
# The commands that name a target's sources, its name the first argument.
_CMAKE_SOURCE_COMMANDS = frozenset({CMakeWord("add_executable"), CMakeWord("target_sources")})
# The commands that write a variable named by their first argument.
_CMAKE_VARIABLE_WRITES = frozenset({CMakeWord("set"), CMakeWord("unset")})
_LINKAGE = CMakeWord("ALETHEIA_CPP_LINKAGE")
# The mutation build's branch opening on the static form.
_STATIC_UNDER_MUTATION = (
    _CMakeCommand(CMakeWord("if"), (CMakeWord("ALETHEIA_MUTATION"),)),
    _CMakeCommand(CMakeWord("set"), (_LINKAGE, CMakeWord("STATIC"))),
)
_ELSE = _CMakeCommand(CMakeWord("else"), ())
# The library taking its link form from the variable.
# What cmakelang hands back where CMake stops with a parse error: a quote or a
# bracket argument opened and never closed is an unquoted literal spelled with
# its opening, a bracket comment never closed a line comment spelled with its.
_UNCLOSED = {
    lex.TokenType.UNQUOTED_LITERAL: re.compile(r'^(?:"|\[=*\[)'),
    lex.TokenType.COMMENT: re.compile(r"^#\[=*\["),
}
_LIBRARY_TAKES_THE_FORM = (CMakeWord("aletheia-cpp"), CMakeWord("${ALETHEIA_CPP_LINKAGE}"))

# The mutators gremlins ships off, each of which the Go lane turns on.
GO_DEFAULT_OFF_MUTATORS = (
    GremlinsMutator("invert-assignments"),
    GremlinsMutator("invert-bitwise"),
    GremlinsMutator("invert-bwassign"),
    GremlinsMutator("invert-logical"),
    GremlinsMutator("invert-loopctrl"),
    GremlinsMutator("remove-self-assignments"),
)


class _MutatorSwitch(TypedDict, total=False):
    enabled: bool


# What gremlins reads of its configuration; a level that is not the mapping
# it reads is held as None, and the gate tests every level for a mapping.
class _GremlinsConfig(TypedDict, total=False):
    mutants: dict[GremlinsMutator, _MutatorSwitch | None] | None


# PyYAML's safe loader reading a boolean as gremlins does: PyYAML reads YAML
# 1.1, where ``yes`` and ``on`` are booleans too, and gremlins YAML 1.2, where
# they are strings, so the bool resolver takes 1.2's spellings alone, and an
# explicit ``!!bool`` of any other spelling is refused, as gremlins' reader
# refuses it.  Built with ``type()`` so it does not inherit ``SafeLoader``'s
# ancestry into a flagged ``too-many-ancestors``; the fresh table leaves the
# parent's untouched, as ``add_constructor`` copies the parent's before adding.
_YAML_BOOL_TAG = "tag:yaml.org,2002:bool"
_YAML12_BOOL_RE = re.compile(r"^(?:true|True|TRUE|false|False|FALSE)$")
_GremlinsLoader: type[yaml.SafeLoader] = type(
    "_GremlinsLoader",
    (yaml.SafeLoader,),
    {
        "yaml_implicit_resolvers": {
            first: [
                (tag, _YAML12_BOOL_RE if tag == _YAML_BOOL_TAG else pattern)
                for tag, pattern in resolvers
            ]
            for first, resolvers in yaml.SafeLoader.yaml_implicit_resolvers.items()
        }
    },
)


def _construct_yaml12_bool(loader: yaml.SafeLoader, node: yaml.Node) -> bool:
    """Read a boolean as YAML 1.2 spells one, refusing any other spelling."""
    text = loader.construct_scalar(node)
    if not _YAML12_BOOL_RE.match(text):
        raise yaml.MarkedYAMLError(
            problem=f"{text!r} is no YAML 1.2 boolean", problem_mark=node.start_mark
        )
    return text.lower() == "true"


_GremlinsLoader.add_constructor(_YAML_BOOL_TAG, _construct_yaml12_bool)


def _entry(table: TomlTable, key: TomlString, absent: TomlValue) -> TomlValue:
    """Return the entry ``key`` of ``table``, or ``absent`` where it has none."""
    return table.get(key, absent)


def python_lane_runs_no_doc_harness() -> list[Prose]:
    """Refuse the fence-collecting option among the arguments mutmut runs pytest with.

    mutmut runs pytest with its own arguments and the project's ``addopts``;
    the harness is the run-ci step that passes the option, found there first.
    """
    if f'"{PYTHON_DOC_HARNESS}"' not in str(read_or_exit(REPO_ROOT / "tools" / "_ci_steps.py")):
        return [
            Prose(
                f"[python/doc-harness] tools/_ci_steps.py passes no {PYTHON_DOC_HARNESS}: the "
                + "harness is spelled another way now, and this check would name nothing"
            )
        ]
    tool = table_or_exit(
        PYPROJECT_PATH, _entry(toml_or_exit(PYPROJECT_PATH), TomlString("tool"), {}), Prose("tool")
    )
    mutmut = table_or_exit(
        PYPROJECT_PATH, _entry(tool, TomlString("mutmut"), {}), Prose("tool.mutmut")
    )
    pytest_tool = table_or_exit(
        PYPROJECT_PATH, _entry(tool, TomlString("pytest"), {}), Prose("tool.pytest")
    )
    ini = table_or_exit(
        PYPROJECT_PATH,
        _entry(pytest_tool, TomlString("ini_options"), {}),
        Prose("tool.pytest.ini_options"),
    )
    addopts = _entry(ini, TomlString("addopts"), [])
    runs = [
        *strings_or_exit(
            PYPROJECT_PATH,
            _entry(mutmut, TomlString("pytest_add_cli_args"), []),
            Prose("tool.mutmut.pytest_add_cli_args"),
        ),
        *strings_or_exit(
            PYPROJECT_PATH,
            _entry(mutmut, TomlString("pytest_add_cli_args_test_selection"), []),
            Prose("tool.mutmut.pytest_add_cli_args_test_selection"),
        ),
        # pytest reads its ini value as one string too, split as a shell splits it.
        *(
            shlex.split(addopts)
            if isinstance(addopts, str)
            else strings_or_exit(PYPROJECT_PATH, addopts, Prose("tool.pytest.ini_options.addopts"))
        ),
    ]
    if PYTHON_DOC_HARNESS in runs:
        return [
            Prose(
                f"[python/doc-harness] mutmut runs pytest with {PYTHON_DOC_HARNESS}, so every "
                + "mutant's run collects the documents' fences, which no mutant reaches"
            )
        ]
    return []


def go_lane_runs_no_doc_harness() -> list[Prose]:
    """Hold the Go lane's ``-skip`` to the doc-example harness and nothing else.

    The flag is read from the ``GOFLAGS`` the runner gives gremlins, the last
    ``-skip`` being the one go keeps, and matched as go matches a top-level
    test, unanchored; Python's ``re`` under ``re.ASCII`` reads the pattern's
    anchors and word characters as RE2 does.
    """
    names = [
        TestName(match.group(1))
        for path in listed_or_exit(REPO_ROOT / "go" / "aletheia", Glob("*_test.go"))
        for match in _GO_TEST_RE.finditer(read_or_exit(path))
        if not match.group(1)[4:5].islower()
    ]
    skips = [match.group(1) for match in _GO_SKIP_RE.finditer(go_sweep_goflags(GoFlags("")))]
    if not skips:
        return [
            Prose(
                "[go/doc-harness] the GOFLAGS the runner gives gremlins carry no -skip, so "
                + f"every mutant's run reaches {GO_DOC_HARNESS}"
            )
        ]
    pattern = re.compile(skips[-1], re.ASCII)
    skipped = [name for name in names if pattern.search(name)]
    return _skips_the_harness_alone("go", TestName(GO_DOC_HARNESS), names, skipped)


def rust_lane_runs_no_doc_harness() -> list[Prose]:
    """Hold the Rust lane's ``--skip`` filters to the harness and the program's tests alone.

    cargo-mutants appends the configuration's test arguments to ``cargo
    test``, where those after ``--`` reach the test binaries, an example's
    tests among them; libtest skips a test whose module path contains a
    filter, or equals it under ``--exact``.  The tests are read by bare name,
    so a filter naming a path is refused rather than matched.
    """
    args = strings_or_exit(
        MUTANTS_TOML_PATH,
        _entry(toml_or_exit(MUTANTS_TOML_PATH), TomlString("additional_cargo_test_args"), []),
        Prose("additional_cargo_test_args"),
    )
    binary_args = args[args.index(TomlString("--")) + 1 :] if "--" in args else []
    filters = [
        arg.removeprefix("--skip=")
        for i, arg in enumerate(binary_args)
        if arg.startswith("--skip=") or (i > 0 and binary_args[i - 1] == "--skip")
    ]
    if pathed := [f for f in filters if "::" in f]:
        return [
            Prose(
                f"[rust/doc-harness] the lane's skip names {f!r}, a path libtest matches against "
                + "a test's module path, which this gate reads by bare name: name the test alone"
            )
            for f in pathed
        ]
    exact = "--exact" in binary_args
    names = [
        TestName(match.group(1))
        for directory in ("src", "tests", "examples")
        for path in walked_or_exit(REPO_ROOT / "rust" / directory, Glob("*.rs"))
        for match in _RUST_TEST_RE.finditer(read_or_exit(path))
    ]
    skipped = [name for name in names if any(name == f if exact else f in name for f in filters)]
    program = [
        TestName(match.group(1))
        for match in _RUST_TEST_RE.finditer(read_or_exit(RUST_PROGRAM_TESTS))
    ]
    return [
        *_skips_the_harness_alone(
            "rust", RUST_DOC_HARNESS, names, [name for name in skipped if name not in program]
        ),
        *(
            Prose(
                f"[rust/program-tests] every mutant's run reaches {name}, which builds the "
                + "benchmark example with a cargo of its own: the lane's skip does not match it"
            )
            for name in program
            if name not in skipped
        ),
    ]


def _skips_the_harness_alone(
    binding: Literal["go", "rust"],
    harness: TestName,
    names: list[TestName],
    skipped: list[TestName],
) -> list[Prose]:
    """Say why a lane's skip does not drop the harness alone from the tests it runs, or nothing."""
    defined = names.count(harness)
    if defined != 1:
        return [
            Prose(
                f"[{binding}/doc-harness] {harness} is defined {defined} times among the "
                + "binding's tests rather than once: the harness was renamed or duplicated, "
                + "and the lane's skip is checked against a name the tree does not settle"
            )
        ]
    failures: list[Prose] = []
    if harness not in skipped:
        failures.append(
            Prose(
                f"[{binding}/doc-harness] every mutant's run reaches {harness}: the lane's "
                + "skip does not match it"
            )
        )
    failures += [
        Prose(
            f"[{binding}/doc-harness] the lane's skip also drops {name}, which is not the "
            + "doc-example harness, so no mutant is tested against it"
        )
        for name in sorted(set(skipped) - {harness})
    ]
    return failures


def cpp_lane_runs_no_doc_harness() -> list[Prose]:
    """Refuse the doc-example harness's source among those of the binary the Mull runner runs.

    Every ``add_executable`` and ``target_sources`` of ``cpp/CMakeLists.txt``
    is read, so a source folded into the test binary under the mutation build
    counts as the unconditional ones do.  The file is read as written: a
    source of the test binary, or a target compiling the harness, spelled
    through a variable reference or a generator expression is refused, since
    what CMake evaluates it to is not read here.
    """
    sources: dict[CMakeWord, list[CMakeWord]] = collections.defaultdict(list)
    for command in _cmake_commands():
        if command.name in _CMAKE_SOURCE_COMMANDS and command.args:
            target, *rest = command.args
            sources[target] += rest
    unread = [
        *(
            Prose(
                f"[cpp/doc-harness] {CPP_TEST_TARGET} takes {word}, a source this gate reads as "
                + "written and CMake evaluates: name its files"
            )
            for word in sorted(set(sources.get(CMakeWord(CPP_TEST_TARGET), [])))
            if "$" in word
        ),
        *(
            Prose(
                f"[cpp/doc-harness] {target}, a target this gate reads as written and CMake "
                + f"evaluates, compiles {CPP_DOC_HARNESS}: name the target"
            )
            for target, words in sorted(sources.items())
            if "$" in target and CPP_DOC_HARNESS in words
        ),
    ]
    if unread:
        return unread
    building = sorted(target for target, words in sources.items() if CPP_DOC_HARNESS in words)
    if not building:
        return [
            Prose(
                f"[cpp/doc-harness] no target of cpp/CMakeLists.txt compiles {CPP_DOC_HARNESS}: "
                + "the harness moved, and this check would name nothing"
            )
        ]
    if CPP_TEST_TARGET in building:
        return [
            Prose(
                f"[cpp/doc-harness] {CPP_TEST_TARGET}, the binary the Mull runner runs once per "
                + f"mutant, compiles {CPP_DOC_HARNESS}"
            )
        ]
    return []


def _cmake_commands() -> list[_CMakeCommand]:
    """Return the commands of ``cpp/CMakeLists.txt``, read with cmakelang's lexer.

    The lexer tells a ``#`` that opens a comment from one inside a quoted or a
    bracket argument, and a bracket comment, which may span lines, from the
    code around it; it refuses nothing, so a literal, a comment or a command
    left open, which CMake refuses, stops the gate with exit 2 here.  A
    ``cmake_language(CALL <command> ...)`` is read as the command it invokes.
    """
    all_tokens = lex.tokenize(read_or_exit(CMAKE_PATH))
    if unclosed := [
        token
        for token in all_tokens
        if (opening := _UNCLOSED.get(token.type)) is not None and opening.match(token.spelling)
    ]:
        exit_unreadable(CMAKE_PATH, Prose(f"{unclosed[0].spelling[:12]!r} opens what never closes"))
    tokens = [token for token in all_tokens if token.type not in _CMAKE_SEPARATORS]
    commands: list[_CMakeCommand] = []
    at = 0
    while at + 1 < len(tokens):
        if tokens[at].type is not lex.TokenType.WORD or (
            tokens[at + 1].type is not lex.TokenType.LEFT_PAREN
        ):
            at += 1
            continue
        name, depth, args = CMakeWord(tokens[at].spelling.lower()), 1, list[CMakeWord]()
        at += 2
        while at < len(tokens) and depth:
            token = tokens[at]
            if token.type is lex.TokenType.LEFT_PAREN:
                depth += 1
            elif token.type is lex.TokenType.RIGHT_PAREN:
                depth -= 1
            if depth:
                args.append(_cmake_value(token))
            at += 1
        if depth:
            exit_unreadable(CMAKE_PATH, Prose(f"{name}( is missing its closing parenthesis"))
        if name == "cmake_language" and args[:1] == ["CALL"] and len(args) > 1:
            name, args = CMakeWord(args[1].lower()), args[2:]
        commands.append(_CMakeCommand(name, tuple(args)))
    return commands


def _cmake_value(token: lex.Token) -> CMakeWord:
    """Return one argument's text as this gate reads it.

    A quoted argument's is its text within the quotes, a backslash ending a
    line dropped with the newline as CMake drops it; a bracket argument's its
    content; any other's as written, a variable reference or an escape left
    unevaluated.
    """
    if token.type is lex.TokenType.QUOTED_LITERAL:
        return CMakeWord(token.spelling[1:-1].replace("\\\n", ""))
    if token.type is lex.TokenType.BRACKET_ARGUMENT:
        return CMakeWord(lex.parse_bracket_argument(token.spelling)[1])
    return CMakeWord(token.spelling)


def go_lane_turns_on_the_default_off_mutators() -> list[Prose]:
    """Hold ``go/.gremlins.yaml`` to ``enabled: true`` under each mutator gremlins ships off.

    The file is read as gremlins reads it.  Its YAML reader reads the first
    document and leaves any other unread; it refuses a repeated key or a
    boolean YAML 1.2 does not spell, and gremlins, named the file, then stops
    before it sweeps; it lowercases every key, so a key with a capital can stand
    in for the one this gate reads; and it asserts the value's type, so a
    quoted ``"true"``, or a ``yes`` or an ``on`` that PyYAML would read as
    true, leaves the kind off.  The switch is read nested under ``mutants:``,
    the form the file spells; gremlins' reader also resolves a dotted key
    naming the whole path, which this gate does not.
    """
    text = read_or_exit(REPO_ROOT / GO_CONFIG)
    try:
        node = _gremlins_node(text)
        config = _gremlins_config(text)
    except yaml.YAMLError as exc:
        return [
            Prose(
                f"[go/mutators] {GO_CONFIG} is no YAML gremlins reads "
                + f"({' '.join(str(exc).split())}), so the lane's gremlins stops before it "
                + "sweeps"
            )
        ]
    keys = mapping_keys(node)
    repeated = repeated_key(keys)
    if repeated is not None:
        return [
            Prose(
                f"[go/mutators] {GO_CONFIG} repeats the key {repeated!r}, which gremlins' "
                + "YAML reader refuses, so the lane's gremlins stops before it sweeps"
            )
        ]
    capitalised = [key for mapping in keys for key in mapping if key != key.lower()]
    if capitalised:
        return [
            Prose(
                f"[go/mutators] {GO_CONFIG} holds the key {key!r}: gremlins reads every key "
                + "lowercased, so a key with a capital stands in for the one this gate reads"
            )
            for key in capitalised
        ]
    mutants = config.get("mutants") if isinstance(config, dict) else None
    switches = mutants if isinstance(mutants, dict) else {}
    return [
        Prose(
            f"[go/mutators] {GO_CONFIG} does not set `enabled: true` under mutants.{name} in "
            + "the nested form this gate reads; gremlins ships the kind off, and only the "
            + "lane's recorded generated count shows what it made"
        )
        for name in GO_DEFAULT_OFF_MUTATORS
        if not _turned_on(switches.get(name))
    ]


def _gremlins_node(text: FileText) -> yaml.Node | None:
    """Compose the first document of ``text`` as gremlins' reader would, keys and all."""
    loader = _GremlinsLoader(text)
    try:
        return loader.get_node() if loader.check_node() else None
    finally:
        loader.dispose()


def _gremlins_config(text: FileText) -> _GremlinsConfig | None:
    """Construct the first document of ``text`` as gremlins' reader would; no mapping is None."""
    loader = _GremlinsLoader(text)
    try:
        return cast("_GremlinsConfig | None", loader.get_data() if loader.check_data() else None)
    finally:
        loader.dispose()


def _turned_on(switch: _MutatorSwitch | None) -> bool:
    """Say whether one mutator's block sets ``enabled`` to the boolean true."""
    return isinstance(switch, dict) and switch.get("enabled") is True


def cpp_lane_links_the_library_statically() -> list[Prose]:
    """Hold the mutation build to the static form of the C++ library.

    The Mull runner finds mutants in the test executable, which a shared
    library keeps most of them out of.  The variable is written by the
    branch's first command and by the first of an ``else()`` that follows it,
    and nowhere else, so nothing after the branch can undo the static form.
    """
    commands = _cmake_commands()
    opens = [
        at for at in range(len(commands)) if tuple(commands[at : at + 2]) == _STATIC_UNDER_MUTATION
    ]
    failures: list[Prose] = []
    if not opens:
        failures.append(
            Prose(
                "[cpp/linkage] cpp/CMakeLists.txt does not open if(ALETHEIA_MUTATION) with "
                + "set(ALETHEIA_CPP_LINKAGE STATIC), so the Mull runner sees the library's "
                + "mutants through a shared library, which hides most of them"
            )
        )
    else:
        kept = {opens[0] + 1}
        if commands[opens[0] + 2 : opens[0] + 3] == [_ELSE]:
            kept.add(opens[0] + 3)
        others = [
            at
            for at, command in enumerate(commands)
            if command.name in _CMAKE_VARIABLE_WRITES
            and command.args[:1] == (_LINKAGE,)
            and at not in kept
        ]
        if others:
            failures.append(
                Prose(
                    "[cpp/linkage] cpp/CMakeLists.txt writes ALETHEIA_CPP_LINKAGE in "
                    + f"{len(others)} command(s) beside the if(ALETHEIA_MUTATION) branch's "
                    + "first and the else() that follows it, so the mutation build can end on "
                    + "another form"
                )
            )
    if not any(
        command.name == "add_library" and command.args[:2] == _LIBRARY_TAKES_THE_FORM
        for command in commands
    ):
        failures.append(
            Prose(
                "[cpp/linkage] cpp/CMakeLists.txt does not build aletheia-cpp as "
                + "${ALETHEIA_CPP_LINKAGE}, so the mutation build's link form does not reach it"
            )
        )
    return failures
