# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The Mull plugin gate reads each compile's ending and IR as the fact, a refusal, or no answer.

``tools/check_mull_plugin_facts.py`` compiles under the plugin to show three
facts the mutation build rests on.  The compiles are replaced here by answers
the test writes, the IR among them, so how each ending and each line of IR is
read is held without a compiler.  The IR planted is what the plugin emitted
for the two units, its home path replaced; each refusal is a corruption of it.
"""

from __future__ import annotations

import json
import subprocess
from pathlib import Path
from typing import TYPE_CHECKING, NamedTuple, NewType

import pytest
from _processes import CommandWord

from tools import check_mull_plugin_facts
from tools._common import RelPath
from tools.check_mull_plugin_facts import (
    COMPILE_DATABASE,
    IDENTIFIERS_UNIT,
    REACH_UNIT,
    CommandLine,
    CompileArg,
    CompileEntry,
    DirectoryName,
    Finding,
    FunctionName,
    IrText,
    LineNumber,
    MutantId,
    MutatorName,
    SourceText,
    ToolOutput,
    check,
    identifier_findings,
    identifier_owners,
    ir_command,
    mutant_sites,
    prefix_map_verdict,
    reach_findings,
    verdict,
)

from aletheia.common_types import ExitStatus, Prose

if TYPE_CHECKING:
    from collections.abc import Iterable, Mapping

    from tools.check_mull_plugin_facts import UnitName
    from tools.pin_scope import PinGate

# The name and the value of one variable of a child's environment.
EnvName = NewType("EnvName", str)
EnvValue = NewType("EnvValue", str)

_GATE = "check-mull-plugin-facts"
# An IR compile that ended well, and the tree the gate reads first.
_EMITTED = ExitStatus(0)
_WHOLE_TREE = RelPath("cpp/build-mutation")
_SRC = "/repo/cpp/src"

# The function of json_parse.cpp whose body stores three identifiers, and those identifiers.
_JSON_FUNCTION = FunctionName(
    "_ZN8aletheia6detailL15make_json_errorENS_9ErrorKindERKN8nlohmann16json_abi_v3_12_010basic_"
    + "jsonINSt7__debug3mapENS5_6vectorENSt7__cxx1112basic_stringIcSt11char_traitsIcESaIcEEEblmdSa"
    + "NS3_14adl_serializerENS7_IhSaIhEEEvEE"
)
_JSON_IDS = (
    MutantId(f"cxx_assign_const:{_SRC}/json_parse.cpp:230:24:230:25:dfcc2ad4.0"),
    MutantId(f"cxx_eq_to_ne:{_SRC}/json_parse.cpp:226:14:226:16:dfcc2ad4.0"),
    MutantId(f"cxx_eq_to_ne:{_SRC}/json_parse.cpp:229:14:229:16:dfcc2ad4.0"),
)
# A reader template instantiated at one width, storing a negation mutant of a header.
_READER_FUNCTION = FunctionName("_ZN8aletheia6detail11require_intIlEET_RKN8nlohmann16json_abi_v3")
_HEADER_ID = MutantId(f"negate_mutator:{_SRC}/detail/json_parse_helpers.hpp:81:10:81:10:81f81dd4.0")

# The backend's functions and the identifiers their bodies store: the three
# calls through function pointers, and a negation in the constructor.
_CLOSE = FunctionName("_ZN8aletheia12_GLOBAL__N_110FfiBackend5closeEPv")
_PROCESS = FunctionName(
    "_ZN8aletheia12_GLOBAL__N_110FfiBackend7processB5cxx11ERKNS_12BackendStateE"
)
_BUILD = FunctionName(
    "_ZN8aletheia12_GLOBAL__N_110FfiBackend15build_frame_binERKNS_12BackendStateE"
)
_CONSTRUCT = FunctionName(
    "_ZN8aletheia12_GLOBAL__N_110FfiBackendC2ERKNSt10filesystem7__cxx114pathEi"
)
_VOID_CALL = MutantId(f"cxx_remove_void_call:{_SRC}/ffi_backend.cpp:445:40:445:56:75e3e9f6.0")
_SCALAR_CALL = MutantId(f"cxx_replace_scalar_call:{_SRC}/ffi_backend.cpp:391:29:391:84:9b675964.0")
_POINTER_CALL = MutantId(
    f"cxx_replace_pointer_call_null:{_SRC}/ffi_backend.cpp:321:32:321:63:395a81f.0"
)
_NEGATION = MutantId(f"negate_mutator:{_SRC}/ffi_backend.cpp:275:18:275:14:b4ffc941.0")

# The first identifier with its seventh part, the hash and the ordinal, stripped.
_STRIPPED = MutantId(f"cxx_assign_const:{_SRC}/json_parse.cpp:230:24:230:25")

_CLOSE_LINE = LineNumber(445)
_BUILD_LINE = LineNumber(391)
_PROCESS_LINE = LineNumber(321)


def _body(name: FunctionName, identifiers: Iterable[MutantId]) -> IrText:
    """Return one function's IR as the plugin emits it: a define, the stores, the close."""
    stores = "".join(
        f'  store ptr @"{identifier}", ptr %4, align 8\n' for identifier in identifiers
    )
    return IrText(
        f"define internal void @{name}(ptr dead_on_unwind noalias writable"
        + f' sret(%"class.std::expected") align 8 %0, ptr %1) #0 {{\n{stores}  ret void\n}}\n'
    )


def _json_ir(*bodies: IrText) -> IrText:
    """Return the reader unit's IR: the error builder's body, a reader's, then any other."""
    return IrText(
        _body(_JSON_FUNCTION, _JSON_IDS) + _body(_READER_FUNCTION, [_HEADER_ID]) + "".join(bodies)
    )


def _backend_ir(*, void_call: bool = True) -> IrText:
    """Return the backend's IR, the void-call mutant on the close line dropped on request."""
    return IrText(
        _body(_CONSTRUCT, [_NEGATION])
        + _body(_PROCESS, [_POINTER_CALL])
        + _body(_BUILD, [_SCALAR_CALL])
        + _body(_CLOSE, [_VOID_CALL] if void_call else [])
    )


def _backend_source(*, close_call: bool = True) -> SourceText:
    """Return a backend source whose three calls stand on the lines the IR names."""
    lines = [""] * _CLOSE_LINE
    lines[_PROCESS_LINE - 1] = (
        "        return wrap_str_result(fns_.process(state.get(), &text), m);"
    )
    lines[_BUILD_LINE - 1] = (
        "        auto const status = fns_.build_frame_bin(state.get(), &frame);"
    )
    if close_call:
        lines[_CLOSE_LINE - 1] = (
            "    void close(void* state) noexcept override { fns_.close(state); }"
        )
    return SourceText("\n".join(lines))


@pytest.mark.parametrize(
    ("status", "output", "read"),
    [
        (ExitStatus(139), ToolOutput(""), ExitStatus(0)),
        (ExitStatus(-11), ToolOutput(""), ExitStatus(0)),
        (ExitStatus(1), ToolOutput("clang: error: ... (exit code 139)\n"), ExitStatus(0)),
        (ExitStatus(0), ToolOutput(""), ExitStatus(1)),
        (ExitStatus(1), ToolOutput("fatal error: 'x.hpp' file not found\n"), ExitStatus(2)),
        (ExitStatus(-6), ToolOutput(""), ExitStatus(2)),
    ],
)
def test_the_prefix_map_compile_s_ending_is_the_verdict(
    status: ExitStatus, output: ToolOutput, read: ExitStatus
) -> None:
    """The compiler's SIGSEGV by any route is the fact; success refuses; the rest is no answer."""
    assert prefix_map_verdict(status, output) == read


def test_every_identifier_is_mapped_to_the_function_storing_it() -> None:
    """A store inside a body belongs to its function; one outside any body belongs to none."""
    stray = IrText(f'store ptr @"{_VOID_CALL}", ptr %4, align 8\n')
    owners = identifier_owners(IrText(stray + _json_ir()))
    assert owners == {
        _JSON_IDS[0]: frozenset({_JSON_FUNCTION}),
        _JSON_IDS[1]: frozenset({_JSON_FUNCTION}),
        _JSON_IDS[2]: frozenset({_JSON_FUNCTION}),
    }


def test_identifiers_each_in_shape_and_stored_once_pass() -> None:
    """The plugin's own identifiers carry their seventh part and have one trampoline each."""
    assert not identifier_findings(identifier_owners(_json_ir()))


def test_an_identifier_without_its_seventh_part_refuses() -> None:
    """Stripping the hash and ordinal from an identifier is the refusal the shape holds."""
    owners = identifier_owners(_body(_JSON_FUNCTION, [_STRIPPED, _JSON_IDS[1]]))
    assert identifier_findings(owners) == [
        Finding(ExitStatus(1), Prose(f"no seventh part: {_STRIPPED}"))
    ]


def test_an_identifier_two_trampolines_store_refuses() -> None:
    """One identifier stored under a second define names two clones."""
    owners = identifier_owners(_json_ir(_body(_READER_FUNCTION, [_JSON_IDS[1]])))
    assert identifier_findings(owners) == [
        Finding(ExitStatus(1), Prose(f"shared by 2 trampolines: {_JSON_IDS[1]}"))
    ]


def test_ir_holding_no_identifier_is_no_answer() -> None:
    """A unit the plugin left unmutated shows nothing about the identifiers' shape."""
    assert identifier_findings(identifier_owners(_body(_JSON_FUNCTION, []))) == [
        Finding(ExitStatus(2), Prose("no mutant identifier in the IR of cpp/src/json_parse.cpp"))
    ]


def test_mutant_sites_are_read_for_one_unit() -> None:
    """Every store naming the unit gives its mutator and line; a header's store is left out."""
    assert mutant_sites(IrText(_backend_ir() + _json_ir()), REACH_UNIT) == {
        (MutatorName("cxx_remove_void_call"), _CLOSE_LINE),
        (MutatorName("cxx_replace_scalar_call"), _BUILD_LINE),
        (MutatorName("cxx_replace_pointer_call_null"), _PROCESS_LINE),
        (MutatorName("negate_mutator"), LineNumber(275)),
    }


def test_the_call_mutators_reaching_their_lines_pass() -> None:
    """Each named mutator with a mutant on its line is the fact."""
    assert not reach_findings(mutant_sites(_backend_ir(), REACH_UNIT), _backend_source())


def test_a_call_a_mutator_does_not_reach_refuses() -> None:
    """Dropping the void-call store is the refusal: the line exists and no mutant stands on it."""
    sites = mutant_sites(_backend_ir(void_call=False), REACH_UNIT)
    assert reach_findings(sites, _backend_source()) == [
        Finding(
            ExitStatus(1),
            Prose("no cxx_remove_void_call mutant on line(s) [445] of cpp/src/ffi_backend.cpp"),
        )
    ]


def test_a_line_the_fact_names_that_no_longer_exists_is_no_answer() -> None:
    """A pattern matching no source line is the gate's own staleness, never a refusal."""
    sites = mutant_sites(_backend_ir(), REACH_UNIT)
    assert reach_findings(sites, _backend_source(close_call=False)) == [
        Finding(
            ExitStatus(2), Prose(r"no line of cpp/src/ffi_backend.cpp matches fns_\.close\(state\)")
        )
    ]


def test_the_ir_command_drops_the_object_and_asks_for_ir(tmp_path: Path) -> None:
    """The entry's output and ``-c`` go; ``-S -emit-llvm -o <ir>`` is appended."""
    entry = CompileEntry(
        directory=DirectoryName("/repo/cpp/build-mutation"),
        file=RelPath("/repo/cpp/src/json_parse.cpp"),
        command=CommandLine(
            "/usr/bin/clang++-23 -I/repo/cpp/include -g -O0 -o CMakeFiles/x.o"
            + " -c /repo/cpp/src/json_parse.cpp"
        ),
    )
    assert ir_command(entry, tmp_path / "unit.ll") == [
        CompileArg("/usr/bin/clang++-23"),
        CompileArg("-I/repo/cpp/include"),
        CompileArg("-g"),
        CompileArg("-O0"),
        CompileArg("/repo/cpp/src/json_parse.cpp"),
        CompileArg("-S"),
        CompileArg("-emit-llvm"),
        CompileArg("-o"),
        CompileArg(str(tmp_path / "unit.ll")),
    ]


@pytest.mark.parametrize(
    ("statuses", "read"),
    [
        ((), ExitStatus(0)),
        ((ExitStatus(2),), ExitStatus(2)),
        ((ExitStatus(2), ExitStatus(1)), ExitStatus(1)),
    ],
)
def test_a_refusal_outranks_no_answer(statuses: tuple[ExitStatus, ...], read: ExitStatus) -> None:
    """The gate exits 1 on any refusal, 2 on any fact it could not reach, else 0."""
    assert verdict(Finding(status, Prose("")) for status in statuses) == read


class _Call(NamedTuple):
    """One compile the gate asked for: its words, where it ran, and the configuration it named."""

    cmd: list[CommandWord]
    cwd: Path | None
    mull_config: EnvValue | None


def _toolchain(monkeypatch: pytest.MonkeyPatch, tmp_path: Path, *, plugin: bool = True) -> Path:
    """Answer that clang is on PATH and the plugin installed, or not; return the plugin's path."""
    plugin_file = tmp_path / "mull-ir-frontend-23"
    if plugin:
        _ = plugin_file.write_text("", encoding="utf-8")

    def clang(name: CommandWord) -> CommandWord:
        assert name == "clang++-23"
        return CommandWord("/usr/bin/clang++-23")

    def installed() -> Path:
        return plugin_file

    monkeypatch.setattr(check_mull_plugin_facts, "find_executable", clang)
    monkeypatch.setattr(check_mull_plugin_facts, "plugin_path", installed)
    return plugin_file


def _answers(
    monkeypatch: pytest.MonkeyPatch,
    *,
    prefix_map: ExitStatus,
    ir: Mapping[UnitName, IrText],
    ir_status: ExitStatus = _EMITTED,
) -> list[_Call]:
    """Answer the prefix-map compile with ``prefix_map`` and each IR compile by writing ``ir``."""
    asked: list[_Call] = []

    def answer(
        cmd: list[CommandWord],
        *,
        cwd: Path | None = None,
        env: Mapping[EnvName, EnvValue] | None = None,
    ) -> subprocess.CompletedProcess[Prose]:
        asked.append(_Call(cmd, cwd, None if env is None else env.get(EnvName("MULL_CONFIG"))))
        if "-emit-llvm" not in cmd:
            return subprocess.CompletedProcess(cmd, prefix_map, Prose(""), Prose("crashed\n"))
        unit = next(name for name in ir if cmd[-5].endswith(f"/cpp/src/{name}"))
        if ir_status == 0:
            _ = Path(cmd[-1]).write_text(ir[unit], encoding="utf-8")
        return subprocess.CompletedProcess(cmd, ir_status, Prose("out "), Prose("said\n"))

    monkeypatch.setattr(check_mull_plugin_facts, "run_capture", answer)
    return asked


def _repository(
    tmp_path: Path,
    *,
    tree: RelPath = _WHOLE_TREE,
    units: Iterable[UnitName] = (IDENTIFIERS_UNIT, REACH_UNIT),
) -> Path:
    """Return a repository with one configured tree naming ``units`` and the backend's source."""
    root = tmp_path / "repo"
    (root / tree).mkdir(parents=True)
    entries = [
        {
            "directory": str(root / tree),
            "file": str(root / "cpp" / "src" / unit),
            "command": f"/usr/bin/clang++-23 -g -O0 -o CMakeFiles/x.o -c {root}/cpp/src/{unit}",
        }
        for unit in units
    ]
    _ = (root / tree / COMPILE_DATABASE).write_text(json.dumps(entries), encoding="utf-8")
    (root / "cpp" / "src").mkdir(parents=True)
    _ = (root / "cpp" / "src" / REACH_UNIT).write_text(_backend_source(), encoding="utf-8")
    return root


def _ir() -> dict[UnitName, IrText]:
    """Return the IR the plugin emits for both units, as the gate expects it."""
    return {IDENTIFIERS_UNIT: _json_ir(), REACH_UNIT: _backend_ir()}


def test_every_fact_holding_passes_silently(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """Three compiles, each answered as the fact, print nothing and pass."""
    plugin = _toolchain(monkeypatch, tmp_path)
    root = _repository(tmp_path)
    asked = _answers(monkeypatch, prefix_map=ExitStatus(139), ir=_ir())
    assert check(root) == ExitStatus(0)
    assert capsys.readouterr().out == ""
    assert len(asked) == 3
    prefix_map, identifiers, reach = asked[0], asked[1], asked[2]
    assert prefix_map.cmd[:6] == [
        "/usr/bin/clang++-23",
        "-std=c++23",
        f"-fpass-plugin={plugin}",
        "-g",
        "-O0",
        f"-ffile-prefix-map={root}=.",
    ]
    assert prefix_map.cwd is not None
    assert prefix_map.cmd[6] == f"-fcrash-diagnostics-dir={prefix_map.cwd}"
    assert prefix_map.cwd.name.startswith("mull-plugin-facts-")
    assert prefix_map.cmd[7:] == [
        f"-I{root / 'cpp' / 'include'}",
        f"-I{root / 'cpp' / 'src'}",
        "-c",
        str(root / "cpp" / "src" / "types.cpp"),
        "-o",
        str(prefix_map.cwd / "types.o"),
    ]
    for call, unit in ((identifiers, IDENTIFIERS_UNIT), (reach, REACH_UNIT)):
        assert call.cmd == [
            "/usr/bin/clang++-23",
            "-g",
            "-O0",
            str(root / "cpp" / "src" / unit),
            "-S",
            "-emit-llvm",
            "-o",
            str(prefix_map.cwd / f"{unit}.ll"),
        ]
        assert call.cwd == root / "cpp" / "build-mutation"
        assert call.mull_config == str(root / "cpp" / "mull.yml")


def test_the_first_configured_tree_is_the_one_read(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    """With the whole tree unconfigured, a slice's database serves."""
    _ = _toolchain(monkeypatch, tmp_path)
    root = _repository(tmp_path, tree=RelPath("cpp/build-mutation-2"))
    asked = _answers(monkeypatch, prefix_map=ExitStatus(139), ir=_ir())
    assert check(root) == ExitStatus(0)
    assert [call.cwd for call in asked[1:]] == [root / "cpp" / "build-mutation-2"] * 2


def test_a_compile_the_plugin_accepts_refuses_the_prefix_map_fact(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """A compile ending 0 under the flag means the build can apply it, which refuses."""
    _ = _toolchain(monkeypatch, tmp_path)
    root = _repository(tmp_path)
    _ = _answers(monkeypatch, prefix_map=ExitStatus(0), ir=_ir())
    assert check(root) == ExitStatus(1)
    assert capsys.readouterr().out == (
        f"{_GATE}: the plugin now accepts -ffile-prefix-map;"
        + " cpp/CMakeLists.txt can apply it to the mutation build\n"
    )


def test_a_prefix_map_compile_ending_another_way_is_no_answer(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """A compile failing for another reason reaches no fact, and its last lines are shown."""
    _ = _toolchain(monkeypatch, tmp_path)
    root = _repository(tmp_path)
    _ = _answers(monkeypatch, prefix_map=ExitStatus(1), ir=_ir())
    assert check(root) == ExitStatus(2)
    assert capsys.readouterr().out == (
        f"{_GATE}: clang++-23 ended with status 1 compiling cpp/src/types.cpp under the plugin,"
        + " neither 0 nor SIGSEGV:\ncrashed\n"
    )


def test_corrupt_identifiers_in_the_emitted_ir_refuse(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """An identifier without its seventh part and one two trampolines store are each named."""
    _ = _toolchain(monkeypatch, tmp_path)
    root = _repository(tmp_path)
    corrupt = IrText(
        _body(_JSON_FUNCTION, [_STRIPPED, _JSON_IDS[1]]) + _body(_READER_FUNCTION, [_JSON_IDS[1]])
    )
    _ = _answers(monkeypatch, prefix_map=ExitStatus(139), ir={**_ir(), IDENTIFIERS_UNIT: corrupt})
    assert check(root) == ExitStatus(1)
    assert capsys.readouterr().out == (
        f"{_GATE}: no seventh part: {_STRIPPED}\n"
        + f"{_GATE}: shared by 2 trampolines: {_JSON_IDS[1]}\n"
    )


def test_a_call_mutator_missing_its_line_refuses(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """IR with no void-call mutant on the close line refuses the reach fact."""
    _ = _toolchain(monkeypatch, tmp_path)
    root = _repository(tmp_path)
    ir = {**_ir(), REACH_UNIT: _backend_ir(void_call=False)}
    _ = _answers(monkeypatch, prefix_map=ExitStatus(139), ir=ir)
    assert check(root) == ExitStatus(1)
    assert capsys.readouterr().out == (
        f"{_GATE}: no cxx_remove_void_call mutant on line(s) [445] of cpp/src/ffi_backend.cpp\n"
    )


def test_a_source_line_gone_is_no_answer_beside_a_refusal(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """Every finding is printed, and the refusal decides the exit over the staleness."""
    _ = _toolchain(monkeypatch, tmp_path)
    root = _repository(tmp_path)
    _ = (root / "cpp" / "src" / REACH_UNIT).write_text(
        _backend_source(close_call=False), encoding="utf-8"
    )
    _ = _answers(monkeypatch, prefix_map=ExitStatus(0), ir=_ir())
    assert check(root) == ExitStatus(1)
    assert capsys.readouterr().out == (
        f"{_GATE}: the plugin now accepts -ffile-prefix-map;"
        + " cpp/CMakeLists.txt can apply it to the mutation build\n"
        + f"{_GATE}: no line of cpp/src/ffi_backend.cpp matches fns_\\.close\\(state\\)\n"
    )


def test_an_ir_compile_that_fails_is_no_answer(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """A unit that does not compile reaches neither IR fact, each named with the compiler's say."""
    _ = _toolchain(monkeypatch, tmp_path)
    root = _repository(tmp_path)
    _ = _answers(monkeypatch, prefix_map=ExitStatus(139), ir=_ir(), ir_status=ExitStatus(1))
    assert check(root) == ExitStatus(2)
    assert capsys.readouterr().out == (
        f"{_GATE}: clang++-23 could not emit the IR of cpp/src/json_parse.cpp (status 1); a"
        + " plugin built without the patches under tools/mull/ ends this way too, its"
        + " scalar-call mutator aborting clang on a bool-returning call:\nout said\n"
        + f"{_GATE}: clang++-23 could not emit the IR of cpp/src/ffi_backend.cpp (status 1); a"
        + " plugin built without the patches under tools/mull/ ends this way too, its"
        + " scalar-call mutator aborting clang on a bool-returning call:\nout said\n"
    )


def test_a_database_naming_a_unit_twice_is_no_answer(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """A unit the database names twice, or never, gives no one command to emit its IR with."""
    _ = _toolchain(monkeypatch, tmp_path)
    root = _repository(tmp_path, units=(IDENTIFIERS_UNIT, IDENTIFIERS_UNIT))
    asked = _answers(monkeypatch, prefix_map=ExitStatus(139), ir=_ir())
    assert check(root) == ExitStatus(2)
    assert len(asked) == 1
    database = root / "cpp" / "build-mutation" / COMPILE_DATABASE
    assert capsys.readouterr().out == (
        f"{_GATE}: {database} names /cpp/src/json_parse.cpp 2 times, not once\n"
        + f"{_GATE}: {database} names /cpp/src/ffi_backend.cpp 0 times, not once\n"
    )


def test_no_configured_tree_is_no_answer(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """Without a database the IR facts cannot be reached; the trees looked for are named."""
    _ = _toolchain(monkeypatch, tmp_path)
    root = _repository(tmp_path, tree=RelPath("cpp/build"))
    asked = _answers(monkeypatch, prefix_map=ExitStatus(139), ir=_ir())
    assert check(root) == ExitStatus(2)
    assert len(asked) == 1
    assert capsys.readouterr().out == (
        f"{_GATE}: no configured mutation tree: none of cpp/build-mutation, cpp/build-mutation-1,"
        + f" cpp/build-mutation-2, cpp/build-mutation-3 under {root} holds {COMPILE_DATABASE}\n"
    )


def test_a_missing_plugin_is_no_answer(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """Without the plugin nothing is compiled."""
    plugin = _toolchain(monkeypatch, tmp_path, plugin=False)
    asked = _answers(monkeypatch, prefix_map=ExitStatus(139), ir=_ir())
    assert check(_repository(tmp_path)) == ExitStatus(2)
    assert not asked
    assert capsys.readouterr().out == (
        f"{_GATE}: Mull plugin not found at {plugin}; tools/build_mull.sh installs it\n"
    )


def test_a_missing_compiler_is_no_answer(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """Without clang++-23 nothing is compiled."""

    def absent(name: CommandWord) -> CommandWord:
        message = f"required executable not found on PATH: {name}"
        raise RuntimeError(message)

    monkeypatch.setattr(check_mull_plugin_facts, "find_executable", absent)
    asked = _answers(monkeypatch, prefix_map=ExitStatus(139), ir=_ir())
    assert check(_repository(tmp_path)) == ExitStatus(2)
    assert not asked
    assert capsys.readouterr().out == (
        f"{_GATE}: required executable not found on PATH: clang++-23\n"
    )


def _out_of_scope(_gate: PinGate, _root: Path) -> bool:
    """Answer that the branch moved nothing a gate rests on."""
    return False


def _never_checked(_root: Path) -> ExitStatus:
    """Fail the test if the gate reaches for a compiler."""
    raise AssertionError


def test_a_branch_moving_nothing_the_facts_rest_on_compiles_nothing(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    """Out of scope, the gate passes without compiling."""

    def the_tree() -> Path:
        return tmp_path

    monkeypatch.setattr(check_mull_plugin_facts, "git_toplevel", the_tree)
    monkeypatch.setattr(check_mull_plugin_facts, "gate_runs", _out_of_scope)
    monkeypatch.setattr(check_mull_plugin_facts, "check", _never_checked)
    monkeypatch.setattr("sys.argv", ["check_mull_plugin_facts"])
    assert check_mull_plugin_facts.main() == ExitStatus(0)


def test_in_scope_the_gate_s_verdict_is_the_check_s(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    """A branch moving what the facts rest on gets the check's own exit status."""

    def the_tree() -> Path:
        return tmp_path

    def in_scope(_gate: PinGate, _root: Path) -> bool:
        return True

    def refusing(root: Path) -> ExitStatus:
        assert root == tmp_path
        return ExitStatus(1)

    monkeypatch.setattr(check_mull_plugin_facts, "git_toplevel", the_tree)
    monkeypatch.setattr(check_mull_plugin_facts, "gate_runs", in_scope)
    monkeypatch.setattr(check_mull_plugin_facts, "check", refusing)
    monkeypatch.setattr("sys.argv", ["check_mull_plugin_facts"])
    assert check_mull_plugin_facts.main() == ExitStatus(1)


def test_the_gate_refuses_an_argument_it_does_not_take(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """An argument the gate does not take stops it before it reads anything."""
    monkeypatch.setattr("sys.argv", ["check_mull_plugin_facts", "--unknown"])
    with pytest.raises(SystemExit) as stopped:
        _ = check_mull_plugin_facts.main()
    assert stopped.value.code == 2
