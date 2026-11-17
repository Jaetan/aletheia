# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Tests for ``tools.bundle_c_example``, the gate building the guide's C example against a bundle.

Covers the tool's pure logic on planted inputs: the reader of the guide's C
section, a recipe as the gate runs it, the reply check, the work tree it lays
out, the command line and the refusals that end a run before anything starts.
Building and running the example needs a bundle and a C compiler, so the gate
itself runs them, where the bundle is built.
"""

from __future__ import annotations

from pathlib import Path

import pytest

from tools._common import CommandWord
from tools._markdown import Fence
from tools.bundle_c_example import (
    COULD_NOT_CHECK,
    PLACEHOLDER,
    CGuide,
    CGuideError,
    Config,
    c_guide_fences,
    check,
    lay_out,
    parse_args,
    read_c_guide,
    recipe_command,
    recipe_output,
    reply_problem,
)
from tools.bundle_validate import BundleValidationError

from aletheia.common_types import Prose

# A guide whose C section holds a fence of another language beside its recipe,
# and whose C++ section holds a subsection of the same name, which the reader
# must pass over.
_GUIDE_TEXT = Prose(
    r"""# Guide

### C++

#### Compile and link

~~~bash
not this one
~~~

### C

#### Compile and link

~~~
a tree, not a recipe
~~~

```bash
gcc -std=gnu23 -I/path/to/aletheia/include \
    -o my_app main.c
```

#### Relative RPATH (relocatable binary)

```bash
gcc -std=gnu23 -Ialetheia/include -o bin/my_app main.c
```

#### Minimal C example

```c
int main(void) { return 0; }
```

### Go
"""
)

_GUIDE = CGuide(
    link=Prose("gcc -std=gnu23 -I/path/to/aletheia/include \\\n    -o my_app main.c\n"),
    relocatable=Prose("gcc -std=gnu23 -Ialetheia/include -o bin/my_app main.c\n"),
    example=Prose("int main(void) { return 0; }\n"),
)


# ── The guide's C section ───────────────────────────────────────────────────


def test_the_reader_takes_each_fence_of_the_c_section_alone() -> None:
    """Each subsection of the C section gives its one fence of its language, the C++ one none."""
    assert read_c_guide(_GUIDE_TEXT) == _GUIDE


def test_each_fence_is_found_on_its_line_with_its_opening_tildes_too() -> None:
    """The reader finds a fence opened either way, so the fence gate has its line and its mark."""
    found = c_guide_fences(_GUIDE_TEXT)
    assert [block.fence for block in found] == [
        Fence(19, Prose("```"), Prose("bash")),
        Fence(26, Prose("```"), Prose("bash")),
        Fence(32, Prose("```"), Prose("c")),
    ]
    program = "int main(void) { return 0; }\n"
    tilde = Prose(str(_GUIDE_TEXT).replace(f"```c\n{program}```", f"~~~c\n{program}~~~", 1))
    assert tilde != _GUIDE_TEXT
    assert c_guide_fences(tilde).example.fence == Fence(32, Prose("~~~"), Prose("c"))
    assert read_c_guide(tilde) == _GUIDE


def test_a_guide_without_a_c_section_is_refused() -> None:
    """TEETH: no ``### C`` heading is a refusal, never an empty recipe."""
    with pytest.raises(CGuideError, match="0 '### C' sections, not one"):
        _ = read_c_guide(Prose(str(_GUIDE_TEXT).replace("### C\n", "### D\n", 1)))


def test_a_missing_subsection_is_refused() -> None:
    """TEETH: a subsection the C section does not hold is named in the refusal."""
    with pytest.raises(CGuideError, match="0 '#### Minimal C example' sections under '### C'"):
        _ = read_c_guide(Prose(str(_GUIDE_TEXT).replace("#### Minimal C example", "#### Example")))


def test_a_second_recipe_fence_is_refused() -> None:
    """TEETH: two bash fences under one subsection are refused rather than one of them run."""
    text = str(_GUIDE_TEXT).replace(
        "~~~\n\n```bash\ngcc", "~~~\n\n```bash\necho\n```\n\n```bash\ngcc"
    )
    assert text != _GUIDE_TEXT
    with pytest.raises(CGuideError, match="2 bash fences under 'Compile and link', not one"):
        _ = read_c_guide(Prose(text))


# ── A recipe as the gate runs it ────────────────────────────────────────────


def test_a_recipe_runs_with_the_compiler_named_and_the_bundle_for_the_placeholder() -> None:
    """The compiler word is the one named, and every placeholder the bundle's path."""
    recipe = Prose(f"gcc -I{PLACEHOLDER}/include -L{PLACEHOLDER}/lib -o my_app main.c")
    command = recipe_command(recipe, Path("/work/aletheia"), CommandWord("clang-23"))
    assert command == "clang-23 -I/work/aletheia/include -L/work/aletheia/lib -o my_app main.c"


def test_a_recipe_opening_with_another_word_is_refused() -> None:
    """TEETH: a recipe whose first word is not the compiler's is not run with it."""
    with pytest.raises(BundleValidationError, match="does not open with 'gcc '"):
        _ = recipe_command(Prose("cc -o my_app main.c"), Path("/work"), CommandWord("gcc"))


def test_a_bundle_path_the_shell_would_split_is_refused() -> None:
    """TEETH: the placeholder is written bare, so a path needing quotes is refused."""
    with pytest.raises(BundleValidationError, match="needs quoting"):
        _ = recipe_command(Prose("gcc -o a main.c"), Path("/a b/aletheia"), CommandWord("gcc"))


def test_the_program_is_the_one_word_after_its_output_flag() -> None:
    """``-o`` names the program, on the recipe's first line or a continuation."""
    assert recipe_output(_GUIDE.link) == Path("my_app")
    assert recipe_output(_GUIDE.relocatable) == Path("bin/my_app")


@pytest.mark.parametrize("recipe", ["gcc main.c", "gcc -o a -o b main.c"])
def test_a_recipe_naming_no_one_program_is_refused(recipe: Prose) -> None:
    """TEETH: no output, or two, leaves the program to run unknown, and is refused."""
    with pytest.raises(BundleValidationError, match="outputs after -o, not one"):
        _ = recipe_output(recipe)


def test_a_success_reply_passes() -> None:
    """The example's reply to a DBC it loads is a success, and passes."""
    assert reply_problem(Prose('{"status": "success", "dbc": {}}\n')) is None


@pytest.mark.parametrize(
    ("stdout", "problem"),
    [
        ('{"status": "error", "code": "parse_missing_field"}\n', "not a success reply"),
        ("hello\n", "not one JSON reply"),
        ("[]\n", "not one JSON reply"),
        ("{}\n", "not one JSON reply"),
        ("", "not one JSON reply"),
    ],
)
def test_anything_but_a_success_reply_fails(stdout: Prose, problem: Prose) -> None:
    """TEETH: an error reply, no JSON, a JSON array or an object with no status each fail."""
    found = reply_problem(stdout)
    assert found is not None
    assert str(found).endswith(problem)


def test_each_recipe_gets_a_directory_laid_out_as_the_guide_draws_it(tmp_path: Path) -> None:
    """The example in each; the relocatable one beside the bundle, ``lib`` its libraries."""
    (tmp_path / "aletheia" / "lib").mkdir(parents=True)
    link, deploy = lay_out(_GUIDE, tmp_path)
    assert (link.recipe, deploy.recipe) == (_GUIDE.link, _GUIDE.relocatable)
    for build in (link, deploy):
        assert (build.cwd / "main.c").read_text(encoding="utf-8") == _GUIDE.example
    assert link.cwd != deploy.cwd
    assert (deploy.cwd / "aletheia").resolve() == (tmp_path / "aletheia").resolve()
    assert (deploy.cwd / "lib").resolve() == (tmp_path / "aletheia" / "lib").resolve()
    assert (deploy.cwd / "bin").is_dir()


# ── The command line and the refusals before a run ──────────────────────────


def test_the_command_line_names_the_compiler_and_the_guide(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Every flag lands in the Config; the compiler is gcc unless named."""
    monkeypatch.setattr("sys.argv", ["bundle_c_example", "x.tar.gz"])
    assert parse_args().compiler == "gcc"
    argv = ["bundle_c_example", "x.tar.gz", "--guide", "g.md", "--c-compiler", "clang-23"]
    monkeypatch.setattr("sys.argv", [*argv, "--keep-work"])
    wanted = Config(Path("x.tar.gz"), Path("g.md"), CommandWord("clang-23"), keep_work=True)
    assert parse_args() == wanted


def _config(tmp_path: Path, compiler: CommandWord) -> Config:
    """Return a run over a tarball and a guide planted under ``tmp_path``."""
    return Config(tmp_path / "aletheia.tar.gz", tmp_path / "guide.md", compiler)


def test_an_absent_compiler_could_not_check(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """TEETH: a compiler not in PATH is a could-not-check, named, never a pass."""
    said: list[Prose] = []
    monkeypatch.setattr("tools.bundle_c_example.emit", said.append)
    assert check(_config(tmp_path, CommandWord("no-such-c-compiler"))) == COULD_NOT_CHECK
    assert said == ["c example: COULD NOT CHECK, no-such-c-compiler is not in PATH"]


def test_an_absent_tarball_could_not_check(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    """TEETH: no tarball is a could-not-check, named."""
    said: list[Prose] = []
    monkeypatch.setattr("tools.bundle_c_example.emit", said.append)
    assert check(_config(tmp_path, CommandWord("bash"))) == COULD_NOT_CHECK
    assert said == [f"c example: COULD NOT CHECK, no tarball at {tmp_path / 'aletheia.tar.gz'}"]


def test_a_guide_the_reader_cannot_take_could_not_check(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """TEETH: a guide with no C section is a could-not-check, naming the guide."""
    cfg = _config(tmp_path, CommandWord("bash"))
    _ = cfg.tarball.write_bytes(b"")
    _ = cfg.guide.write_text("# Guide\n", encoding="utf-8")
    said: list[Prose] = []
    monkeypatch.setattr("tools.bundle_c_example.emit", said.append)
    assert check(cfg) == COULD_NOT_CHECK
    assert said == [f"c example: COULD NOT CHECK, {cfg.guide}: 0 '### C' sections, not one"]
