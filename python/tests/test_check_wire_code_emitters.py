# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""``check_wire_code_emitters`` — every wire code names a constructor the runtime builds.

A gate that cannot fail has a bug, so each arm is proven red: a constructor only
matched, only declared, or built only outside the runtime closure fails the
check, and each unreadable input (no generated tree, no literal arm, an arm
naming no constructor, an empty closure) exits 2.  The classifier is pinned on
the generated layouts it meets: a construction under ``coe`` on the same or an
earlier line, a pattern whose ``->`` sits on the next line, a nested pattern.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

from tools.check_wire_code_emitters import (
    AgdaModule,
    Formatter,
    FunctionName,
    GeneratedName,
    SourceText,
    Tree,
    TypeName,
    constructions,
    run,
    unbuilt,
)

if TYPE_CHECKING:
    from pathlib import Path

FORMATTER = Formatter(
    AgdaModule("Aletheia.Error"),
    FunctionName("fooCode"),
    TypeName("Foo"),
    AgdaModule("Aletheia.Error"),
)

AGDA = SourceText("""\
fooCode : Foo → String
fooCode Built         = "foo_built"
fooCode (Matched _)   = "foo_matched"
fooCode (InContext _ inner) = fooCode inner
""")

DATA = SourceText("""\
data T_Foo_4
  = C_Built_6 | C_Matched_8 AgdaAny |
    C_InContext_10 AgdaAny AgdaAny
""")

FORMATTER_BODY = SourceText("""\
d_fooCode_12 v0
  = case coe v0 of
      C_Built_6 -> coe ("foo_built" :: Data.Text.Text)
      C_Matched_8 v1
        -> coe ("foo_matched" :: Data.Text.Text)
      _ -> MAlonzo.RTE.mazUnreachableError
""")

BUILDER = SourceText("""\
d_make_2 v0
  = coe
      MAlonzo.Code.Aletheia.Error.C_Built_6
""")


def _tree(
    tmp_path: Path,
    *,
    builder: SourceText = BUILDER,
    closure: tuple[AgdaModule, ...] = (AgdaModule("Aletheia.Error"), AgdaModule("Aletheia.User")),
) -> Tree:
    src = tmp_path / "src" / "Aletheia"
    gen = tmp_path / "gen" / "Aletheia"
    src.mkdir(parents=True)
    gen.mkdir(parents=True)
    _ = (src / "Error.agda").write_text(AGDA, encoding="utf-8")
    _ = (gen / "Error.hs").write_text(DATA + FORMATTER_BODY, encoding="utf-8")
    _ = (gen / "User.hs").write_text(builder, encoding="utf-8")
    snapshot = tmp_path / "closure.snapshot"
    _ = snapshot.write_text("".join(f"MAlonzo.Code.{m}\n" for m in closure), encoding="utf-8")
    return Tree(tmp_path / "src", tmp_path / "gen", snapshot)


def test_construction_under_coe_on_an_earlier_line_counts() -> None:
    """Construction under coe on an earlier line counts."""
    assert constructions(GeneratedName("C_Built_6"), BUILDER) == 1


def test_pattern_with_arrow_on_the_next_line_does_not_count() -> None:
    """Pattern with arrow on the next line does not count."""
    assert constructions(GeneratedName("C_Matched_8"), FORMATTER_BODY) == 0


def test_nested_pattern_does_not_count() -> None:
    """Nested pattern does not count."""
    text = SourceText("      C_Outer_2 (MAlonzo.Code.Aletheia.Error.C_Matched_8 v1) v2 -> coe v1\n")
    assert constructions(GeneratedName("C_Matched_8"), text) == 0


def test_nullary_construction_before_the_next_alternative_counts() -> None:
    """Nullary construction before the next alternative counts."""
    text = SourceText("      C_A_2 -> coe C_Built_6\n      C_B_4 -> coe v0\n")
    assert constructions(GeneratedName("C_Built_6"), text) == 1


def test_matched_only_constructor_fails_and_is_named(tmp_path: Path) -> None:
    """Matched only constructor fails and is named."""
    tree = _tree(tmp_path)
    _, dead = unbuilt(tree, (FORMATTER,))
    assert [code.code for code in dead] == ["foo_matched"]
    assert run(tree, (FORMATTER,)) == 1


def test_every_constructor_built_passes(tmp_path: Path) -> None:
    """Every constructor built passes."""
    builder = SourceText(BUILDER + "d_other_4 v0 = coe C_Matched_8 v0\n")
    assert run(_tree(tmp_path, builder=builder), (FORMATTER,)) == 0


def test_construction_outside_the_closure_does_not_count(tmp_path: Path) -> None:
    """Construction outside the closure does not count."""
    builder = SourceText(BUILDER + "d_other_4 v0 = coe C_Matched_8 v0\n")
    tree = _tree(
        tmp_path,
        builder=builder,
        closure=(AgdaModule("Aletheia.Error"), AgdaModule("Aletheia.Other")),
    )
    _ = (tmp_path / "gen" / "Aletheia" / "Other.hs").write_text("", encoding="utf-8")
    assert run(tree, (FORMATTER,)) == 1


def test_declaration_alone_is_not_a_construction(tmp_path: Path) -> None:
    """Declaration alone is not a construction."""
    assert run(_tree(tmp_path, builder=SourceText("")), (FORMATTER,)) == 1


def test_missing_generated_module_exits_two(tmp_path: Path) -> None:
    """Missing generated module exits two."""
    tree = _tree(tmp_path)
    (tmp_path / "gen" / "Aletheia" / "User.hs").unlink()
    assert run(tree, (FORMATTER,)) == 2


def test_formatter_without_literal_arms_exits_two(tmp_path: Path) -> None:
    """Formatter without literal arms exits two."""
    tree = _tree(tmp_path)
    _ = (tmp_path / "src" / "Aletheia" / "Error.agda").write_text(
        "fooCode : Foo → String\n", encoding="utf-8"
    )
    assert run(tree, (FORMATTER,)) == 2


def test_arm_naming_no_constructor_exits_two(tmp_path: Path) -> None:
    """Arm naming no constructor exits two."""
    tree = _tree(tmp_path)
    _ = (tmp_path / "src" / "Aletheia" / "Error.agda").write_text(
        AGDA + 'fooCode Ghost = "foo_ghost"\n', encoding="utf-8"
    )
    assert run(tree, (FORMATTER,)) == 2


def test_closure_without_aletheia_modules_exits_two(tmp_path: Path) -> None:
    """Closure without aletheia modules exits two."""
    assert run(_tree(tmp_path, closure=(AgdaModule("Agda.Builtin.Nat"),)), (FORMATTER,)) == 2
