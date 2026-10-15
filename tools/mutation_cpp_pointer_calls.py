# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The C++ lane's pointer-call rule, held on the census of every run over the whole tree.

``cpp/mull.yml`` sweeps ``cxx_replace_pointer_call_null``, which answers a
pointer-returning call with null, and the plugin makes it only where null is an
answer the caller reads: a call through a function pointer, or a result that
reaches a comparison with null.  A census carrying no such mutant is that
replacement made nowhere.  A census carrying one on a line that reads an
exception's message through ``.what()`` or ``->what()`` is the replacement made on a call that
never answers null, whose kill is the language's undefined behaviour rather
than a test.  The lane refuses both, whatever the record says.
"""

from __future__ import annotations

import re
from typing import TYPE_CHECKING

from tools.mutation_cpp_elements import MutatorName, repo_relative

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from tools.mutation_cpp_elements import ElementsFiles, LineReader

POINTER_CALL_MUTATOR = MutatorName("cxx_replace_pointer_call_null")
# What a line reading an exception's message spells: its ``what()``, through an object or a pointer.
_EXCEPTION_MESSAGE = re.compile(r"(?:\.|->)what\(\)")


def pointer_call_refusal(files: ElementsFiles, read_line: LineReader) -> Prose | None:
    """Refuse a census that breaks the pointer-call rule, or return None where it holds.

    ``files`` is an Elements report's ``files``, and ``read_line`` supplies a
    line of a repository-relative file.  A refusal on message lines names each
    line once, in file and line order: the instantiations of one template share
    a line.
    """
    sites = [
        (repo_relative(path), mutant["location"]["start"]["line"])
        for path, entry in files.items()
        for mutant in entry["mutants"]
        if mutant["mutatorName"] == POINTER_CALL_MUTATOR
    ]
    if not sites:
        return Prose(
            f"the census carries no {POINTER_CALL_MUTATOR} mutant: the plugin makes the "
            + "pointer-call replacement cpp/mull.yml sweeps nowhere"
        )
    on_message = sorted(
        {(file, line) for file, line in sites if _EXCEPTION_MESSAGE.search(read_line(file, line))}
    )
    if not on_message:
        return None
    named = ", ".join(f"{file}:{line}" for file, line in on_message)
    return Prose(
        f"{POINTER_CALL_MUTATOR} mutants on lines reading an exception's message, which "
        + f"never answers null: {named}"
    )
