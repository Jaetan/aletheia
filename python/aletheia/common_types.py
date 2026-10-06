# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Types the library shares across its modules and with the tooling that builds and checks it.

A type hint is universally quantified, so a value with a meaning carries a
type naming it rather than a bare ``str`` or ``int``.  The ones used in more
than one part of the package, or on both sides of the package boundary, live
here, where the library, its command line and ``tools/`` all import them.  The
module imports nothing outside the standard library, since the tooling reaches
it under an interpreter that holds no third-party package.
"""

from dataclasses import dataclass
from typing import Annotated, NewType

# Text only a person reads: a diagnostic, a message, a description.  Typed
# apart from a value with a meaning, so that a `str` in a hint never stands
# for prose.
Prose = NewType("Prose", str)

# A process's exit status, as a command returns it and `sys.exit` takes it.
ExitStatus = NewType("ExitStatus", int)


@dataclass(frozen=True)
class Gt[T]:
    """``Annotated`` metadata: the annotated value is greater than ``bound``."""

    bound: T


# An integer greater than zero: a length, a count or a limit.
PositiveInt = Annotated[int, Gt(0)]
