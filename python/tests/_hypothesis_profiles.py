# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The hypothesis profiles the property tests draw under.

``ci`` draws 200 examples a test and ``dev``, the default, 20; every run of the
whole suite by run_ci and by the coverage lane selects ``ci`` with
``--hypothesis-profile``.  The conftest registers them when it is imported:
the hypothesis plugin applies that option when pytest configures, after the
conftest is imported and before any test module is, and ``@given`` keeps the
profile in force when it decorates.  Neither profile replays an example a run
before it saved, and no deadline or speed check decides an outcome, since a
test reads no clock (AGENTS.md, Universal Rules).
"""

from typing import Literal, NewType

from hypothesis import HealthCheck, settings

# How many examples a profile draws for a test, and the profiles there are.
ExampleCount = NewType("ExampleCount", int)
type ProfileName = Literal["ci", "dev"]

CI_PROFILE: ProfileName = "ci"
DEFAULT_PROFILE: ProfileName = "dev"


def _register(name: ProfileName, examples: ExampleCount) -> None:
    """Register a profile that draws ``examples`` a test and nothing a run before it saved."""
    settings.register_profile(
        name,
        max_examples=examples,
        database=None,
        deadline=None,
        suppress_health_check=[HealthCheck.too_slow],
    )


def register_profiles() -> None:
    """Register both profiles and load the default, which ``--hypothesis-profile`` overrides."""
    _register(CI_PROFILE, ExampleCount(200))
    _register(DEFAULT_PROFILE, ExampleCount(20))
    settings.load_profile(DEFAULT_PROFILE)
