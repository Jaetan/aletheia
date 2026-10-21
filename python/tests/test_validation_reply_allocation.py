# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""A refused load allocates in proportion to its issues.

The kernel's ``handler_validation_failed`` reply joins every error issue's
detail into its ``message``; a join that copies the text joined so far at
every step allocates in proportion to the square of the issue count, and a
DBC whose every message carries hundreds of overlap issues then takes minutes
to refuse.  The bytes the kernel's runtime allocates for one refusal, read
through :func:`aletheia.allocated_bytes` around the load, may grow by at most
``MAX_ALLOCATION_DOUBLING`` per doubling of the issue count, the factor the
required load-scaling check holds accepted loads to.  Allocation is counted,
not timed, so the machine's load does not move the verdict.
"""

from __future__ import annotations

from typing import Final, NamedTuple, NewType

from tools.benchmark_gate import MAX_ALLOCATION_DOUBLING

from aletheia import AletheiaClient, allocated_bytes
from aletheia.common_types import AllocatedBytes

# Signals per message, every one at bit 0: a message carries one overlap issue
# per pair of its signals.
_OVERLAPPING_SIGNALS: Final = 50

# How many messages a DBC text holds, and the text itself.
MessageCount = NewType("MessageCount", int)
DBCText = NewType("DBCText", str)
IssueCount = NewType("IssueCount", int)


class Refusal(NamedTuple):
    """What one refused load cost and carried."""

    allocated: AllocatedBytes
    issues: IssueCount


def _overlapping_dbc(messages: MessageCount) -> DBCText:
    """Write ``messages`` messages, each of ``_OVERLAPPING_SIGNALS`` signals at bit 0."""
    lines = ['VERSION ""', "", "NS_ :", "", "BS_:", "", "BU_: N", ""]
    for m in range(messages):
        lines.append(f"BO_ {m + 1} M{m}: 8 N")
        lines.extend(
            f' SG_ S{m}_{s} : 0|8@1+ (1,0) [0|1] "" N' for s in range(_OVERLAPPING_SIGNALS)
        )
        lines.append("")
    return DBCText("\n".join(lines) + "\n")


def _refuse(client: AletheiaClient, messages: MessageCount) -> Refusal:
    """Load ``messages`` overlapping messages, counting the refusal's bytes and issues."""
    before = allocated_bytes()
    reply = client.parse_dbc_text(_overlapping_dbc(messages))
    after = allocated_bytes()
    assert before is not None
    assert after is not None
    assert reply["status"] == "error", reply
    assert reply["code"] == "handler_validation_failed", reply["code"]
    assert "issues" in reply, reply
    return Refusal(AllocatedBytes(after - before), IssueCount(len(reply["issues"])))


def test_a_refusal_allocates_in_proportion_to_its_issues() -> None:
    """Doubling the messages doubles the issues and multiplies the bytes by at most the factor."""
    with AletheiaClient() as client:
        two = _refuse(client, MessageCount(2))
        four = _refuse(client, MessageCount(4))
    assert four.issues == 2 * two.issues, (two.issues, four.issues)
    assert four.allocated <= two.allocated * MAX_ALLOCATION_DOUBLING, (
        two,
        four,
        four.allocated / two.allocated,
    )
