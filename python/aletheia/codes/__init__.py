# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Machine-readable codes — runtime error codes and DBC validation issues.

The public ``aletheia.codes`` namespace gathers the cross-binding code
enumerations:

* **Error codes** (``_error``) — ``ErrorCode``: the kernel's runtime error
  vocabulary, mirroring Agda's ``Error`` ADT (1:1 with Go / C++ enums).
* **Validation issues** (``_issue``) — ``IssueCode`` / ``IssueSeverity`` /
  ``ValidationIssue``: the DBC validator's issue vocabulary, mirroring the
  Agda ``IssueCode`` ADT.

``ErrorCode``, ``IssueCode`` and ``ValidationIssue`` are also re-exported
from the top-level ``aletheia`` package for convenience; ``IssueSeverity``
is available here as ``aletheia.codes.IssueSeverity``.
"""

from aletheia.codes._error import ErrorCode
from aletheia.codes._issue import IssueCode, IssueSeverity, ValidationIssue

__all__ = ["ErrorCode", "IssueCode", "IssueSeverity", "ValidationIssue"]
