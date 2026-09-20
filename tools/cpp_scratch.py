# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The scratch directories the C++ test binaries own, and the sweep of the dead.

Each run of a C++ test binary creates one directory under the system temp
directory and removes it at exit. A run a signal ends never reaches that
removal: a mutant killed by a test's assertion exits normally and takes its
directory with it, where one killed by a fault or by the kernel leaves it, and
a sweep leaves a directory for about one run in eight. They accumulate until
the filesystem is full and the next run fails on whatever writes next rather
than on the cause.

The fixture in cpp/tests/temp_path.hpp clears what it finds when a binary
starts, which repairs every caller, the probes that drive mull-runner directly
included. What it cannot repair is the tail: the runs at the end of a sweep
have no next binary. This is that tail, and it takes the same lock the fixture
does, the lock being what tells a directory whose owner is running from one
whose owner is gone. The kernel drops a ``flock`` however its holder ends,
whereas a process id is reused and a timestamp is not a freshness signal.
"""

from __future__ import annotations

import fcntl
import os
import shutil
import tempfile
from pathlib import Path

# The name every C++ test scratch directory starts with, the other spelling of
# which is ``scratch_prefix`` in cpp/tests/temp_path.hpp; a probe holds the two
# to one string.
SCRATCH_PREFIX = "aletheia-cpp-tests-"


def reap_dead_scratch_dirs() -> int:
    """Remove every scratch directory whose owning process is gone, and count them.

    A directory that cannot be opened, or whose lock a live owner holds, is
    left where it is, and nothing here refuses: what it sweeps is debris
    already.
    """
    removed = 0
    for candidate in sorted(Path(tempfile.gettempdir()).glob(f"{SCRATCH_PREFIX}*")):
        # The symlink is refused rather than resolved: the system temp
        # directory is world writable, and a link planted under this name
        # would otherwise be read as the directory it points at.
        if candidate.is_symlink() or not candidate.is_dir():
            continue
        try:
            fd = os.open(candidate, os.O_RDONLY | os.O_CLOEXEC)
        except OSError:
            continue
        try:
            fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except OSError:
            continue
        else:
            shutil.rmtree(candidate, ignore_errors=True)
            # Counted only when it is gone: a directory the removal could not
            # take, one holding an entry this user cannot unlink, stays and is
            # not a removal.
            if not candidate.exists():
                removed += 1
        finally:
            os.close(fd)
    return removed
