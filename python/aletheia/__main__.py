"""CLI entry point: ``python -m aletheia``.

Mirrors the ``aletheia`` console script in ``pyproject.toml`` so the same
entry point is reachable through both the shim (``aletheia``) and the
in-tree form (``python -m aletheia``), which matters in containers where
console scripts may not be on ``PATH``.  ``sys.exit`` is preferred over
``raise SystemExit`` because the latter shows up as an uncaught exception
in some IDEs even though semantically they are equivalent.
"""

import sys

from .cli import main

sys.exit(main())
