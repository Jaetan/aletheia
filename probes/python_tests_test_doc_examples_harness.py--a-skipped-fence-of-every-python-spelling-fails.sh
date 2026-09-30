#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes python/tests/test_doc_examples_harness.py.
# Claim: its check for a Python fence the harness skips sees a notest fence in
# every spelling the plugin runs as Python, py, python and python3, opened
# with backticks or with tildes, and reports no fence the harness runs. The
# check it replaced matched a backtick python fence alone and passed the rest.
# Non-zero exit: a skipped fence goes unreported, or a run fence is reported.
set -u
cd "$(dirname "$0")/.." || exit 2
python=python/.venv/bin/python
[ -f python/tests/test_doc_examples_harness.py ] && [ -x "$python" ] || exit 2
scratch=$(mktemp -d) || exit 2
trap 'rm -rf "$scratch"' EXIT

# Skipped fences open on lines 3, 7, 11 and 15; the run one on line 19.
cat > "$scratch/skips.md" <<'EOF'
# Fences

```py notest
raise SystemExit(1)
```

~~~python notest
raise SystemExit(1)
~~~

```python3 notest
raise SystemExit(1)
```

```python notest
raise SystemExit(1)
```

```python
value = 1
```
EOF

"$python" - "$scratch/skips.md" <<'EOF'
import sys
from pathlib import Path

sys.path[:0] = ["python/tests", "."]
from test_doc_examples_harness import _python_fences, _run_fences

doc = Path(sys.argv[1]).resolve()
skipped = sorted(_python_fences(doc) - _run_fences(doc))
run = sorted(_run_fences(doc))
if skipped != [3, 7, 11, 15] or run != [19]:
    print(f"skipped reported {skipped}, want [3, 7, 11, 15]; run {run}, want [19]")
    sys.exit(1)
print("PASS: a notest fence is reported in every Python spelling, and the run fence is not")
EOF
