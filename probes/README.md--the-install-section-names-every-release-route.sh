#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes README.md, its Install section.
# Claim: the section names every route a release is published by, each by a
# link to that route's section of docs/development/DISTRIBUTION.md, and names
# no other: the bundle tarball, the .deb and .rpm packages, and the GHCR
# image. The routes are read from .github/workflows/release.yml, its signed
# artifact list and its image push, so a route the release gains is one the
# section has to name. The section named two of the three when the release
# shipped all of them.
# Non-zero exit: a published route has no link in the section, the section
# links a guide section no route is, a linked section is not in the guide, or
# the release publishes something this probe cannot map to a route.
set -u
cd "$(dirname "$0")/.." || exit 2
py=python/.venv/bin/python
[ -x "$py" ] || exit 2
"$py" - <<'PY'
import re
import sys
from pathlib import Path

from tools.check_docs import header_slugs

guide = Path("docs/development/DISTRIBUTION.md")
readme = Path("README.md").read_text(encoding="utf-8")
release = Path(".github/workflows/release.yml").read_text(encoding="utf-8")
# Each route a release publishes, by what the workflow publishes, and the
# guide section that installs it.
route_of_artifact = {
    "dist/aletheia.tar.gz": "using-a-release-bundle",
    "dist/*.deb": "installing-from-a-native-package-deb--rpm",
    "dist/*.rpm": "installing-from-a-native-package-deb--rpm",
}
image_route = "pull-the-published-image-ghcr"
bad = []

listed = re.search(r"^\s*artifacts=\(([^)]*)\)", release, re.M)
if not listed:
    print(".github/workflows/release.yml no longer lists its signed artifacts"); sys.exit(2)
published = set()
for artifact in listed.group(1).split():
    if artifact not in route_of_artifact:
        bad.append(f"the release publishes {artifact}, which no route here covers")
    else:
        published.add(route_of_artifact[artifact])
if re.search(r'image="ghcr\.io/', release) and re.search(r'^\s*docker push "\$\{image\}', release, re.M):
    published.add(image_route)

if "### Install" not in readme:
    print("README.md has no Install section"); sys.exit(1)
section = readme[readme.index("### Install"):]
section = section[:section.index("\n### ", 1)]
linked = set(re.findall(r"\]\(docs/development/DISTRIBUTION\.md#([^)]+)\)", section))
slugs = header_slugs(guide)
for route in sorted(published - linked):
    bad.append(f"the release publishes a route the Install section does not link: #{route}")
for route in sorted(linked - published):
    bad.append(f"the Install section links #{route}, which is no route the release publishes")
for route in sorted(linked - slugs):
    bad.append(f"the Install section links #{route}, which is no section of {guide}")
if bad:
    print("README.md's Install section and the release's routes disagree:")
    for line in bad:
        print(f"  {line}")
    sys.exit(1)
print(f"PASS: the Install section links each of the {len(published)} routes the release publishes, and no other")
PY
