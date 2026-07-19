# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Staged-bindings-tree fixture shared by the SBOM generator + coverage-gate tests.

Builds the directory shape the Shakefile ``dist`` rule stages under
``dist/aletheia/bindings`` (which the repository root mirrors: ``python/``,
``go/``, ``rust/``, ``cpp/`` each carry their manifests at the top level), so
both test modules exercise the manifest parsers over one canonical tree.  The
manifests are miniature but cover every shape the parsers must handle:
self-referential Python extras, block-form go.mod requires with an
``// indirect`` marker, a default-on/default-off Rust feature split with a
dev-only lock entry, and all three C++ fetch-URL version shapes plus the
test-only Catch2 declare.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from pathlib import Path

PYPROJECT = """\
[project]
name = "aletheia"
version = "1.2.3"

[project.optional-dependencies]
can = ["python-can>=4.6.1"]
yaml = ["pyyaml>=6.0.3"]
all = ["aletheia[can,yaml]"]
dev = ["aletheia[all]", "pytest>=9.1.1,<10"]
"""

GO_MOD = """\
module example.com/aletheia-go

go 1.24.0

require (
\tgopkg.in/yaml.v3 v3.0.1
\texample.com/other v1.2.0 // indirect
)
"""

GO_SUM = """\
example.com/other v1.2.0 h1:AAAAotherdigestAAAAotherdigestAAAAotherdigestA=
example.com/other v1.2.0/go.mod h1:BBBBotherdigestBBBBotherdigestBBBBotherdigB=
gopkg.in/yaml.v3 v3.0.1 h1:fxVm/GzAzEWqLHuvctI91KS9hhNmmWOoWu0XTYJS7CA=
gopkg.in/yaml.v3 v3.0.1/go.mod h1:K4uyk7z7BCEPqu6E+C64Yfv1cQ7kz7rIZviUmN+EgEM=
"""

CARGO_TOML = """\
[package]
name = "aletheia"
version = "1.2.3"

[dependencies]
libloading = "0.8"
yaml-rust2 = { version = "0.10", optional = true }
futures-channel = { version = "0.3", optional = true }

[dev-dependencies]
futures = "0.3"

[features]
default = ["yaml"]
yaml = ["dep:yaml-rust2"]
async = ["dep:futures-channel"]
"""

# Distinct, syntactically valid SHA-256 hex strings for the lock entries.
CFG_IF_SHA = "aa" * 32
FUTURES_SHA = "bb" * 32
FUTURES_CHANNEL_SHA = "cc" * 32
LIBLOADING_SHA = "dd" * 32
YAML_RUST2_SHA = "ee" * 32

CARGO_LOCK = f"""\
version = 4

[[package]]
name = "aletheia"
version = "1.2.3"
dependencies = ["libloading", "yaml-rust2"]

[[package]]
name = "cfg-if"
version = "1.0.4"
source = "registry+https://github.com/rust-lang/crates.io-index"
checksum = "{CFG_IF_SHA}"

[[package]]
name = "futures"
version = "0.3.32"
source = "registry+https://github.com/rust-lang/crates.io-index"
checksum = "{FUTURES_SHA}"

[[package]]
name = "futures-channel"
version = "0.3.32"
source = "registry+https://github.com/rust-lang/crates.io-index"
checksum = "{FUTURES_CHANNEL_SHA}"

[[package]]
name = "libloading"
version = "0.8.9"
source = "registry+https://github.com/rust-lang/crates.io-index"
checksum = "{LIBLOADING_SHA}"

[[package]]
name = "yaml-rust2"
version = "0.10.4"
source = "registry+https://github.com/rust-lang/crates.io-index"
checksum = "{YAML_RUST2_SHA}"
"""

JSON_SHA = "11" * 32
YAML_CPP_SHA = "22" * 32
OPENXLSX_SHA = "33" * 32
CATCH2_SHA = "44" * 32
OPENXLSX_COMMIT = "5723411d47643ce3b5b9994064c26ca8cd841f13"

CMAKELISTS = f"""\
cmake_minimum_required(VERSION 3.25)
project(fixture)

include(FetchContent)

FetchContent_Declare(json
    URL https://example.com/nlohmann/json/releases/download/v3.11.3/json.tar.xz
    URL_HASH SHA256={JSON_SHA})

FetchContent_Declare(yaml-cpp
    URL https://example.com/jbeder/yaml-cpp/archive/refs/tags/0.8.0.tar.gz
    URL_HASH SHA256={YAML_CPP_SHA})

FetchContent_Declare(OpenXLSX
    URL https://example.com/troldal/OpenXLSX/archive/{OPENXLSX_COMMIT}.tar.gz
    URL_HASH SHA256={OPENXLSX_SHA})

if(BUILD_TESTING)
    FetchContent_Declare(Catch2
        URL https://example.com/catchorg/Catch2/archive/refs/tags/v3.7.1.tar.gz
        URL_HASH SHA256={CATCH2_SHA})
endif()
"""

MANIFEST_CONTENTS: dict[str, str] = {
    "python/pyproject.toml": PYPROJECT,
    "go/go.mod": GO_MOD,
    "go/go.sum": GO_SUM,
    "rust/Cargo.toml": CARGO_TOML,
    "rust/Cargo.lock": CARGO_LOCK,
    "cpp/CMakeLists.txt": CMAKELISTS,
}


def make_bindings_tree(root: Path) -> Path:
    """Write the fixture manifests under ``root`` in the staged-bindings shape."""
    for rel, content in MANIFEST_CONTENTS.items():
        path = root / rel
        path.parent.mkdir(parents=True, exist_ok=True)
        _ = path.write_text(content, encoding="utf-8")
    return root
