# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Aletheia developer tooling (CI gates, dead-import detection, warm-process checks).

A package so modules can import siblings explicitly (`from tools.X import ...`);
the warm tools are invoked as `python -m tools.warm_check_properties` etc.
"""
