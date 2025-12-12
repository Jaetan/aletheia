"""Binary location utilities for Aletheia Python API

This module provides utilities for locating the Aletheia binary,
used by all client classes (StreamingClient, FrameBuilder, SignalExtractor).
"""

from pathlib import Path


def get_binary_path() -> Path:
    """Locate the Aletheia binary

    Returns:
        Path to the binary

    Raises:
        FileNotFoundError: If binary not found
    """
    module_dir = Path(__file__).parent
    repo_root = module_dir.parent.parent
    binary = repo_root / "build" / "aletheia"

    if not binary.exists():
        raise FileNotFoundError(
            f"Aletheia binary not found at {binary}. "
            "Please build it first with: cabal run shake -- build"
        )

    return binary
