"""FFI infrastructure for loading and initializing the Aletheia shared library."""

import ctypes
import json
import logging
import os
import threading
from pathlib import Path

from ..protocols import is_str_dict
from ._log import LogEvent, log_event
from ._types import ProtocolError


def parse_json_object(s: str) -> dict[str, object]:
    """Parse a JSON string that is expected to be an object.

    Wraps ``json.loads`` with validation and proper typing so
    callers get ``dict[str, object]`` instead of ``dict[Unknown, Unknown]``.
    """
    try:
        parsed: object = json.loads(s)
    except json.JSONDecodeError as exc:
        raise ProtocolError(f"FFI returned invalid JSON: {exc}") from exc
    if not is_str_dict(parsed):
        raise ProtocolError(f"Expected JSON object, got {type(parsed).__name__}")
    return parsed


class RTSState:
    """Module-level GHC RTS management.

    GHC RTS can only be initialized once per process.  We reference-count
    clients so ``hs_init()`` is called on first use and the RTS stays
    alive until process exit (GHC does not support reinitialization after
    ``hs_exit()``).
    """

    lib: ctypes.CDLL | None = None
    refcount: int = 0
    initialized: bool = False
    cores: int = 0
    _lock: threading.Lock = threading.Lock()

    @classmethod
    def acquire(cls, lib: ctypes.CDLL, rts_cores: int = 1) -> None:
        """Increment RTS reference count, initializing on first use.

        Args:
            lib: The loaded shared library.
            rts_cores: Number of GHC RTS capabilities (``-N`` flag).
                Use 1 (default) for single-bus monitoring.  Set to the
                number of CAN buses for multi-bus monitoring from
                separate Python threads.  Only takes effect on the first
                ``AletheiaClient`` created in a process.
        """
        with cls._lock:
            if not cls.initialized:
                lib.hs_init.argtypes = [
                    ctypes.POINTER(ctypes.c_int),
                    ctypes.POINTER(ctypes.POINTER(ctypes.c_char_p)),
                ]
                lib.hs_init.restype = None
                if rts_cores > 1:
                    args = [b"aletheia", b"+RTS",
                            b"-N" + str(rts_cores).encode(), b"-RTS"]
                else:
                    args = [b"aletheia"]
                argc = ctypes.c_int(len(args))
                argv = (ctypes.c_char_p * len(args))(*args)
                argv_ptr = ctypes.cast(argv, ctypes.POINTER(ctypes.c_char_p))
                lib.hs_init(ctypes.byref(argc), ctypes.byref(argv_ptr))
                cls.lib = lib
                cls.cores = rts_cores
                cls.initialized = True
            elif rts_cores != cls.cores:
                log_event(
                    logging.getLogger("aletheia"), logging.WARNING,
                    LogEvent.RTS_CORES_MISMATCH,
                    active_cores=cls.cores, requested_cores=rts_cores,
                )
            cls.refcount += 1

    @classmethod
    def release(cls) -> None:
        """Decrement RTS reference count."""
        with cls._lock:
            if cls.refcount > 0:
                cls.refcount -= 1


def configure_ffi_signatures(lib: ctypes.CDLL) -> None:
    """Configure ``argtypes``/``restype`` for every Aletheia FFI entry point.

    Called once after the shared library is loaded.  Split out of
    ``AletheiaClient.__enter__`` so the client module stays focused on
    protocol flow rather than ctypes boilerplate.
    """
    # Core lifecycle + JSON command endpoint
    lib.aletheia_init.argtypes = []
    lib.aletheia_init.restype = ctypes.c_void_p
    lib.aletheia_process.argtypes = [ctypes.c_void_p, ctypes.c_char_p]
    lib.aletheia_process.restype = ctypes.c_void_p
    lib.aletheia_free_str.argtypes = [ctypes.c_void_p]
    lib.aletheia_free_str.restype = None
    lib.aletheia_close.argtypes = [ctypes.c_void_p]
    lib.aletheia_close.restype = None

    # Binary frame endpoint (hot path — bypasses JSON serialization on input)
    lib.aletheia_send_frame.argtypes = [
        ctypes.c_void_p,                 # state
        ctypes.c_uint64,                 # timestamp
        ctypes.c_uint32,                 # can_id
        ctypes.c_uint8,                  # extended (0 or 1)
        ctypes.c_uint8,                  # dlc
        ctypes.POINTER(ctypes.c_uint8),  # data pointer
        ctypes.c_uint8,                  # data_len
    ]
    lib.aletheia_send_frame.restype = ctypes.c_void_p

    # Binary entry points (no JSON parsing on input)
    lib.aletheia_start_stream.argtypes = [ctypes.c_void_p]
    lib.aletheia_start_stream.restype = ctypes.c_void_p
    lib.aletheia_end_stream.argtypes = [ctypes.c_void_p]
    lib.aletheia_end_stream.restype = ctypes.c_void_p
    lib.aletheia_format_dbc.argtypes = [ctypes.c_void_p]
    lib.aletheia_format_dbc.restype = ctypes.c_void_p
    lib.aletheia_extract_signals.argtypes = [
        ctypes.c_void_p,                 # state
        ctypes.c_uint32,                 # can_id
        ctypes.c_uint8,                  # extended
        ctypes.c_uint8,                  # dlc
        ctypes.POINTER(ctypes.c_uint8),  # data pointer
        ctypes.c_uint8,                  # data_len
    ]
    lib.aletheia_extract_signals.restype = ctypes.c_void_p

    # CAN error/remote event endpoints (acknowledged without LTL evaluation)
    lib.aletheia_send_error.argtypes = [
        ctypes.c_void_p,   # state
        ctypes.c_uint64,   # timestamp
    ]
    lib.aletheia_send_error.restype = ctypes.c_void_p
    lib.aletheia_send_remote.argtypes = [
        ctypes.c_void_p,   # state
        ctypes.c_uint64,   # timestamp
        ctypes.c_uint32,   # can_id
        ctypes.c_uint8,    # extended (0 or 1)
    ]
    lib.aletheia_send_remote.restype = ctypes.c_void_p

    # Binary output entry points (no JSON on output either)
    lib.aletheia_build_frame_bin.argtypes = [
        ctypes.c_void_p,                  # state
        ctypes.c_uint32,                  # can_id
        ctypes.c_uint8,                   # extended
        ctypes.c_uint8,                   # dlc
        ctypes.c_uint32,                  # numSignals
        ctypes.POINTER(ctypes.c_uint32),  # indices
        ctypes.POINTER(ctypes.c_int64),   # numerators
        ctypes.POINTER(ctypes.c_int64),   # denominators
        ctypes.POINTER(ctypes.c_uint8),   # out_buf
        ctypes.POINTER(ctypes.c_char_p),  # out_err
    ]
    lib.aletheia_build_frame_bin.restype = ctypes.c_int8
    lib.aletheia_update_frame_bin.argtypes = [
        ctypes.c_void_p,                  # state
        ctypes.c_uint32,                  # can_id
        ctypes.c_uint8,                   # extended
        ctypes.c_uint8,                   # dlc
        ctypes.POINTER(ctypes.c_uint8),   # data pointer
        ctypes.c_uint8,                   # data_len
        ctypes.c_uint32,                  # numSignals
        ctypes.POINTER(ctypes.c_uint32),  # indices
        ctypes.POINTER(ctypes.c_int64),   # numerators
        ctypes.POINTER(ctypes.c_int64),   # denominators
        ctypes.POINTER(ctypes.c_uint8),   # out_buf
        ctypes.POINTER(ctypes.c_char_p),  # out_err
    ]
    lib.aletheia_update_frame_bin.restype = ctypes.c_int8
    lib.aletheia_extract_signals_bin.argtypes = [
        ctypes.c_void_p,                          # state
        ctypes.c_uint32,                           # can_id
        ctypes.c_uint8,                            # extended
        ctypes.c_uint8,                            # dlc
        ctypes.POINTER(ctypes.c_uint8),            # data pointer
        ctypes.c_uint8,                            # data_len
        ctypes.POINTER(ctypes.POINTER(ctypes.c_uint8)),  # out_buf
        ctypes.POINTER(ctypes.c_uint32),           # out_size
        ctypes.POINTER(ctypes.c_char_p),           # out_err
    ]
    lib.aletheia_extract_signals_bin.restype = ctypes.c_int8
    lib.aletheia_free_buf.argtypes = [ctypes.POINTER(ctypes.c_uint8)]
    lib.aletheia_free_buf.restype = None


def find_ffi_library() -> Path:
    """Locate the libaletheia-ffi.so shared library.

    Search order:
    1. ``ALETHEIA_LIB`` environment variable (explicit path)
    2. Install config (generated by 'cabal run shake -- install')
    3. build/libaletheia-ffi.so (project root)
    4. haskell-shim/dist-newstyle/**/libaletheia-ffi.so (Cabal build dir)

    Returns:
        Path to the shared library

    Raises:
        FileNotFoundError: If library not found
    """
    # Check ALETHEIA_LIB environment variable (Docker, custom deployments).
    env_path = os.environ.get("ALETHEIA_LIB")
    if env_path:
        p = Path(env_path)
        if p.exists():
            return p
        raise FileNotFoundError(
            f"ALETHEIA_LIB={env_path} does not exist"
        )

    # Check install config (generated by 'cabal run shake -- install').
    # Lazy import: _install_config.py is generated at install time and may not exist.
    try:
        from .. import _install_config  # pylint: disable=import-outside-toplevel
        if _install_config.LIBRARY_PATH.exists():
            return _install_config.LIBRARY_PATH
    except ImportError:
        pass

    module_dir = Path(__file__).parent
    repo_root = module_dir.parent.parent.parent

    # Check project build dir first
    build_path = repo_root / "build" / "libaletheia-ffi.so"
    if build_path.exists():
        return build_path

    # Search Cabal dist-newstyle
    cabal_dir = repo_root / "haskell-shim" / "dist-newstyle"
    if cabal_dir.exists():
        for so_file in cabal_dir.rglob("libaletheia-ffi.so"):
            return so_file

    raise FileNotFoundError(
        "libaletheia-ffi.so not found. Build with: " +
        "cabal run shake -- build"
    )
