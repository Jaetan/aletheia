"""FFI infrastructure for loading and initializing the Aletheia shared library."""

import ctypes
import json
import logging
import os
import stat
import threading
from pathlib import Path

from aletheia.protocols import is_str_dict
from aletheia.client._log import LogEvent, log_event
from aletheia.client._types import ProtocolError


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
                # Use hs_init_with_rtsopts so callers can pass arbitrary RTS
                # flags (e.g., -hT for heap profiling, -p for time profiling)
                # regardless of the shared library's link-time -rtsopts level
                # (which has no effect for native-shared libraries per the
                # GHC linker).
                init_fn = lib.hs_init_with_rtsopts
                init_fn.argtypes = [
                    ctypes.POINTER(ctypes.c_int),
                    ctypes.POINTER(ctypes.POINTER(ctypes.c_char_p)),
                ]
                init_fn.restype = None
                extra_rts = os.environ.get("ALETHEIA_RTS_OPTS", "").split()
                if rts_cores > 1 or extra_rts:
                    args: list[bytes] = [b"aletheia", b"+RTS"]
                    if rts_cores > 1:
                        args.append(b"-N" + str(rts_cores).encode())
                    for flag in extra_rts:
                        args.append(flag.encode("ascii"))
                    args.append(b"-RTS")
                else:
                    args = [b"aletheia"]
                argc = ctypes.c_int(len(args))
                argv = (ctypes.c_char_p * len(args))(*args)
                argv_ptr = ctypes.cast(argv, ctypes.POINTER(ctypes.c_char_p))
                init_fn(ctypes.byref(argc), ctypes.byref(argv_ptr))
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

    # Binary frame endpoint (hot path — bypasses JSON serialization on input).
    # The 4 trailing u8 args encode the optional CAN-FD BRS / ESI bits as
    # (present, value) pairs — `present=0` means the bit is absent (CAN 2.0B
    # frame), `present!=0` means present with `value!=0` for True.  See
    # `Aletheia.Trace.CANTrace.TimedFrame` + ISO 11898-1:2015 §10.4.2 / §10.4.3.
    lib.aletheia_send_frame.argtypes = [
        ctypes.c_void_p,                 # state
        ctypes.c_uint64,                 # timestamp
        ctypes.c_uint32,                 # can_id
        ctypes.c_uint8,                  # extended (0 or 1)
        ctypes.c_uint8,                  # dlc
        ctypes.POINTER(ctypes.c_uint8),  # data pointer
        ctypes.c_uint8,                  # data_len
        ctypes.c_uint8,                  # brs_present (0 or 1)
        ctypes.c_uint8,                  # brs_value   (0 or 1)
        ctypes.c_uint8,                  # esi_present (0 or 1)
        ctypes.c_uint8,                  # esi_value   (0 or 1)
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

    # Cross-binding-identical Rational pretty-printer (R20 cluster Y stage 2).
    # Returns a CString that the caller must free via ``aletheia_free_str``.
    # Display path only — bindings call this to render predicate values for
    # human-readable diagnostics.
    lib.aletheia_format_rational.argtypes = [
        ctypes.c_int64,   # numerator
        ctypes.c_int64,   # denominator (sign normalisation handled in shim)
    ]
    lib.aletheia_format_rational.restype = ctypes.c_void_p


def _validate_lib_path(p: Path, source: str) -> None:
    """Reject a candidate ``libaletheia-ffi.so`` path that fails security gates.

    Applied to every resolution path — env var, install config, build dir,
    dist-newstyle scan — per R20 cluster N / PY-B-26.2 / PY-A-27.2.  R19
    cluster 12 / PY-B-26.11 originally restricted these checks to the
    ``ALETHEIA_LIB`` env var; the fallback paths bypassed the symlink and
    permission gates even though they are equally untrusted from a
    "could be tampered post-install" standpoint.

    ``source`` is interpolated into error messages ("ALETHEIA_LIB=…",
    "install config", "build dir", "dist-newstyle") so the operator knows
    which resolution path failed.

    Raises:
        PermissionError: Path is a symlink, or group/world-writable.
    """
    # Reject symlinks before stat() — `Path.stat()` follows symlinks, so a
    # symlink-to-world-writable target would slip past the mode check.
    link_st = os.lstat(p)
    if stat.S_ISLNK(link_st.st_mode):
        raise PermissionError(
            f"{source} {p} is a symlink; refusing to load."
            + "  Resolve the link and pass the real path explicitly."
        )
    st = p.stat()
    if st.st_mode & (stat.S_IWGRP | stat.S_IWOTH):
        mode_octal = oct(st.st_mode & 0o777)
        raise PermissionError(
            f"{source} {p} is group- or world-writable"
            + f" (mode {mode_octal}); refusing to load for"
            + " security.  Restrict to owner-only writes"
            + f" ('chmod go-w {p}')."
        )


def find_ffi_library() -> Path:
    """Locate the libaletheia-ffi.so shared library.

    Search order:
    1. ``ALETHEIA_LIB`` environment variable (explicit path)
    2. Install config (generated by 'cabal run shake -- install')
    3. build/libaletheia-ffi.so (project root)
    4. haskell-shim/dist-newstyle/**/libaletheia-ffi.so (Cabal build dir)

    Every resolved path is run through :func:`_validate_lib_path` so a
    tampered ``_install_config.py``, build dir, or dist-newstyle entry
    cannot bypass the symlink + permission check that the ``ALETHEIA_LIB``
    path already enjoyed.  Defense-in-depth — if an attacker can plant
    ``_install_config.py`` they already own the package, but the two
    cheap stat calls cost essentially nothing.

    Returns:
        Path to the shared library

    Raises:
        FileNotFoundError: If library not found
        PermissionError: A resolved path is a symlink or group/world-writable
    """
    # Check ALETHEIA_LIB environment variable (Docker, custom deployments).
    # Permission hardening (R19 cluster B / PY-B-26.11): refuse a path
    # that any non-owner can write to.  The env var is implicitly trusted
    # — anyone who can set it can already redirect us to a malicious .so —
    # but a world-writable / group-writable file is even worse: an
    # unprivileged third party who cannot set the env var can still poison
    # an existing legitimate path.  Reject those.  Owner-of-file ≠ current
    # uid is allowed (shared /usr/local install with root-owned .so loaded
    # by a non-root user is a common, legitimate deployment).
    env_path = os.environ.get("ALETHEIA_LIB")
    if env_path:
        p = Path(env_path)
        if not p.exists():
            raise FileNotFoundError(
                f"ALETHEIA_LIB={env_path} does not exist"
            )
        _validate_lib_path(p, f"ALETHEIA_LIB={env_path}")
        return p

    # Check install config (generated by 'cabal run shake -- install').
    # Lazy import: _install_config.py is generated at install time and may not exist.
    try:
        from aletheia import _install_config  # pylint: disable=import-outside-toplevel
        if _install_config.LIBRARY_PATH.exists():
            _validate_lib_path(_install_config.LIBRARY_PATH, "install config")
            return _install_config.LIBRARY_PATH
    except ImportError:
        pass

    module_dir = Path(__file__).parent
    repo_root = module_dir.parent.parent.parent

    # Check project build dir first
    build_path = repo_root / "build" / "libaletheia-ffi.so"
    if build_path.exists():
        _validate_lib_path(build_path, "build dir")
        return build_path

    # Search Cabal dist-newstyle
    cabal_dir = repo_root / "haskell-shim" / "dist-newstyle"
    if cabal_dir.exists():
        for so_file in cabal_dir.rglob("libaletheia-ffi.so"):
            _validate_lib_path(so_file, "dist-newstyle")
            return so_file

    raise FileNotFoundError(
        "libaletheia-ffi.so not found. Build with: " +
        "cabal run shake -- build"
    )
