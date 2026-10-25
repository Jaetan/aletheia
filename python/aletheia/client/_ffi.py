# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""FFI infrastructure for loading and initializing the Aletheia shared library."""

import ctypes
import importlib
import json
import logging
import os
import stat
import threading
from pathlib import Path
from typing import TYPE_CHECKING, NewType, cast

from aletheia.client._log import LogEvent, log_event
from aletheia.client._types import FFIError, ProtocolError, ValidationError
from aletheia.common_types import CoreCount, Prose
from aletheia.types import JSONValue, is_str_dict

if TYPE_CHECKING:
    from aletheia.common_types import AllocatedBytes
    from aletheia.types import Response

# The reply of a kernel entry that answers in JSON, as the bytes it returned.
KernelResponse = NewType("KernelResponse", bytes)

# The address of a string the library allocated, read and then freed.
KernelString = NewType("KernelString", int)


def parse_json_object(raw: KernelResponse) -> dict[str, JSONValue]:
    """Read a kernel response as the JSON object it should spell.

    Wraps ``json.loads`` with validation and proper typing so
    callers get ``dict[str, JSONValue]`` instead of ``dict[Unknown, Unknown]``.
    A response that is not UTF-8, is not JSON, holds an integer longer than
    the interpreter converts or nests deeper than the decoder's recursion
    holds raises ``ProtocolError``, never the decoder's own error.
    """
    try:
        parsed: object = json.loads(raw.decode("utf-8"))
    except (ValueError, RecursionError) as exc:
        msg = f"FFI returned invalid JSON: {exc}"
        raise ProtocolError(msg) from exc
    if not is_str_dict(parsed):
        msg = f"Expected JSON object, got {type(parsed).__name__}"
        raise ProtocolError(msg)
    return parsed


# Runtime RTS parameters — SSOT: docs/RESOURCE_BUDGETS.yaml (runtime block);
# mirrored here verbatim.  Parity with the SSOT is enforced by
# tools/check_rts_runtime.py (a run_ci gate).
#
# Default maximum heap for the loaded kernel's GHC RTS.  The RTS has NO heap
# limit by default, so a runaway allocation inside the kernel is not a failed
# call — it exhausts host memory and the OOM killer takes the whole machine
# down (observed twice while probing a kernel defect whose cost grew with a
# rational's magnitude).
#
# CONTAINMENT-BY-ABORT contract: the cap does NOT yield a recoverable error.
# When it fires, GHC's heap-overflow check trips and the foreign-export
# wrapper's ``rts_checkSchedStatus`` calls ``stg_exit`` on the non-Success
# return, so the PROCESS TERMINATES with a diagnostic
# (``aletheia: aletheia_process: Return code (4) not ok``).  There is no
# catchable error and no partial result — the guarantee is that the HOST
# survives while the process does not.
#
# The value is a containment bound, not a working-set estimate: the heaviest
# kernel working set measured on this project is ~1.5 GiB (the full proof
# gate), and ordinary client use sits near a hundred megabytes, so this leaves
# ample headroom while staying far below any developer host's memory.  Override
# per process with ``ALETHEIA_RTS_OPTS`` (its flags are appended after this one,
# and the RTS honours the last occurrence, so a caller -M wins).
DEFAULT_RTS_HEAP_CAP = b"-M3G"

# GHC capability count when a caller does not ask for more (single-bus
# monitoring).  A ``-N`` flag is emitted only when ``rts_cores`` exceeds this.
DEFAULT_RTS_CORES = 1

# The GHC entry point used to start the RTS.  Plain ``hs_init`` cannot carry
# the ``-M`` cap under the .so's link-time RtsOptsSafeOnly (it aborts at init
# with "Most RTS options are disabled"); ``hs_init_with_rtsopts`` honours the
# full flag set.  Both share the C signature ``void(int*, char***)``.
RTS_INIT_SYMBOL = "hs_init_with_rtsopts"

# Environment variable whose whitespace-split flags are appended after the cap.
RTS_OVERRIDE_ENV = "ALETHEIA_RTS_OPTS"

# The GHC runtime's count of the CPUs the process may use (its affinity set on
# Linux), callable before the runtime starts: a core count past it is refused.
RTS_PROCESSORS_SYMBOL = "getNumberOfProcessors"


class RTSState:
    """The GHC runtime's once-per-process state.

    The runtime starts once per process and stays up until it exits (GHC does
    not start again after ``hs_exit()``): ``lib`` and ``cores`` are the library
    and the core count it started with.  ``refcount`` counts the backend
    references :meth:`acquire` took and :meth:`release` gave back; a start of
    its own (:func:`start_runtime`) takes none.
    """

    lib: ctypes.CDLL | None = None
    refcount: int = 0
    initialized: bool = False
    cores: int = 0

    @classmethod
    def acquire(cls, lib: ctypes.CDLL, rts_cores: int | None = None) -> None:
        """Take a backend's reference to the runtime, starting it on ``lib`` if nothing has.

        Args:
            lib: The loaded shared library.
            rts_cores: The GHC runtime's capabilities (``-N``), or ``None`` for
                the count running, 1 if nothing runs.  A runtime already up
                keeps its count, and another count asked of it is warned.

        Raises:
            ValidationError: ``rts_cores`` is outside 1 to the CPUs the process may use.

        """
        start_runtime_on(lib, None if rts_cores is None else CoreCount(rts_cores))
        with _RUNTIME_LOCK:
            cls.refcount += 1

    @classmethod
    def release(cls) -> None:
        """Give back a backend's reference."""
        with _RUNTIME_LOCK:
            if cls.refcount > 0:
                cls.refcount -= 1


_RUNTIME_LOCK = threading.Lock()


def core_count_refusal(requested: CoreCount, available: CoreCount) -> Prose | None:
    """Return the refusal of a core count outside 1 to ``available``, or ``None`` inside it."""
    if 1 <= requested <= available:
        return None
    return Prose(
        f"core count {requested} is outside 1 to {available}, the CPUs this process may use"
    )


def available_cores(lib: ctypes.CDLL) -> CoreCount:
    """Return the CPUs the process may use, as the GHC runtime of ``lib`` counts them."""
    count = getattr(lib, RTS_PROCESSORS_SYMBOL)
    count.argtypes = []
    count.restype = ctypes.c_uint32
    cpus: CoreCount = count()
    return cpus


def start_runtime_on(lib: ctypes.CDLL, cores: CoreCount | None) -> None:
    """Start the GHC runtime on ``lib`` with ``cores`` capabilities, unless it runs.

    The one start every route takes, :func:`start_runtime` and a backend's
    :meth:`RTSState.acquire`.  ``None`` asks the count running, 1 if nothing
    runs.  The count is checked against the CPUs the process may use whether or
    not the runtime runs; a runtime that runs keeps its count, and another one
    asked of it is the ``rts.cores_mismatch`` warning on the package logger.

    Raises:
        ValidationError: ``cores`` is outside 1 to the CPUs the process may use.

    """
    with _RUNTIME_LOCK:
        running = CoreCount(RTSState.cores) if RTSState.initialized else None
        if cores is not None:
            asked = cores
        else:
            asked = running if running is not None else CoreCount(DEFAULT_RTS_CORES)
        refusal = core_count_refusal(asked, available_cores(lib))
        if refusal is not None:
            raise ValidationError(refusal)
        if running is None:
            _start(lib, asked)
            RTSState.lib = lib
            RTSState.cores = asked
            RTSState.initialized = True
        elif asked != running:
            log_event(
                logging.getLogger("aletheia"),
                logging.WARNING,
                LogEvent.RTS_CORES_MISMATCH,
                active_cores=running,
                requested_cores=asked,
            )


def _start(lib: ctypes.CDLL, cores: CoreCount) -> None:
    """Call the runtime's start entry with the heap cap, ``-N`` past one core and the override."""
    # hs_init_with_rtsopts honours every flag whatever the library's link-time
    # -rtsopts level (which has no effect for a native shared library), so a
    # caller can pass a profiling flag through ALETHEIA_RTS_OPTS.
    init_fn = getattr(lib, RTS_INIT_SYMBOL)
    init_fn.argtypes = [
        ctypes.POINTER(ctypes.c_int),
        ctypes.POINTER(ctypes.POINTER(ctypes.c_char_p)),
    ]
    init_fn.restype = None
    extra_rts = os.environ.get(RTS_OVERRIDE_ENV, "").split()
    # The heap cap goes FIRST so a caller-supplied -M in ALETHEIA_RTS_OPTS
    # lands later and wins (the RTS honours the last occurrence of a flag).
    args: list[bytes] = [b"aletheia", b"+RTS", DEFAULT_RTS_HEAP_CAP]
    if cores > DEFAULT_RTS_CORES:
        args.append(b"-N" + str(cores).encode())
    args.extend(flag.encode("ascii") for flag in extra_rts)
    args.append(b"-RTS")
    argc = ctypes.c_int(len(args))
    argv = (ctypes.c_char_p * len(args))(*args)
    argv_ptr = ctypes.cast(argv, ctypes.POINTER(ctypes.c_char_p))
    init_fn(ctypes.byref(argc), ctypes.byref(argv_ptr))


def open_library(lib_path: Path | None) -> ctypes.CDLL:
    """Open ``libaletheia-ffi.so`` at ``lib_path``, or where :func:`find_ffi_library` finds it.

    The ABI version is checked before any entry is configured, so a library laid
    out for another version runs nothing.
    """
    path = lib_path if lib_path is not None else find_ffi_library()
    lib = ctypes.CDLL(str(path))
    check_abi_version(lib)
    configure_ffi_signatures(lib)
    return lib


def start_runtime(cores: int, *, lib_path: Path | None = None) -> None:
    """Start the kernel's GHC runtime on ``cores`` capabilities, before any client.

    The kernel reads every number a check carries, and its runtime starts once
    per process, so a program that loads checks before opening a client starts
    it first:

    ```python
    from pathlib import Path

    import aletheia

    aletheia.start_runtime(1)
    checks = aletheia.load_checks(Path("checks.yaml"))
    with aletheia.AletheiaClient(default_checks=checks) as client:
        ...
    ```

    A client opened later naming no core count asks for the count running.  A
    runtime already up keeps its count, and another count asked of it is
    warned (``rts.cores_mismatch``) on the ``aletheia`` logger.

    Args:
        cores: The GHC runtime's capabilities (``-N``): 1 for one bus, the
            number of buses when several threads each monitor their own.
        lib_path: ``libaletheia-ffi.so``, or ``None`` for where
            :func:`find_ffi_library` finds it.

    Raises:
        ValidationError: ``cores`` is outside 1 to the CPUs the process may use.
        FileNotFoundError: ``lib_path`` is ``None`` and no library is found.
        FFIError: the library implements another ABI version.

    """
    start_runtime_on(open_library(lib_path), CoreCount(cores))


def hs_initialized() -> bool:
    """Return whether the GHC runtime has started, by :func:`start_runtime` or a backend.

    The rational renderer and the decimal parser read it to stay vocal: they
    never start the runtime themselves, since a start fixes the core count for
    the process.
    """
    return RTSState.initialized


def started_library(reading: Prose) -> ctypes.CDLL:
    """Return the library the runtime started on, or refuse while it is down.

    The renderer and the decimal parser call the kernel through it, so they read
    the library :func:`start_runtime` or a backend started and never load one
    of their own.  ``reading`` names what the caller was doing, for the refusal.

    Raises:
        FFIError: the runtime has not started.

    """
    lib = RTSState.lib
    if not hs_initialized() or lib is None:
        msg = (
            "GHC runtime not initialized: call aletheia.start_runtime or open a client"
            f" before {reading}"
        )
        raise FFIError(msg)
    return lib


def allocated_bytes() -> AllocatedBytes | None:
    """Answer the bytes the kernel's runtime has allocated in this process since it started.

    The count covers the whole process, every session and thread, so the
    difference of two reads is what ran between them allocated.  It is read
    through the library :class:`RTSState` latched when the runtime started, and
    is ``None`` before it has.  Each read runs a garbage collection first, which
    a timed span should leave out.
    """
    lib = RTSState.lib
    if lib is None:
        return None
    count: AllocatedBytes = lib.aletheia_allocated_bytes()
    return count


# ``ALETHEIA_ABI_VERSION``: the version of the structures and signatures this
# binding lays out, which ``test_ffi_abi_version.py`` holds to the header's.
ABI_VERSION = 3


def check_abi_version(lib: ctypes.CDLL) -> None:
    """Refuse a library whose ABI version is not this binding's.

    Called before any other entry is resolved and before the GHC runtime
    starts, so a library laid out for another version runs nothing.  A library
    older than the version export lacks the symbol and is refused for that.
    """
    try:
        entry = lib.aletheia_abi_version
    except AttributeError as exc:
        msg = "the library has no aletheia_abi_version: it predates the versioned ABI"
        raise FFIError(msg) from exc
    entry.argtypes = []
    entry.restype = ctypes.c_uint32
    found: int = entry()
    if found != ABI_VERSION:
        msg = f"the library implements ABI version {found}, and this binding needs {ABI_VERSION}"
        raise FFIError(msg)


class AletheiaText(ctypes.Structure):  # pylint: disable=too-few-public-methods
    """``struct aletheia_text``: ``size`` bytes of UTF-8 from ``data``, no NUL after them."""

    _fields_ = (
        ("data", ctypes.c_char_p),
        ("size", ctypes.c_size_t),
    )


class AletheiaFrame(ctypes.Structure):  # pylint: disable=too-few-public-methods
    """``struct aletheia_frame``: one CAN frame, passed by pointer.

    The layout is ``haskell-shim/include/aletheia.h``'s; ``test_ffi_abi_layout.py`` pins
    every offset and the size against the table there.
    """

    _fields_ = (
        ("timestamp", ctypes.c_uint64),
        ("data", ctypes.POINTER(ctypes.c_uint8)),
        ("can_id", ctypes.c_uint32),
        ("extended", ctypes.c_uint8),
        ("dlc", ctypes.c_uint8),
        ("data_len", ctypes.c_uint8),
        ("brs_present", ctypes.c_uint8),
        ("brs_value", ctypes.c_uint8),
        ("esi_present", ctypes.c_uint8),
        ("esi_value", ctypes.c_uint8),
    )


class AletheiaSignalValues(ctypes.Structure):  # pylint: disable=too-few-public-methods
    """``struct aletheia_signal_values``: parallel signal indices and rationals."""

    _fields_ = (
        ("indices", ctypes.POINTER(ctypes.c_uint32)),
        ("numerators", ctypes.POINTER(ctypes.c_int64)),
        ("denominators", ctypes.POINTER(ctypes.c_int64)),
        ("count", ctypes.c_uint32),
    )


class AletheiaBuffer(ctypes.Structure):  # pylint: disable=too-few-public-methods
    """``struct aletheia_buffer``: a binary result and its error message."""

    _fields_ = (
        ("data", ctypes.POINTER(ctypes.c_uint8)),
        # A raw address, not ``c_char_p``, so the string can be freed after reading.
        ("err", ctypes.c_void_p),
        ("size", ctypes.c_uint32),
    )


class AletheiaRational(ctypes.Structure):  # pylint: disable=too-few-public-methods
    """``struct aletheia_rational``: an exact rational."""

    _fields_ = (
        ("numerator", ctypes.c_int64),
        ("denominator", ctypes.c_int64),
    )


class AletheiaDecimal(ctypes.Structure):  # pylint: disable=too-few-public-methods
    """``struct aletheia_decimal``: a parsed decimal, or the error the parser set."""

    _fields_ = (
        ("value", AletheiaRational),
        # A raw address, not ``c_char_p``, so the string can be freed after reading.
        ("err", ctypes.c_void_p),
    )


def take_error_envelope(
    lib: ctypes.CDLL, out: AletheiaBuffer | AletheiaDecimal, missing: Prose
) -> Response:
    """Read and free the error envelope a failed entry left in *out*.

    A failure without one is a wire fault, raised as :class:`ProtocolError`
    with *missing*.
    """
    err: KernelString | None = out.err
    if err is None:
        raise ProtocolError(missing)
    try:
        return cast("Response", parse_json_object(KernelResponse(ctypes.string_at(err))))
    finally:
        lib.aletheia_free_str(err)


def configure_ffi_signatures(lib: ctypes.CDLL) -> None:
    """Configure ``argtypes``/``restype`` for every Aletheia FFI entry point.

    Called once after the shared library is loaded.  Split out of
    ``AletheiaClient.__enter__`` so the client module stays focused on
    protocol flow rather than ctypes boilerplate.
    """
    # Core lifecycle + JSON command endpoint
    lib.aletheia_init.argtypes = []
    lib.aletheia_init.restype = ctypes.c_void_p
    lib.aletheia_process.argtypes = [ctypes.c_void_p, ctypes.POINTER(AletheiaText)]
    lib.aletheia_process.restype = ctypes.c_void_p
    lib.aletheia_free_str.argtypes = [ctypes.c_void_p]
    lib.aletheia_free_str.restype = None
    lib.aletheia_close.argtypes = [ctypes.c_void_p]
    lib.aletheia_close.restype = None

    # Binary frame endpoint (hot path: no JSON on input).  The frame crosses
    # as one ``struct aletheia_frame``; its CAN-FD BRS / ESI bits are
    # (present, value) byte pairs, present 0 for a CAN 2.0B frame
    # (ISO 11898-1:2015 section 10.4.2 / 10.4.3).
    frame_ptr = ctypes.POINTER(AletheiaFrame)
    values_ptr = ctypes.POINTER(AletheiaSignalValues)
    buffer_ptr = ctypes.POINTER(AletheiaBuffer)
    lib.aletheia_send_frame.argtypes = [ctypes.c_void_p, frame_ptr]
    lib.aletheia_send_frame.restype = ctypes.c_void_p

    # Binary entry points (no JSON parsing on input)
    lib.aletheia_start_stream.argtypes = [ctypes.c_void_p]
    lib.aletheia_start_stream.restype = ctypes.c_void_p
    lib.aletheia_end_stream.argtypes = [ctypes.c_void_p]
    lib.aletheia_end_stream.restype = ctypes.c_void_p
    lib.aletheia_format_dbc.argtypes = [ctypes.c_void_p]
    lib.aletheia_format_dbc.restype = ctypes.c_void_p
    lib.aletheia_extract_signals.argtypes = [ctypes.c_void_p, frame_ptr]
    lib.aletheia_extract_signals.restype = ctypes.c_void_p

    # CAN error/remote event endpoints (acknowledged without LTL evaluation)
    lib.aletheia_send_error.argtypes = [ctypes.c_void_p, frame_ptr]
    lib.aletheia_send_error.restype = ctypes.c_void_p
    lib.aletheia_send_remote.argtypes = [ctypes.c_void_p, frame_ptr]
    lib.aletheia_send_remote.restype = ctypes.c_void_p

    # Binary output entry points (no JSON on output either)
    lib.aletheia_build_frame_bin.argtypes = [ctypes.c_void_p, frame_ptr, values_ptr, buffer_ptr]
    lib.aletheia_build_frame_bin.restype = ctypes.c_int8
    lib.aletheia_update_frame_bin.argtypes = [ctypes.c_void_p, frame_ptr, values_ptr, buffer_ptr]
    lib.aletheia_update_frame_bin.restype = ctypes.c_int8
    lib.aletheia_extract_signals_bin.argtypes = [ctypes.c_void_p, frame_ptr, buffer_ptr]
    lib.aletheia_extract_signals_bin.restype = ctypes.c_int8
    lib.aletheia_free_buf.argtypes = [ctypes.POINTER(ctypes.c_uint8)]
    lib.aletheia_free_buf.restype = None

    # Cross-binding-identical Rational pretty-printer.
    # Returns a CString that the caller must free via ``aletheia_free_str``.
    # Display path only — bindings call this to render predicate values for
    # human-readable diagnostics.
    # The rational crosses as one ``struct aletheia_rational``; the shim moves
    # a negative denominator's sign to the numerator.
    lib.aletheia_format_rational.argtypes = [ctypes.POINTER(AletheiaRational)]
    lib.aletheia_format_rational.restype = ctypes.c_void_p

    # Cross-binding decimal → exact rational SSOT (the float principle).
    # Takes a decimal string and writes a ``struct aletheia_decimal``: the
    # rational on success (status 0), or on a parse failure / Int64 overflow
    # a ``{"status":"error",...}`` envelope in ``err`` (status 1), freed via
    # ``aletheia_free_str``.  Consumed by
    # ``aletheia.client._helpers.rational.from_decimal``.
    lib.aletheia_parse_decimal.argtypes = [
        ctypes.POINTER(AletheiaText),
        ctypes.POINTER(AletheiaDecimal),
    ]
    lib.aletheia_parse_decimal.restype = ctypes.c_int8

    # The bytes the runtime has allocated since it started, read after a
    # collection.  It needs the runtime started, so :func:`allocated_bytes`
    # calls it only on the library :class:`RTSState` latched.
    lib.aletheia_allocated_bytes.argtypes = []
    lib.aletheia_allocated_bytes.restype = ctypes.c_uint64


def _validate_lib_path(p: Path, source: str) -> None:
    """Reject a candidate ``libaletheia-ffi.so`` path that fails security gates.

    Applied to every resolution path — env var, install config, build dir,
    dist-newstyle scan.  Earlier versions restricted these checks to the
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
    # Permission hardening: refuse a path that any non-owner can write
    # to.  The env var is implicitly trusted
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
            msg = f"ALETHEIA_LIB={env_path} does not exist"
            raise FileNotFoundError(msg)
        _validate_lib_path(p, f"ALETHEIA_LIB={env_path}")
        return p

    # Check install config (generated by 'cabal run shake -- install').
    # _install_config.py is generated at install time and may not exist;
    # importlib.import_module lets us handle that without a top-level import.
    try:
        _install_config = importlib.import_module("aletheia._install_config")
        lib_path: Path = _install_config.LIBRARY_PATH
        if lib_path.exists():
            _validate_lib_path(lib_path, "install config")
            return lib_path
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
        "libaletheia-ffi.so not found. Build with: " + "cabal run shake -- build"
    )
