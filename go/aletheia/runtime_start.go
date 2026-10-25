//go:build cgo && linux

// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia

// The GHC runtime's start, once per process, which [StartRuntime] and
// [NewFFIBackend] share. The runtime is never finalised, since hs_exit does
// not allow a second start. The start records the entries of the library it
// started on that a caller outside a session reaches, the rational renderer,
// the decimal parser and [AllocatedBytes], so those reach the kernel through
// that library and never open one of their own.

// #cgo LDFLAGS: -ldl
//
// #include <dlfcn.h>
// #include <stdint.h>
// #include <stdlib.h>
//
// static uint32_t rt_call_abi_version(void *fn) {
//     return ((uint32_t (*)(void))fn)();
// }
// static uint32_t rt_call_processors(void *fn) {
//     return ((uint32_t (*)(void))fn)();
// }
// static uint64_t rt_call_allocated_bytes(void *fn) {
//     return ((uint64_t (*)(void))fn)();
// }
//
// // The runtime's argument vector, assembled by rtsInitArgv in rts.go, moves
// // into storage C owns: hs_init_with_rtsopts may keep the array and its
// // strings for the life of the process, and cgo forbids C to keep a Go
// // pointer past the call. Nothing frees them, because the runtime offers no
// // hook to release them and the leak is one small array and a few short
// // strings, allocated once. The Python, C++ and Rust bindings retain theirs
// // the same way (aletheia/client/_ffi.py, cpp/src/runtime_start.cpp,
// // rust/src/backend.rs).
// static char** g_alloc_argv(int n) {
//     return (char**)calloc((size_t)n, sizeof(char*));
// }
// static void g_set_argv(char **argv, int i, char *s) {
//     argv[i] = s;  // s is a CString the Go caller means to leak
// }
// static void call_hs_init_argv(void *fn, int argc, char **argv) {
//     // hs_init_with_rtsopts takes int* and char***; it may rewrite the local
//     // copies, stripping the span it consumed, and those copies are discarded.
//     ((void (*)(int*, char***))fn)(&argc, &argv);
// }
import "C"

import (
	"context"
	"fmt"
	"log/slog"
	"os"
	"path/filepath"
	"runtime"
	"strings"
	"sync"
	"unsafe"
)

// runtimeEntries are the entries of the library the runtime started on that a
// caller outside a session calls.
type runtimeEntries struct {
	allocatedBytes unsafe.Pointer
	formatRational unsafe.Pointer
	parseDecimal   unsafe.Pointer
	freeStr        unsafe.Pointer
}

// runtimeSymbols are what a start reads of a library: its start entry, its
// count of the CPUs the process may use, and the entries recorded if it is the
// library the runtime starts on.
type runtimeSymbols struct {
	hsInit     unsafe.Pointer
	processors unsafe.Pointer
	entries    runtimeEntries
}

var (
	hsInitMu sync.Mutex
	// started is the entries of the library the runtime started on, nil until
	// the runtime starts; hsInitCores is the core count it started with.
	started     *runtimeEntries
	hsInitCores int
)

// hsInitialized reports whether the GHC runtime has started. The renderer and
// the decimal parser ask before calling the kernel, so that they can answer an
// error rather than start the runtime themselves.
func hsInitialized() bool {
	hsInitMu.Lock()
	defer hsInitMu.Unlock()
	return started != nil
}

// startedEntries are the recorded entries, or the refusal of a caller reading
// a number while the runtime is down; reading names what it was doing.
func startedEntries(reading string) (*runtimeEntries, error) {
	hsInitMu.Lock()
	defer hsInitMu.Unlock()
	if started == nil {
		return nil, ffiError("GHC runtime not initialized: call aletheia.StartRuntime or open a client before " + reading)
	}
	return started, nil
}

// AllocatedBytes is how many bytes the kernel's runtime has allocated since
// it started, a count of the whole process as [StablePtrCount] is: the
// difference of two reads is what ran between them allocated. It answers
// false and no count until the runtime has started, and then reads the
// library it started on. Each read runs a collection first, since the runtime
// counts an allocation area only when it collects it, so a read belongs
// outside anything timed. The scaling benchmark reads it around a load.
func AllocatedBytes() (uint64, bool) {
	hsInitMu.Lock()
	entries := started
	hsInitMu.Unlock()
	if entries == nil {
		return 0, false
	}
	runtime.LockOSThread()
	defer runtime.UnlockOSThread()
	return uint64(C.rt_call_allocated_bytes(entries.allocatedBytes)), true
}

// openKernel opens libaletheia-ffi.so at libPath and refuses one laid out for
// another ABI before anything else is resolved or started. The caller pins the
// thread, dlerror being per thread, and owns the handle.
func openKernel(libPath string) (unsafe.Pointer, error) {
	// Clean does not reject a NUL, and C.CString would truncate at one,
	// opening a different path than the caller named.
	if strings.ContainsRune(libPath, 0) {
		return nil, validationError("libPath contains NUL byte")
	}
	cPath := C.CString(filepath.Clean(libPath))
	defer C.free(unsafe.Pointer(cPath))
	handle := C.dlopen(cPath, C.RTLD_NOW|C.RTLD_LOCAL)
	if handle == nil {
		return nil, ffiError("dlopen failed: " + C.GoString(C.dlerror()))
	}
	abiVersionFn, err := loadSym(handle, "aletheia_abi_version")
	if err == nil {
		err = abiVersionError(uint32(C.rt_call_abi_version(abiVersionFn)))
	}
	if err != nil {
		C.dlclose(handle)
		return nil, err
	}
	return handle, nil
}

// loadRuntimeSymbols resolves what a start reads of an opened library, its
// start entry first. The caller pins the thread.
func loadRuntimeSymbols(handle unsafe.Pointer) (runtimeSymbols, error) {
	names := []string{rtsInitSymbol, rtsProcessorsSymbol, "aletheia_allocated_bytes",
		"aletheia_format_rational", "aletheia_parse_decimal", "aletheia_free_str"}
	syms := make([]unsafe.Pointer, len(names))
	for i, name := range names {
		sym, err := loadSym(handle, name)
		if err != nil {
			return runtimeSymbols{}, err
		}
		syms[i] = sym
	}
	return runtimeSymbols{
		hsInit:     syms[0],
		processors: syms[1],
		entries:    runtimeEntries{allocatedBytes: syms[2], formatRational: syms[3], parseDecimal: syms[4], freeStr: syms[5]},
	}, nil
}

// coreCountRefusal is the refusal of a core count outside 1 to available, or
// empty for one inside it.
func coreCountRefusal(requested, available int) string {
	if requested >= 1 && requested <= available {
		return ""
	}
	return fmt.Sprintf("core count %d is outside 1 to %d, the CPUs this process may use", requested, available)
}

// startRuntimeOn starts the runtime on the library syms came from with cores
// capabilities, unless it runs; named false asks for the count running, the
// default when nothing runs. The count is held to 1 through the CPUs the
// process may use, as the runtime counts them, whether or not it runs. A
// runtime that runs keeps its count, and another count asked of it is logged
// as rts.cores_mismatch when logger is not nil. It answers whether this call
// started the runtime, whose library the caller then keeps open for good.
func startRuntimeOn(syms runtimeSymbols, cores int, named bool, logger *slog.Logger) (bool, error) {
	hsInitMu.Lock()
	defer hsInitMu.Unlock()
	asked := cores
	if !named {
		asked = rtsDefaultCores
		if started != nil {
			asked = hsInitCores
		}
	}
	if refusal := coreCountRefusal(asked, int(C.rt_call_processors(syms.processors))); refusal != "" {
		return false, validationError(refusal)
	}
	if started == nil {
		// The argument vector always carries the heap cap, whatever the core
		// count, so the host is contained either way. Its array and strings
		// are leaked on purpose, as the preamble explains.
		argv := rtsInitArgv(asked)
		cargv := C.g_alloc_argv(C.int(len(argv)))
		for i, s := range argv {
			C.g_set_argv(cargv, C.int(i), C.CString(s))
		}
		C.call_hs_init_argv(syms.hsInit, C.int(len(argv)), cargv)
		hsInitCores = asked
		entries := syms.entries
		started = &entries
		return true, nil
	}
	if asked != hsInitCores && logger != nil {
		logger.LogAttrs(context.Background(), slog.LevelWarn, "rts.cores_mismatch",
			slog.Int("active_cores", hsInitCores),
			slog.Int("requested_cores", asked))
	}
	return false, nil
}

// StartRuntime opens libaletheia-ffi.so at libPath and starts the kernel's GHC
// runtime on cores capabilities, unless it runs: 1 for one bus, the number of
// buses when several goroutines each monitor their own. The kernel reads
// every number a check carries ([FromDecimal], [LoadChecksFromYAML], the
// Excel loader), so a program that loads checks before it opens a client
// calls it first; a backend opened later without [WithRTSCores] asks for the
// count running. A runtime already up keeps its count, and another count
// asked of it is logged as rts.cores_mismatch on logger; a nil logger logs
// nothing.
//
// Errors: [ErrValidation] for a count outside 1 to the CPUs the process may
// use, or a path holding a NUL; [ErrFFI] when the library cannot be opened,
// is laid out for another ABI version, or lacks an entry the start reads.
func StartRuntime(libPath string, cores int, logger *slog.Logger) error {
	// dlerror is per thread, so the lookups below must not migrate.
	runtime.LockOSThread()
	defer runtime.UnlockOSThread()
	handle, err := openKernel(libPath)
	if err != nil {
		return err
	}
	syms, err := loadRuntimeSymbols(handle)
	startedHere := false
	if err == nil {
		startedHere, err = startRuntimeOn(syms, cores, true, logger)
	}
	// The library the runtime starts on stays open, since the runtime owns
	// threads that reference it; any other was opened only to be read.
	if !startedHere {
		C.dlclose(handle)
	}
	return err
}

// StartRuntimeFromEnv is [StartRuntime] on the library ALETHEIA_LIB names,
// which is what a bundled install exports. An unset or empty variable is a
// validation error.
func StartRuntimeFromEnv(cores int, logger *slog.Logger) error {
	libPath := os.Getenv("ALETHEIA_LIB")
	if libPath == "" {
		return validationError(
			"ALETHEIA_LIB is not set: set it to the path of libaletheia-ffi.so, or use StartRuntime(path, cores, logger)")
	}
	return StartRuntime(libPath, cores, logger)
}
