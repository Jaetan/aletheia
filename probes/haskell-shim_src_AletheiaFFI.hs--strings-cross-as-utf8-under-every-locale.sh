#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes haskell-shim/src/AletheiaFFI.hs.
# Claim: the kernel's string entries read every byte the caller passes as
# UTF-8 and answer UTF-8, whatever the locale of the process that loaded the
# library.
# aletheia_parse_decimal refuses as not UTF-8 exactly the byte strings Python's
# strict decoder refuses, over a corpus of valid sequences, overlong encodings,
# surrogates, code points past U+10FFFF, truncated sequences and stray
# continuation bytes, each placed between digits so that dropping it would
# leave a literal; a NUL between digits is refused rather than read as the
# end of the text; aletheia_process refuses a command that is not UTF-8 and one
# holding a NUL; and a non-ASCII unit comes back whole. Each is run in a process whose locale is C
# and in one whose locale is C.UTF-8, and the two must answer alike. Non-zero
# exit: a disagreement with Python, bytes read without the ones that are not
# UTF-8, a unit changed on the way back, a child that did not get the locale it
# was given, or two locales answering differently. Exits 0 with a note when the
# library is not built. PROBE_LIB points it at another build of the library.
set -u
cd "$(dirname "$0")/.." || exit 2
lib=${PROBE_LIB:-build/libaletheia-ffi.so}
py=python/.venv/bin/python
[ -f "$lib" ] || { echo "kernel not built, claim untestable"; exit 0; }
[ -x "$py" ] || exit 2

# One child under the locale named by $1: every check, one line per answer,
# then a FAIL line per failed check, exiting non-zero when there is one.
run_child() {
    env -i PATH="$PATH" LC_ALL="$1" "$py" - "$lib" "$1" <<'PY'
import ctypes
import json
import locale
import sys

lib_path, want_locale = sys.argv[1], sys.argv[2]
got_locale = locale.setlocale(locale.LC_CTYPE)
if got_locale != want_locale:
    print(f"the child runs under LC_CTYPE {got_locale!r}, not {want_locale!r}")
    sys.exit(1)

lib = ctypes.CDLL(lib_path)
argc = ctypes.c_int(1)
argv = (ctypes.c_char_p * 2)(ctypes.c_char_p(b"probe"), None)
lib.hs_init(ctypes.byref(argc), ctypes.byref(ctypes.cast(argv, ctypes.POINTER(ctypes.c_char_p))))


class Text(ctypes.Structure):
    _fields_ = [("data", ctypes.c_char_p), ("size", ctypes.c_size_t)]


def text(raw):
    return ctypes.byref(Text(raw, len(raw)))


class Decimal(ctypes.Structure):
    _fields_ = [("numerator", ctypes.c_int64), ("denominator", ctypes.c_int64), ("err", ctypes.c_void_p)]


lib.aletheia_parse_decimal.argtypes = [ctypes.POINTER(Text), ctypes.POINTER(Decimal)]
lib.aletheia_parse_decimal.restype = ctypes.c_int8
lib.aletheia_free_str.argtypes = [ctypes.c_void_p]
lib.aletheia_init.restype = ctypes.c_void_p
lib.aletheia_process.argtypes = [ctypes.c_void_p, ctypes.POINTER(Text)]
lib.aletheia_process.restype = ctypes.c_void_p
lib.aletheia_close.argtypes = [ctypes.c_void_p]


def take(pointer):
    try:
        return ctypes.string_at(pointer)
    finally:
        lib.aletheia_free_str(pointer)


NOT_UTF8 = "input is not valid UTF-8"
NUL = "input contains a NUL byte"
CORPUS = [
    "", "41", "7f", "c2 80", "df bf", "e0 a0 80", "ef bf bf", "f0 90 80 80", "f4 8f bf bf",
    "c3 a9 e2 82 ac f0 9f 98 80",
    "c0 80", "c1 bf", "e0 80 80", "e0 9f bf", "f0 80 80 80", "f0 8f bf bf",
    "ed a0 80", "ed bf bf", "ed 9f bf", "ee 80 80", "f4 90 80 80", "f5 80 80 80",
    "f8 88 80 80 80", "80", "bf", "c2", "e0 a0", "f0 90 80", "c2 41", "e2 82", "ff", "fe",
]
failures = []
for row in CORPUS:
    middle = bytes(int(h, 16) for h in row.split())
    try:
        middle.decode("utf-8")
        python_says = "utf-8"
    except UnicodeDecodeError:
        python_says = "not utf-8"
    out = Decimal()
    if lib.aletheia_parse_decimal(text(b"1" + middle + b"5"), ctypes.byref(out)) == 0:
        kernel_says = f"accepted {out.numerator}/{out.denominator}"
    else:
        message = json.loads(take(out.err))["message"]
        kernel_says = "not utf-8" if message == NOT_UTF8 else "refused as a literal"
    print(f"decimal [{row}]: {kernel_says}")
    if python_says == "not utf-8" and kernel_says != "not utf-8":
        failures.append(f"[{row}] is not UTF-8 and the kernel answered {kernel_says}")
    elif python_says == "utf-8" and kernel_says == "not utf-8":
        failures.append(f"[{row}] is UTF-8 and the kernel refused it as not UTF-8")
    elif python_says == "utf-8" and middle and kernel_says.startswith("accepted"):
        failures.append(f"[{row}] is not a digit and the kernel answered {kernel_says}")

out = Decimal()
status = lib.aletheia_parse_decimal(text(b"1\x005"), ctypes.byref(out))
answer = f"accepted {out.numerator}/{out.denominator}" if status == 0 else json.loads(take(out.err))["message"]
print(f"decimal with a NUL between digits: {answer}")
if answer != NUL:
    failures.append(f"a NUL between digits was answered {answer}")

state = lib.aletheia_init()
for command, reason in (
    (b'{"type":"command","command":"no\xff"}', NOT_UTF8),
    (b'{"type":"command","command":"validateDBC"}\x00{}', NUL),
):
    refused = json.loads(take(lib.aletheia_process(state, text(command))))
    print(f"process {command!r}: {refused}")
    if refused.get("code") != "ffi_validation_error" or refused.get("message") != reason:
        failures.append(f"the command {command!r} was answered {refused}")
signal = ('{"name":"T","startBit":0,"length":16,"byteOrder":"little_endian","signed":false,'
          '"factor":1,"offset":0,"minimum":0,"maximum":65535,"unit":"°C",'
          '"presence":"always","receivers":[]}')
command = ('{"type":"command","command":"parseDBC","dbc":{"version":"1.0","messages":[{'
           '"id":256,"name":"M","dlc":8,"sender":"ECU","extended":false,"signals":['
           + signal + ']}],"environmentVars":[]}}')
loaded = json.loads(take(lib.aletheia_process(state, text(command.encode("utf-8")))))
unit = loaded["dbc"]["messages"][0]["signals"][0]["unit"] if loaded.get("status") == "success" else loaded
print(f"unit: {unit!r}")
if unit != "°C":
    failures.append(f"the unit came back as {unit!r}")
lib.aletheia_close(state)

for line in failures:
    print(f"FAIL {line}")
sys.exit(1 if failures else 0)
PY
}

status=0
c_out=$(run_child C) || status=1
utf8_out=$(run_child C.UTF-8) || status=1
grep '^FAIL\|^the child' <<< "$c_out" | sed 's/^/LC_ALL=C: /'
grep '^FAIL\|^the child' <<< "$utf8_out" | sed 's/^/LC_ALL=C.UTF-8: /'
if [ "$c_out" != "$utf8_out" ]; then
    echo "the two locales answered differently:"
    diff <(echo "$c_out") <(echo "$utf8_out")
    status=1
fi
[ "$status" -eq 0 ] && echo "$(grep -c '^decimal \[' <<< "$c_out") byte sequences, both locales alike"
exit "$status"
