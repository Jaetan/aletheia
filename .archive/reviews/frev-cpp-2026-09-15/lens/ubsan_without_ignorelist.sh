# Measurement, not a probe: builds the Excel tests under UBSan in a scratch copy
# of cpp/ with the sanitizer ignorelist withheld and recovery enabled, and
# lists every third-party site UBSan reports. Run from the repository root.
# Takes a few minutes; the result is recorded under base/ for the round.
set -u
R=$(pwd); X=$R/cpp/build/probe-scratch/ubsan-noignore
rm -rf "$X"; mkdir -p "$X"
for e in $(/bin/ls -A "$R"); do [ "$e" = cpp ] || ln -s "$R/$e" "$X/$e"; done
mkdir -p "$X/cpp" && (cd "$R/cpp" && git ls-files . | grep -v '^build' | tar -cf - -T -) | (cd "$X/cpp" && tar -xf -)
cd "$X/cpp" || exit 2
sed -i -e '/-fsanitize-ignorelist=/d' -e 's/-fno-sanitize-recover=undefined/-fsanitize-recover=undefined/' CMakeLists.txt
cmake -B build -DALETHEIA_SANITIZER=undefined -DCMAKE_C_COMPILER=clang-22 -DCMAKE_CXX_COMPILER=clang++-22 \
    -DFETCHCONTENT_SOURCE_DIR_JSON="$R/cpp/build/_deps/json-src" -DFETCHCONTENT_SOURCE_DIR_YAML-CPP="$R/cpp/build/_deps/yaml-cpp-src" \
    -DFETCHCONTENT_SOURCE_DIR_OPENXLSX="$R/cpp/build/_deps/openxlsx-src" -DFETCHCONTENT_SOURCE_DIR_CATCH2="$R/cpp/build/_deps/catch2-src" > /dev/null
cmake --build build --target excel_tests --parallel 4 > /dev/null
ALETHEIA_REPO_ROOT="$R" ALETHEIA_LIB="$R/build/libaletheia-ffi.so" ./build/excel_tests 2>&1 \
    | grep -oE '_deps/openxlsx-src/[^:]+:[0-9]+:[0-9]+: runtime error: [a-z ]+' | sed 's/:[0-9]*:[0-9]*: runtime error:/: /' | sort | uniq -c | sort -rn
