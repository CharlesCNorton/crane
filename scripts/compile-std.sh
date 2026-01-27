#!/bin/bash
# Compile C++ files with proper libc++ linking for Homebrew LLVM
# Usage: compile-std.sh output.exe source1.cpp source2.cpp ...

set -e

OUTPUT="$1"
shift
SOURCES="$@"

# Detect Homebrew LLVM
HB_LLVM="${HB_LLVM:-/opt/homebrew/opt/llvm}"

if [ -d "$HB_LLVM" ]; then
    # Use Homebrew LLVM with explicit libc++ linking
    exec "$HB_LLVM/bin/clang++" \
        -std=c++23 \
        -O2 \
        -I . \
        -nostdlib++ \
        -stdlib=libc++ \
        -I"$HB_LLVM/include/c++/v1" \
        -L"$HB_LLVM/lib" \
        -L"$HB_LLVM/lib/c++" \
        -Wl,-rpath,"$HB_LLVM/lib" \
        -Wl,-rpath,"$HB_LLVM/lib/c++" \
        $SOURCES \
        -lc++ -lc++abi \
        -o "$OUTPUT"
else
    # Fallback to system clang++
    exec clang++ -std=c++23 -O2 -I . $SOURCES -o "$OUTPUT"
fi
