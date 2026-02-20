#!/bin/bash
# Run Facebook Infer static analysis on all test C++ files
# Usage: ./scripts/run-infer.sh

set -e

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd -P)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd -P)"
THEORIES_CPP="$PROJECT_ROOT/theories/cpp"
TESTS_DIR="$PROJECT_ROOT/tests"

# Infer ships its own clang, so we just need a clang++ on PATH for the
# compiler driver name.  Do NOT pass Homebrew LLVM libc++ include paths or
# -nostdlib++/-stdlib=libc++ flags — they conflict with infer's bundled
# clang-18 headers.
CXX="clang++"
CXX_FLAGS="-std=c++23 -fbracket-depth=1024 -I $THEORIES_CPP"

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
CYAN='\033[0;36m'
BOLD='\033[1m'
NC='\033[0m'

echo ""
echo -e "${BOLD}Running Infer on Crane test files${NC}"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""

# Collect all source files
FILES=$(find "$TESTS_DIR" -path '*/wip/*' -prune -o -type f \( -name '*.h' -o -name '*.cpp' -o -name '*.t.cpp' \) -print | sort)

file_count=$(echo "$FILES" | wc -l | tr -d ' ')
echo -e "Found ${CYAN}${file_count}${NC} source files"
echo ""

# Temporary directory for object files
TMPDIR="${TMPDIR:-/tmp}"
OBJ_DIR="$TMPDIR/crane_infer_$$"
mkdir -p "$OBJ_DIR"
trap "rm -rf $OBJ_DIR" EXIT

# Clean previous Infer output
rm -rf "$PROJECT_ROOT/infer-out"

# Capture phase: run infer on each file individually
capture_errors=0
file_index=0
for file in $FILES; do
    rel_path="${file#$PROJECT_ROOT/}"
    file_dir="$(dirname "$file")"

    echo -e "  Analyzing ${CYAN}${rel_path}${NC}"

    obj_file="$OBJ_DIR/out_${file_index}.o"
    file_index=$((file_index + 1))

    # Run infer capture for this file.
    # Use --continue so each invocation appends to the capture DB rather
    # than replacing it. The file's own directory is added as an include
    # path so sibling headers resolve.
    if ! infer capture --continue --no-progress-bar -- \
        "$CXX" $CXX_FLAGS -I "$file_dir" -c "$file" -o "$obj_file" 2>/dev/null; then
        echo -e "    ${RED}capture failed${NC}"
        capture_errors=$((capture_errors + 1))
    fi
done

echo ""
echo -e "${BOLD}Running analysis...${NC}"
echo ""

# Analyze all captured files
infer analyze --no-progress-bar

# Print results
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"

REPORT="$PROJECT_ROOT/infer-out/report.txt"

if [ -f "$REPORT" ] && [ -s "$REPORT" ]; then
    warning_count=$(wc -l < "$REPORT" | tr -d ' ')
    echo -e "${BOLD}${RED}Infer warnings:${NC}"
    echo ""
    cat "$REPORT"
    echo ""
    echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
    echo -e "${BOLD}${RED}${warning_count} warning(s) found${NC}"
else
    echo -e "${BOLD}${GREEN}No warnings found${NC}"
fi

if [ $capture_errors -gt 0 ]; then
    echo -e "${RED}${capture_errors} file(s) failed to capture${NC}"
fi

echo ""
