#!/usr/bin/env bash
#
# Verify individual Isabelle theory files via CLI
#

set -e

# Check arguments
if [ $# -eq 0 ]; then
    echo "Usage: $0 <theory_file.thy>"
    echo "Example: $0 HadamardTest.thy"
    exit 1
fi

THEORY_FILE="$1"

# Check if file exists
if [ ! -f "$THEORY_FILE" ]; then
    echo "Error: Theory file '$THEORY_FILE' not found"
    exit 1
fi

echo "🔍 Verifying: $THEORY_FILE"
echo ""

# Extract theory name (without .thy extension)
THEORY_NAME=$(basename "$THEORY_FILE" .thy)

# Use Isabelle CLI to process the theory
source ~/isabelle/isabelle-config.sh

echo "Building session QHL_Tests (this may take a few minutes on first run)..."
echo ""

# Build the entire session (which includes the theory)
isabelle build -v -D . QHL_Tests 2>&1 | tee /tmp/isabelle_build_$$.log | grep -E "(Building|Finished|FAILED|ERROR|$THEORY_NAME)" || true

# Check the result
if grep -q "FAILED" /tmp/isabelle_build_$$.log; then
    echo ""
    echo "❌ Verification FAILED for $THEORY_NAME"
    echo "Check errors with: isabelle build_log -H Error"
    exit 1
elif grep -q "QHL_Tests.*Finished" /tmp/isabelle_build_$$.log; then
    echo ""
    echo "✅ Verification SUCCESS for $THEORY_NAME"
    exit 0
else
    echo ""
    echo "⏳ Build still in progress or inconclusive"
    echo "Check manually: isabelle build -D . QHL_Tests"
    exit 2
fi