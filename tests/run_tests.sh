#!/usr/bin/env bash
#
# Test script for OpenQASM to Isabelle pipeline
#

set -e

# Colors for output
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m'

echo -e "${GREEN}Running OpenQASM to Isabelle Pipeline Tests${NC}"

# Get script directory
SCRIPT_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
PIPELINE_SCRIPT="$(dirname "$SCRIPT_DIR")/qasm_to_isabelle.py"

echo "Pipeline script: $PIPELINE_SCRIPT"

# Test 1: Hadamard gate
echo ""
echo -e "${YELLOW}Test 1: Hadamard Gate${NC}"
uv run python "$PIPELINE_SCRIPT" "$SCRIPT_DIR/hadamard_test.qasm" -n HadamardTest

# Test 2: CNOT gate
echo ""
echo -e "${YELLOW}Test 2: CNOT Gate${NC}"
uv run python "$PIPELINE_SCRIPT" "$SCRIPT_DIR/cnot_test.qasm" -n CNOTTest

# Test 3: Bell State
echo ""
echo -e "${YELLOW}Test 3: Bell State${NC}"
uv run python "$PIPELINE_SCRIPT" "$SCRIPT_DIR/bell_state.qasm" -n BellState

# Test 4: Quantum Teleportation
echo ""
echo -e "${YELLOW}Test 4: Quantum Teleportation${NC}"
uv run python "$PIPELINE_SCRIPT" "$SCRIPT_DIR/teleportation.qasm" -n Teleportation

echo ""
echo -e "${GREEN}All tests completed!${NC}"
echo "Generated theory files:"
ls -1 *.thy 2>/dev/null || echo "No theory files found in current directory"