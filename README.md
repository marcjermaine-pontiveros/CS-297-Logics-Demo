# CS-297-Logics
OpenQASM to Isabelle Quantum Hoare Logic Pipeline - Automated verification of quantum circuits

## Overview

This repository provides a complete pipeline for converting OpenQASM quantum circuits into Isabelle theory files for formal verification using Quantum Hoare Logic (QHL).

### Pipeline Architecture

```
OpenQASM → Qiskit → Isabelle Theory → Formal Verification
```

## Important: AFP Compatibility ⚠️

**AFP versions must match your Isabelle version!**

- **Isabelle2024**: Needs AFP-2024 (from SourceForge)
- **Isabelle2025**: Can use `afp-current.tar.gz`

The setup script downloads the current AFP by default. If you encounter compatibility errors, download the AFP version matching your Isabelle release from [SourceForge](https://sourceforge.net/projects/afp/files/).

## Quick Start

### 1. Automated Setup

Run the automated installation script to set up Isabelle and AFP:

```bash
./setup.sh
```

This will:
- Download and install Isabelle2024
- Download and configure the AFP (Archive of Formal Proofs)
- Register QHLProver with Isabelle
- Create configuration files

### 2. Install Python Dependencies

Using UV (recommended):

```bash
uv sync
```

Or using pip:

```bash
pip install -r requirements.txt
```

### 3. Convert OpenQASM to Isabelle

```bash
python3 qasm_to_isabelle.py tests/hadamard_test.qasm
```

This generates `hadamard_test_verify.thy` with formal verification lemmas.

## Environment Setup ✅

### Manual Setup

If you prefer manual setup or the automated script doesn't work:

1. Install Isabelle
   - Download **Isabelle2024** (or **Isabelle 2025-1**) from: https://isabelle.in.tum.de/

2. Download the AFP (Archive of Formal Proofs)
   - Clone the AFP repository: `git clone https://gitlab.in.tum.de/afp/afp.git`

3. Link the QHLProver session
   - From a terminal, tell Isabelle about the AFP thys directory:

```bash
isabelle components -u /path/to/your/afp/thys
```

4. Test in Isabelle/jEdit
   - Open Isabelle/jEdit and create a new theory containing:

```isabelle
imports "QHLProver.Quantum_Hoare"
```

If the background indicator turns green, the `QHLProver` environment is available and ready.

---

## Usage 🚀

### Command Line Interface

The main pipeline script `qasm_to_isabelle.py` provides a CLI for converting OpenQASM files:

```bash
# Basic usage
python3 qasm_to_isabelle.py circuit.qasm

# Custom output file
python3 qasm_to_isabelle.py circuit.qasm -o output.thy

# Custom theory name
python3 qasm_to_isabelle.py circuit.qasm -n MyCircuit

# Help
python3 qasm_to_isabelle.py --help
```

### Supported Gates

The pipeline supports the following quantum gates:

**Single-qubit gates:**
- H (Hadamard)
- X, Y, Z (Pauli gates)
- S, Sdg (Phase gates)
- T, Tdg (π/8 gates)

**Two-qubit gates:**
- CNOT (CX)
- CZ (Controlled-Z)
- SWAP

**Measurement:**
- Measure operations

### Examples

The `tests/` directory contains example quantum circuits:

```bash
# Run all tests
./tests/run_tests.sh

# Individual examples
python3 qasm_to_isabelle.py tests/hadamard_test.qasm
python3 qasm_to_isabelle.py tests/cnot_test.qasm
python3 qasm_to_isabelle.py tests/bell_state.qasm
python3 qasm_to_isabelle.py tests/teleportation.qasm
```

## Batch Processing 🔨

Build all generated theory files:

```bash
# Build all theories in current directory
./build_isabelle.sh

# Build with verbose output
./build_isabelle.sh -v

# Clean build
./build_isabelle.sh -c
```

## What Gets Proved? 📚

Isabelle uses *weakest preconditions* (wp) to symbolically reason about quantum circuits. For example, the Hadamard circuit proof shows:

```
H† ⋅ P₀ ⋅ H = (1/2) ⋅ I
```

This establishes that the acceptance observable equals one half the identity matrix for that quantum construction.

The pipeline automatically generates:
1. **Circuit definitions** in Isabelle QHL syntax
2. **Probability lemmas** for measurement outcomes
3. **Wellformedness lemmas** ensuring circuit validity

## Project Structure 📁

```
cs-297-logics/
├── qasm_to_isabelle.py    # Main pipeline script
├── setup.sh                # Isabelle & AFP installation
├── build_isabelle.sh       # Batch processing for theories
├── config.yaml             # Pipeline configuration
├── requirements.txt        # Python dependencies
├── example.py              # Original example (deprecated)
├── tests/                  # Test circuits
│   ├── hadamard_test.qasm
│   ├── cnot_test.qasm
│   ├── bell_state.qasm
│   ├── teleportation.qasm
│   └── run_tests.sh
└── README.md
```

