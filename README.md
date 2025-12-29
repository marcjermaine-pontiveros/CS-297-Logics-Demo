# OpenQASM to Isabelle Pipeline

Convert OpenQASM quantum circuits to formally verified Isabelle theories using Quantum Hoare Logic.

## Overview

This pipeline transforms quantum circuits written in OpenQASM into Isabelle theory files that can be formally verified using the QHLProver (Quantum Hoare Logic Prover) from the Archive of Formal Proofs.

**Pipeline:** `OpenQASM → Qiskit → Isabelle Theory → Formal Verification`

## Features

- ✅ **Multi-gate support**: H, X, Y, Z, S, T gates + measurements
- ✅ **QHLProver integration**: Compatible with Isabelle2025 + AFP-2025
- ✅ **Automated verification**: Generates provable circuit properties
- ✅ **CLI interface**: Easy command-line usage
- ✅ **Batch processing**: Process multiple circuits at once

## Quick Start

```bash
# 1. Install dependencies
uv sync

# 2. Generate theory from QASM
uv run python qasm_to_isabelle.py examples/hadamard.qasm

# 3. Verify the theory
bin/build.sh
```

## Project Structure

```
cs-297-logics/
├── qasm_to_isabelle.py    # Main pipeline script
├── examples/              # Example QASM circuits
├── bin/                   # Utility scripts
└── output/                # Generated theories
```

See [USAGE.md](USAGE.md) for detailed instructions and [SETUP.md](SETUP.md) for installation guide.