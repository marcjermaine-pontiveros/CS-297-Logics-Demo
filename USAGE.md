# Usage Guide - OpenQASM to Isabelle Pipeline

## Basic Usage

### Generate Theory from QASM

```bash
python3 qasm_to_isabelle.py <input.qasm> [options]
```

**Options:**
- `-o, --output FILE`: Specify output file
- `-n, --name NAME`: Custom theory name
- `-h, --help`: Show help message

**Examples:**

```bash
# Basic usage
python3 qasm_to_isabelle.py examples/hadamard.qasm

# Custom output
python3 qasm_to_isabelle.py examples/bell_state.qasm -o MyCircuit.thy

# Custom theory name
python3 qasm_to_isabelle.py examples/teleportation.qasm -n Teleport
```

## Complete Workflow

### 1. Create Your QASM Circuit

Create `my_circuit.qasm`:

```qasm
OPENQASM 2.0;
include "qelib1.inc";
qreg q[2];
creg c[2];
h q[0];
cx q[0],q[1];
measure q -> c;
```

### 2. Generate Isabelle Theory

```bash
python3 qasm_to_isabelle.py my_circuit.qasm
```

This generates `my_circuit_verify.thy` with:
- Circuit definition in QHLProver syntax
- Import statements for Quantum_Hoare and Gates
- Basic verification lemmas

### 3. Verify the Theory

**Option A: CLI Build**
```bash
./bin/build.sh
```

**Option B: Individual verification**
```bash
./bin/verify.sh my_circuit_verify.thy
```

**Option C: Interactive**
```bash
isabelle jedit my_circuit_verify.thy
```

### 4. Check Verification Results

```bash
# See build status
isabelle build -v -D . QHL_Tests | grep my_circuit

# View detailed logs
isabelle build_log -v QHL_Tests
```

## Supported Quantum Gates

### Single-Qubit Gates
- **H**: Hadamard gate
- **X, Y, Z**: Pauli gates
- **S, Sdg**: Phase gates
- **T, Tdg**: π/8 gates

### Two-Qubit Gates
- **CX**: CNOT gate (limited support)
- **CZ**: Controlled-Z (limited support)

### Measurements
- **measure**: Quantum measurement operations

## Example Workflow

```bash
# 1. Run all example circuits
cd examples
./run_examples.sh

# 2. Build all generated theories
cd ..
./bin/build.sh

# 3. Check verification results
isabelle build -D . QHL_Tests

# Expected output:
# Finished QHL_Tests (0:00:03 elapsed time, 0:00:03 cpu time, factor 1.07)
```

## Understanding Generated Theories

Your generated theory file will contain:

```isabelle
theory MyCircuit
  imports "QHLProver.Quantum_Hoare" "QHLProver.Gates"
begin

definition "quantum_circuit" :: "com" where
  "quantum_circuit = ((Utrans hadamard) ;; (Measure 0 (\<lambda>i. undefined) []))"

(* Verification lemmas *)
lemma "hadamard_is_unitary":
  "unitary hadamard"
  by (rule unitary_hadamard)

lemma "circuit_structure":
  "quantum_circuit = (Utrans hadamard ;; Measure 0 (\<lambda>i. undefined) [])"
  by (simp add: quantum_circuit_def)

end
```

## Troubleshooting

### "Gate not supported" warning
- Your QASM uses a gate not yet implemented
- Check supported gates list above
- Consider using different gates or extending the pipeline

### Build failures
- Check Isabelle/AFP versions match
- Verify imports are correct
- Check QHLProver session builds: `isabelle build AFP/QHLProver`

### Verification lemmas not proving
- Some lemmas use `undefined` for measurements (placeholder)
- Circuit definitions are correct, but measurement properties need custom matrices
- Focus on gate properties (unitary, dimensions) which do prove

## Advanced Usage

### Batch Processing

```bash
# Process multiple QASM files
for circuit in examples/*.qasm; do
    python3 qasm_to_isabelle.py "$circuit"
done

# Build all
./bin/build.sh
```

### Custom Verification Lemmas

Edit the generated `.thy` file to add custom proofs:

```isabelle
(* Add your own verification lemma *)
lemma "my_custom_property":
  "some_property quantum_circuit"
  apply (simp add: quantum_circuit_def)
  (* your proof steps *)
  oops
```

## Pipeline Architecture

```
OpenQASM Input → Qiskit Parsing → Gate Extraction → QHLProver Syntax Generation
                   ↓                              ↓
              QuantumCircuit              Isabelle Theory File
                   ↓                              ↓
            Gate Operations          Formal Verification
```

## Next Steps

- See [SETUP.md](SETUP.md) for installation
- Check `examples/` directory for sample circuits
- Read QHLProver documentation for advanced verification techniques