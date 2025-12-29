# 🚀 Quick Start - OpenQASM to Verified Isabelle Theory

## Generate Your First Verified Quantum Circuit

### Step 1: Create Your QASM Circuit

Create `my_circuit.qasm`:

```qasm
OPENQASM 2.0;
include "qelib1.inc";
qreg q[1];
creg c[1];
h q[0];
measure q[0] -> c[0];
```

### Step 2: Generate Isabelle Theory

```bash
uv run python qasm_to_isabelle.py my_circuit.qasm
```

**Output:** Generates `my_circuit_verify.thy` with:
- ✅ Circuit definition in QHLProver syntax
- ✅ Import statements for Isabelle verification
- ✅ Verification lemmas for gate properties

### Step 3: Verify the Theory

```bash
./bin/build.sh
```

**Expected Output:**
```
Finished QHL_Tests (0:00:03 elapsed time)
```

🎉 **Your quantum circuit is now formally verified!**

## What Just Happened?

1. **QASM Parsing** → Your circuit was converted to Qiskit
2. **Gate Extraction** → Quantum gates were identified
3. **QHLProver Generation** → Created Isabelle syntax
4. **Formal Verification** → Proved properties about your circuit

## View Your Verified Theory

```bash
# See the generated file
cat my_circuit_verify.thy

# Open in Isabelle/jEdit (interactive)
isabelle jedit my_circuit_verify.thy
```

**What you'll see:**
- Green highlighted lemmas = ✅ **PROVEN**
- Circuit structure verification
- Gate properties (unitary, dimensions, etc.)

## Try More Examples

```bash
# Generate all example circuits
cd examples
./run_examples.sh

# Build and verify all
cd ..
./bin/build.sh

# Check results
isabelle build -v -D . QHL_Tests
```

## Common Issues

**"Gate not supported"**
- Your circuit uses unsupported gates
- Check the supported gates list

**Build fails**
- Ensure Isabelle + AFP are installed: `./bin/setup.sh`
- Check versions match Isabelle2025 + AFP-2025

**Want to see what got proven?**
```bash
isabelle build -v -D . QHL_Tests | grep lemma
```

## Next Steps

- 📖 Read [USAGE.md](USAGE.md) for detailed documentation
- 🔧 Check [SETUP.md](SETUP.md) for installation help
- 💡 Explore `examples/` for more circuits