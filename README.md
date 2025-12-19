# CS-297-Logics
My final paper on CS 297 Logics for Verified Systems, focusing on Quantum Hoare Logic

---

## Environment Setup ✅

Follow these steps before running any code in this repo.

1. Install Isabelle
   - Download **Isabelle2024** (or **Isabelle 2025-1**) from the official site: https://isabelle.in.tum.de/

2. Download the AFP (Archive of Formal Proofs)
   - Obtain the AFP archive and extract it somewhere on your system.

3. Link the QHLProver session
   - From a terminal, tell Isabelle about the AFP thys directory:

```bash
isabelle components -u /path/to/your/afp/thys
```

This command registers AFP sessions (including `QHLProver`) with your local Isabelle installation.

4. Test in Isabelle/jEdit
   - Open Isabelle/jEdit and create a new theory containing:

```isabelle
imports "QHLProver.Quantum_Hoare"
```

If the background indicator turns green, the `QHLProver` environment is available and ready.

---

## "Hello World" Pipeline (Python) 🔧

This repo includes a minimal pipeline to convert an OpenQASM description into an Isabelle theory that uses the QHLProver.

- Steps: OpenQASM → Qiskit → Isabelle
- Main script: `example.py`

Example usage (the script generates `HadamardVerify.thy`):

```python
import qiskit
from qiskit import QuantumCircuit

def generate_hello_world_verification(qasm_str):
    # 1. OpenQASM -> Qiskit
    qc = QuantumCircuit.from_qasm_str(qasm_str)
    
    # 2. Transpile to Isabelle
    theory_name = "HadamardVerify"
    isabelle_content = f"""theory {theory_name}
  imports "QHLProver.Quantum_Hoare"
begin

(* Auto-generated from Qiskit *)
definition "hello_circuit" :: "qcmd" where
  "hello_circuit = """
    
    # Logic to convert Qiskit data to Isabelle QHL syntax
    ops = []
    for instr in qc.data:
        name = instr.operation.name
        indices = [qc.find_bit(q).index for q in instr.qubits]
        if name == 'h':
            ops.append(f"(QUnit H_gate {indices})")
        elif name == 'measure':
            ops.append(f"(QMeas {indices[0]} skip skip)")

    # Join operations with QSeq (Sequential Composition)
    isabelle_content += f"{ops[0]} ({ops[1]})" if len(ops) > 1 else ops[0]
    isabelle_content += '"\n\n'

    # 3. Add the Verification Lemma
    isabelle_content += f"""lemma "probability_is_half":
  "wp hello_circuit (P0 0) = (1/2) * Id"
proof -
  show ?thesis
    unfolding hello_circuit_def
    by (simp add: wp_simps matrix_arith)
qed

end"""

    with open(f"{theory_name}.thy", "w") as f:
        f.write(isabelle_content)
    print(f"File {theory_name}.thy generated successfully!")

# --- The QASM Input ---
qasm_input = """
OPENQASM 2.0;
include "qelib1.inc";
qreg q[1];
creg c[1];
h q[0];
measure q[0] -> c[0];
"""

generate_hello_world_verification(qasm_input)
```

---

## Running the "Hello World" Proof

1. Run the Python script locally:

```bash
python3 example.py
```

2. Open the generated `HadamardVerify.thy` in Isabelle/jEdit.
   - Isabelle will build the `QHLProver` image on first import; this can take a minute.

3. Scroll to the lemma at the bottom.
   - If the line `by (simp add: wp_simps matrix_arith)` evaluates (turns white/green), the proof is verified.

---

## What this proves (short)

Isabelle uses *weakest preconditions* (wp) to symbolically reason about the circuit. For the Hadamard example, the proof shows:

H^
\dagger P_{|0\rangle} H = (1/2) I

which establishes that the acceptance observable equals one half the identity for that construction.

