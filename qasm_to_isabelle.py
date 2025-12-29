#!/usr/bin/env python3
"""
OpenQASM to Isabelle Quantum Hoare Logic Pipeline
Converts OpenQASM quantum circuits to Isabelle theory files for verification
"""

import argparse
import sys
from pathlib import Path
from typing import List, Tuple, Optional
import qiskit
from qiskit import QuantumCircuit
from qiskit.exceptions import QiskitError


class GateMapping:
    """Maps Qiskit gates to Isabelle QHLProver syntax"""

    # QHLProver uses matrix-based gates, not symbolic gate names
    # For now, we'll generate placeholder matrices that can be replaced
    GATES = {
        'h': 'hadamard',  # From Gates.hadamard
        'x': 'sigma_x',   # From Gates.sigma_x
        'y': 'sigma_y',   # From Gates.sigma_y
        'z': 'sigma_z',   # From Gates.sigma_z
    }

    @classmethod
    def get_gate(cls, gate_name: str) -> Optional[str]:
        return cls.GATES.get(gate_name.lower())


class QASMParseError(Exception):
    """Custom exception for QASM parsing errors"""
    pass


class CircuitExtractor:
    """Extracts quantum circuit information from QASM"""

    def __init__(self, qasm_str: str):
        self.qasm_str = qasm_str
        self.circuit = None
        self.num_qubits = 0
        self.num_clbits = 0

    def parse(self) -> QuantumCircuit:
        """Parse QASM string into Qiskit QuantumCircuit"""
        try:
            self.circuit = QuantumCircuit.from_qasm_str(self.qasm_str)
            self.num_qubits = self.circuit.num_qubits
            self.num_clbits = self.circuit.num_clbits
            return self.circuit
        except QiskitError as e:
            raise QASMParseError(f"Failed to parse QASM: {str(e)}")
        except Exception as e:
            raise QASMParseError(f"Unexpected error parsing QASM: {str(e)}")

    def extract_operations(self) -> List[Tuple[str, List[int]]]:
        """Extract operations as (gate_name, qubit_indices) tuples"""
        if not self.circuit:
            raise QASMParseError("Circuit not parsed yet")

        operations = []
        for instr in self.circuit.data:
            gate_name = instr.operation.name
            qubit_indices = [self.circuit.find_bit(q).index for q in instr.qubits]
            operations.append((gate_name, qubit_indices))

        return operations


class IsabelleTheoryGenerator:
    """Generates Isabelle theory files from quantum circuits"""

    def __init__(self, theory_name: str, circuit_name: str = "quantum_circuit"):
        self.theory_name = theory_name
        self.circuit_name = circuit_name

    def generate_header(self) -> str:
        """Generate theory file header"""
        return f'''theory {self.theory_name}
  imports "QHLProver.Quantum_Hoare" "QHLProver.Gates" "QHLProver.Grover"
begin

(* Auto-generated from OpenQASM *)
'''

    def generate_quantum_predicates(self, num_qubits: int) -> str:
        """Generate quantum predicate definitions for WLP analysis"""
        predicates = f"(* Quantum Predicates for {num_qubits}-qubit system *)\n"

        # Basic quantum state vectors
        predicates += "definition \"ket_zero\" :: \"complex Matrix.mat\" where\n"
        predicates += '  "ket_zero = (mat 2 1 (λ(i,j). if i = 0 then 1 else 0))"\n\n'

        predicates += "definition \"ket_one\" :: \"complex Matrix.mat\" where\n"
        predicates += '  "ket_one = (mat 2 1 (λ(i,j). if i = 1 then 1 else 0))"\n\n'

        # Projectors for measurement
        predicates += "definition \"proj_zero\" :: \"complex Matrix.mat\" where\n"
        predicates += '  "proj_zero = ket_zero * adjoint ket_zero"\n\n'

        predicates += "definition \"proj_one\" :: \"complex Matrix.mat\" where\n"
        predicates += '  "proj_one = ket_one * adjoint ket_one"\n\n'

        # Quantum predicates for post-conditions
        predicates += "definition \"P0\" :: \"nat ⇒ complex Matrix.mat\" where\n"
        predicates += '  "P0 q = proj_zero"\n\n'

        predicates += "definition \"P1\" :: \"nat ⇒ complex Matrix.mat\" where\n"
        predicates += '  "P1 q = proj_one"\n\n'

        return predicates

    def generate_circuit_definition(self, operations: List[Tuple[str, List[int]]]) -> str:
        """Generate quantum circuit definition in Isabelle syntax"""
        definition = f'definition "{self.circuit_name}" :: "com" where\n'
        definition += f'  "{self.circuit_name} = '

        if not operations:
            definition += 'SKIP"\n\n'
            return definition

        # Convert operations to Isabelle QHLProver syntax
        isabelle_ops = []
        for gate_name, indices in operations:
            # Handle measurement separately (it's not a gate)
            if gate_name.lower() == 'measure':
                # Generate proper measurement operator using projectors
                qubit_idx = indices[0]
                # Use proj_zero and proj_one from Grover theory
                # This creates a proper measurement operator
                isabelle_ops.append(f"(Measure {qubit_idx} (\\<lambda>k. if k = 0 then proj_zero else proj_one) [])")
                continue

            isabelle_gate = GateMapping.get_gate(gate_name)
            if not isabelle_gate:
                print(f"Warning: Gate '{gate_name}' not supported, skipping", file=sys.stderr)
                continue

            if len(indices) == 1:
                # Single-qubit gate using Utrans
                isabelle_ops.append(f"(Utrans {isabelle_gate})")
            elif len(indices) == 2:
                # Two-qubit gate (not yet fully supported)
                print(f"Warning: Two-qubit gate '{gate_name}' requires custom matrix definition", file=sys.stderr)
                isabelle_ops.append(f"(Utrans undefined)")
            else:
                print(f"Warning: {len(indices)}-qubit gate '{gate_name}' not fully supported", file=sys.stderr)
                isabelle_ops.append(f"(Utrans undefined)")

        # Join operations with sequential composition
        if isabelle_ops:
            if len(isabelle_ops) == 1:
                definition += f"{isabelle_ops[0]}\"\n\n"
            else:
                # Sequential composition: op1 ;; op2 ;; op3 ...
                # QHLProver uses Seq syntax
                composed = isabelle_ops[0]
                for op in isabelle_ops[1:]:
                    composed += f" ;; {op}"
                definition += f"({composed})\"\n\n"
        else:
            definition += 'SKIP"\n\n'

        return definition

    def generate_wlp_lemmas(self, operations: List[Tuple[str, List[int]]], num_qubits: int) -> str:
        """Generate WLP verification lemmas"""
        lemmas = "(* Weakest Liberal Precondition Analysis *)\n\n"

        # Check for measurements
        has_measurements = any(gate_name.lower() == 'measure' for gate_name, _ in operations)

        if has_measurements:
            lemmas += f"(* Circuit contains measurements - computing WLP for measurement probabilities *)\n\n"

            # WLP for measuring |0⟩
            lemmas += f"(* WLP: What must hold before circuit to measure |0⟩ with certainty? *)\n"
            lemmas += f'lemma "{self.circuit_name}_wlp_measure_zero":\n'
            lemmas += f'  assumes "d = 2"\n'
            lemmas += f'  shows "wlp {self.circuit_name} (P0 0) = hadamard * proj_zero * adjoint hadamard"\n'
            lemmas += f'  oops (* Requires state_sig locale and proper wlp setup *)\n\n'

            # WLP for measuring |1⟩
            lemmas += f"(* WLP: What must hold before circuit to measure |1⟩ with certainty? *)\n"
            lemmas += f'lemma "{self.circuit_name}_wlp_measure_one":\n'
            lemmas += f'  assumes "d = 2"\n'
            lemmas += f'  shows "wlp {self.circuit_name} (P1 0) = hadamard * proj_one * adjoint hadamard"\n'
            lemmas += f'  oops (* Requires state_sig locale and proper wlp setup *)\n\n'

            # Expected outcomes
            lemmas += f"(* Expected measurement probabilities from Hadamard *)\n"
            lemmas += f'lemma "{self.circuit_name}_hadamard_probs":\n'
            lemmas += f'  assumes "d = 2" and "initial_state = ket_zero"\n'
            lemmas += f'  shows "trace (proj_zero * hadamard * initial_state * adjoint initial_state * adjoint hadamard) = 1/2"\n'
            lemmas += f'  oops (* Actual probability computation *)\n\n'

        else:
            lemmas += f"(* Circuit without measurements - WLP for unitary transformations *)\n\n"

            # WLP for unitary circuits
            lemmas += f"(* WLP: What predicate ensures final state satisfies P? *)\n"
            lemmas += f'lemma "{self.circuit_name}_wlp_unitary":\n'
            lemmas += f'  assumes "d = 2" and "is_quantum_predicate P"\n'
            lemmas += f'  shows "wlp {self.circuit_name} P = adjoint hadamard * P * hadamard"\n'
            lemmas += f'  oops (* Requires wlp rules for Utrans *)\n\n'

        return lemmas

    def generate_verification_lemmas(self, operations: List[Tuple[str, List[int]]], num_qubits: int) -> str:
        """Generate verification lemmas"""
        lemmas = ""

        # Check which gates were used
        gates_used = set()
        for gate_name, _ in operations:
            gates_used.add(gate_name.lower())

        # Generate gate-specific verification lemmas
        if 'h' in gates_used:
            lemmas += f'''(* Gate Property: Hadamard is unitary *)
lemma "{self.circuit_name}_hadamard_unitary":
  "unitary hadamard"
  by (rule unitary_hadamard)

(* Gate Property: Hadamard dimensions *)
lemma "{self.circuit_name}_hadamard_dim":
  "hadamard \<in> carrier_mat 2 2"
  by (rule hadamard_dim)

(* Gate Property: Hadamard is Hermitian *)
lemma "{self.circuit_name}_hadamard_hermitian":
  "hermitian hadamard"
  by (rule hermitian_hadamard)

'''

        # Generate WLP analysis
        lemmas += self.generate_wlp_lemmas(operations, num_qubits)

        # Circuit well-formedness
        lemmas += f'''(* Circuit Well-formedness *)
lemma "{self.circuit_name}_well_com":
  "well_com {self.circuit_name}"
  oops (* Requires proper measurement and dimension setup *)

'''

        return lemmas

    def generate_footer(self) -> str:
        """Generate theory file footer"""
        return "end\n"

    def generate_theory(self, operations: List[Tuple[str, List[int]]], num_qubits: int) -> str:
        """Generate complete Isabelle theory file"""
        theory = self.generate_header()
        theory += self.generate_quantum_predicates(num_qubits)
        theory += self.generate_circuit_definition(operations)
        theory += self.generate_verification_lemmas(operations, num_qubits)
        theory += self.generate_footer()
        return theory


def process_qasm_file(qasm_file: Path, output_file: Optional[Path] = None,
                     theory_name: Optional[str] = None) -> str:
    """Process QASM file and generate Isabelle theory"""

    # Read QASM file
    try:
        qasm_content = qasm_file.read_text()
    except Exception as e:
        print(f"Error reading QASM file: {e}", file=sys.stderr)
        sys.exit(1)

    # Parse QASM
    extractor = CircuitExtractor(qasm_content)
    try:
        circuit = extractor.parse()
        operations = extractor.extract_operations()
    except QASMParseError as e:
        print(f"QASM parsing error: {e}", file=sys.stderr)
        sys.exit(1)

    # Generate theory name
    if theory_name is None:
        theory_name = qasm_file.stem + "_verify"

    # Generate Isabelle theory
    generator = IsabelleTheoryGenerator(theory_name)
    theory_content = generator.generate_theory(operations, extractor.num_qubits)

    # Determine output file
    if output_file is None:
        output_file = Path(f"{theory_name}.thy")

    # Write theory file
    try:
        output_file.write_text(theory_content)
        print(f"Generated Isabelle theory: {output_file}")
        print(f"  Circuit: {extractor.num_qubits} qubits, {extractor.num_clbits} classical bits")
        print(f"  Operations: {len(operations)}")
        return str(output_file)
    except Exception as e:
        print(f"Error writing theory file: {e}", file=sys.stderr)
        sys.exit(1)


def main():
    parser = argparse.ArgumentParser(
        description="Convert OpenQASM to Isabelle Quantum Hoare Logic theories",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  %(prog)s circuit.qasm                    # Generate circuit_verify.thy
  %(prog)s circuit.qasm -o output.thy      # Specify output file
  %(prog)s circuit.qasm -n MyTheory        # Custom theory name
  %(prog)s circuit.qasm --pretty           # Pretty print output
        """
    )

    parser.add_argument("qasm_file", type=Path,
                       help="Input OpenQASM file")
    parser.add_argument("-o", "--output", type=Path,
                       help="Output Isabelle theory file (default: NAME_verify.thy)")
    parser.add_argument("-n", "--name", type=str,
                       help="Theory name (default: derived from input file)")
    parser.add_argument("--version", action="version", version="%(prog)s 1.0")

    args = parser.parse_args()

    # Validate input file
    if not args.qasm_file.exists():
        print(f"Error: QASM file '{args.qasm_file}' not found", file=sys.stderr)
        sys.exit(1)

    # Process QASM file
    output_file = process_qasm_file(
        args.qasm_file,
        args.output,
        args.name
    )

    print(f"\nNext steps:")
    print(f"1. Open {output_file} in Isabelle/jEdit")
    print(f"2. Verify the proof obligations")
    print(f"3. Run 'isabelle build -D .' to build the theory")


if __name__ == "__main__":
    main()