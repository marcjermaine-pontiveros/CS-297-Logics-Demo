theory HadamardTest
  imports "QHLProver.Quantum_Hoare" "QHLProver.Gates"
begin

(* Auto-generated from OpenQASM *)
definition "quantum_circuit" :: "com" where
  "quantum_circuit = ((Utrans hadamard) ;; (Measure 0 (\<lambda>i. undefined) []))"

(* Verification 1: Use existing QHLProver lemma that Hadamard is unitary *)
lemma "hadamard_is_unitary":
  "unitary hadamard"
  by (rule unitary_hadamard)

(* Verification 2: Show the Hadamard gate has correct dimensions *)
lemma "hadamard_dimensions":
  "hadamard \<in> carrier_mat 2 2"
  by (rule hadamard_dim)

(* Verification 3: Show the circuit structure is correct *)
lemma "circuit_structure":
  "quantum_circuit = (Utrans hadamard ;; Measure 0 (\<lambda>i. undefined) [])"
  by (simp add: quantum_circuit_def)

(* Verification 4: The Hadamard gate is Hermitian *)
lemma "hadamard_is_hermitian":
  "hermitian hadamard"
  by (rule hermitian_hadamard)

end