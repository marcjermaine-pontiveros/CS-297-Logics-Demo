theory BellState
  imports "QHLProver.Quantum_Hoare" "QHLProver.Gates"
begin

(* Auto-generated from OpenQASM *)
definition "quantum_circuit" :: "com" where
  "quantum_circuit = ((Utrans hadamard) ;; (Measure 0 (\<lambda>i. undefined) []) ;; (Measure 1 (\<lambda>i. undefined) []))"

declare "quantum_circuit_def" [simp]

end
