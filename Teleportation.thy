theory Teleportation
  imports "QHLProver.Quantum_Hoare" "QHLProver.Gates"
begin

(* Auto-generated from OpenQASM *)
definition "quantum_circuit" :: "com" where
  "quantum_circuit = ((Utrans hadamard) ;; (Utrans hadamard) ;; (Measure 0 (\<lambda>i. undefined) []) ;; (Measure 1 (\<lambda>i. undefined) []) ;; (Utrans sigma_z) ;; (Measure 2 (\<lambda>i. undefined) []))"

declare "quantum_circuit_def" [simp]

end
