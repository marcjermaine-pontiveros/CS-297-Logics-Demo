theory HadamardVerify
  imports "QHLProver.Quantum_Hoare"
begin

(* Auto-generated from Qiskit *)
definition "hello_circuit" :: "qcmd" where
  "hello_circuit = (QUnit H_gate [0]) ((QMeas 0 skip skip))"

lemma "probability_is_half":
  "wp hello_circuit (P0 0) = (1/2) * Id"
proof -
  show ?thesis
    unfolding hello_circuit_def
    by (simp add: wp_simps matrix_arith)
qed

end