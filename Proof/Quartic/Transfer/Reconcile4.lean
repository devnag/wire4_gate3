import Proof.Quartic.Transfer.Transfer4
import Proof.Quartic.Statement.Final

/-!
# The working statement implies the official statement of `thm:main`

`MainStatement4` (stated with `SymmetricThresholdCircuit.wireCount = Σ_i (|support T_i| + 1)` and
`NearCubicWires.agreement`) implies `NearQuarticWires.Statement.FinalStatement4` (stated with
`wires C = G + Σ_i f_i` and `agr`): the two wire counts are equal because a gate's support is exactly its set of
nonzero weights, and the two agreements are the same formula.
-/

set_option autoImplicit false

namespace NearQuarticWires.Transfer

open NearCubicWires NearCubicGates.Target

theorem wireCount_eq_wires {n : ℕ} (C : SymmetricThresholdCircuit n) :
    C.wireCount = NearQuarticWires.Statement.wires C := by
  classical
  unfold SymmetricThresholdCircuit.wireCount NearQuarticWires.Statement.wires NearQuarticWires.Statement.fanIn
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
  rw [add_comm]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  ext l
  simp [(C.bottom i).mem_support_iff l]

theorem mainStatement4_official (h : MainStatement4) : NearQuarticWires.Statement.FinalStatement4 := by
  obtain ⟨γ, h0, h1, hm⟩ := h
  refine ⟨γ, h0, h1, fun d hd hdγ => ?_⟩
  obtain ⟨K, hK, F, hF, n₀, hn₀, hhard⟩ := hm d hd hdγ
  refine ⟨K, hK, F, hF, n₀, hn₀, fun n hn C hC => ?_⟩
  have h := hhard n hn C (by rw [wireCount_eq_wires]; exact hC)
  exact h

/-- `transfer4` in the official form. -/
theorem transfer4_official (inputs : NearCubicGates.Close.NineInputs) (hC : CounterExists4) :
    NearQuarticWires.Statement.FinalStatement4 :=
  mainStatement4_official (transfer4 hC inputs)

end NearQuarticWires.Transfer
