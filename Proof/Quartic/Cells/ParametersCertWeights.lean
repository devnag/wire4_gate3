import Proof.Quartic.Cells.ParametersCertFormulaMass

set_option autoImplicit false

namespace NearQuarticWires.Cells.ParameterArithmetic

open NearCubicGates.Close.Interfaces

/-- `sec:walks` and the witness specification, paper/paper.tex: every literal proposed coefficient is
a Boolean integer, including indices beyond the stored chain. -/
theorem actual_chain_bit_natAbs_le (c : Call) (p : Parameters) (w : List Bool)
    (j : Fin 2) (i : ℕ) (t : Fin (Builder.occurrences c j)) :
    (Builder.chainBit c (p := p) w j i t).natAbs ≤ 1 := by
  unfold Builder.chainBit Algorithm.CellCall.bitInt
  split_ifs <;> norm_num

/-- `lem:print`, paper/paper.tex: embedding one
circuit's occurrence weights in the concatenated physical bank
preserves their absolute bound, including all unselected labels. -/
theorem circuit_weights_natAbs_le (c : Call) (j : Fin 2)
    (f : Fin (Builder.occurrences c j) → ℤ) (B : ℕ)
    (hf : ∀ t, (f t).natAbs ≤ B) :
    ∀ g, (StagePrint.circuitWeights c j f g).natAbs ≤ B := by
  intro g
  unfold StagePrint.circuitWeights
  split_ifs <;> first | exact hf _ | simp

/-- `sec:walks` and `lem:print`, paper/paper.tex: an actual digit weight has absolute value at most
one plus the selected arity, before any certification test. -/
theorem call_digit_weights_natAbs_le (c : Call) {p : Parameters}
    (hs : ParameterRules (Builder.callInput c) p) (w : List Bool)
    (j : Fin 2) (r : Fin (p.J - 1 + 1)) (t : Fin (Builder.occurrences c j)) :
    (StagePrint.callDigitWeights c hs w j r t).natAbs ≤ 1 + c.n := by
  cases hr : r.val with
  | zero =>
    simpa only [StagePrint.callDigitWeights, hr, NearCubicGates.CountingCore.proposedDigit] using
      (actual_chain_bit_natAbs_le c p w j 0 t).trans (Nat.le_add_right 1 c.n)
  | succ i =>
    have hrate : (Builder.algorithmParameters c hs).rate i ≤ c.n := hs.chain_factor_le_n i
    have h0 := actual_chain_bit_natAbs_le c p w j i t
    have h1 := actual_chain_bit_natAbs_le c p w j (i + 1) t
    simp only [StagePrint.callDigitWeights, hr, NearCubicGates.CountingCore.proposedDigit]
    calc
      _ ≤ (Builder.chainBit c (p := p) w j (i + 1) t).natAbs +
          (((Builder.algorithmParameters c hs).rate i : ℤ) *
            Builder.chainBit c (p := p) w j i t).natAbs := Int.natAbs_sub_le _ _
      _ = (Builder.chainBit c (p := p) w j (i + 1) t).natAbs +
          (Builder.algorithmParameters c hs).rate i *
            (Builder.chainBit c (p := p) w j i t).natAbs := by simp [Int.natAbs_mul]
      _ ≤ _ := Nat.add_le_add h1 (by simpa only [mul_one] using Nat.mul_le_mul hrate h0)

/-- `sec:walks` and `lem:print`, paper/paper.tex: the actual final-error weights fit the selected
population scale, independently of the proposed witness. -/
theorem call_final_weights_natAbs_le (c : Call) (p : Parameters) (w : List Bool)
    (j : Fin 2) (t : Fin (Builder.occurrences c j)) :
    (StagePrint.callFinalWeights c p w j t).natAbs ≤ p.M1 + p.A := by
  unfold StagePrint.callFinalWeights
  calc
    _ ≤ ((p.M1 : ℤ) * Builder.chainBit c (p := p) w j (p.J - 1) t).natAbs +
        (p.A : ℤ).natAbs := Int.natAbs_sub_le _ _
    _ = p.M1 * (Builder.chainBit c (p := p) w j (p.J - 1) t).natAbs + p.A := by
      simp [Int.natAbs_mul]
    _ ≤ _ := by
      have h := Nat.mul_le_mul_left p.M1 (actual_chain_bit_natAbs_le c p w j (p.J - 1) t)
      omega

end NearQuarticWires.Cells.ParameterArithmetic
