import Proof.Quartic.Program.StepFive
import Proof.Quartic.Program.Output
import Proof.Quartic.Cells.ParametersScalarBounds

set_option autoImplicit false

namespace NearQuarticWires.Cells

open NearCubicGates.Close.Interfaces

/-- The two literal totals of Step 4, `sec:algorithm`, paper/paper.tex,
are nonnegative, the accepting total is at most the mask total, and
the latter is at most the number of certified samples. -/
theorem sample_totals_bounds (C : Algorithm.CellCall) :
    0 ≤ Program.acceptTotal C ∧ Program.acceptTotal C ≤ Program.maskTotal C ∧
      Program.maskTotal C ≤ (C.certifiedColumns.card : ℤ) * C.seed.Q := by
  classical
  have hm (z : Fin C.ncol) (j : Fin C.seed.Q) :=
    Program.CellBounds.pointMask_mem C z (C.samples j)
  have hp (z : Fin C.ncol) (j : Fin C.seed.Q) :=
    Program.CellBounds.bitInt_mem (C.pred z (C.samples j))
  refine ⟨?_, ?_, ?_⟩
  · exact Finset.sum_nonneg fun z _ => Finset.sum_nonneg fun j _ => mul_nonneg (hp z j).1 (hm z j).1
  · apply Finset.sum_le_sum
    intro z _
    apply Finset.sum_le_sum
    intro j _
    exact mul_le_of_le_one_left (hm z j).1 (hp z j).2
  · calc
      Program.maskTotal C ≤ ∑ _z ∈ C.certifiedColumns, ∑ _j : Fin C.seed.Q, (1 : ℤ) :=
        Finset.sum_le_sum fun z _ => Finset.sum_le_sum fun j _ => (hm z j).2
      _ = (C.certifiedColumns.card : ℤ) * C.seed.Q := by simp

/-- The exact arithmetic inputs of Step 5 on a selected call,
`sec:algorithm`, paper/paper.tex, satisfy their natural range bounds. -/
theorem selected_output_bounds (c : Call) (p : Program.Selected c) (w : List Bool) :
    0 < p.1.Q ∧ p.1.k ≤ c.n ∧ 0 ≤ p.1.eta ∧
      (Program.runCall c p w).certifiedColumns.card ≤ 2 ^ (c.n - p.1.k) ∧
      0 ≤ Program.acceptTotal (Program.runCall c p w) ∧
      Program.acceptTotal (Program.runCall c p w) ≤ Program.maskTotal (Program.runCall c p w) ∧
      Program.maskTotal (Program.runCall c p w) ≤
        ((Program.runCall c p w).certifiedColumns.card : ℤ) * p.1.Q := by
  classical
  have hs := prepare_spec _ p.1 p.2
  have ht := sample_totals_bounds (Program.runCall c p w)
  refine ⟨?_, hs.k_lt_n.le, hs.eta_pos.le, ?_, ht.1, ht.2.1, ht.2.2⟩
  · rw [hs.Q_eq]
    positivity
  · calc
      (Program.runCall c p w).certifiedColumns.card ≤ (Program.runCall c p w).ncol := by
        simpa only [Fintype.card_fin] using
          (Finset.card_le_univ (Program.runCall c p w).certifiedColumns)
      _ = 2 ^ (c.n - p.1.k) := rfl

/-- Nonnegative sampled totals imply nonnegative upper endpoint,
ordered endpoints, and nonnegative center before outward rounding in
Step 5, `sec:algorithm`, paper/paper.tex. -/
theorem stepFive_endpoint_bounds (n : ℕ) (p : Parameters) (A M : ℤ) (nc : ℕ)
    (hQ : 0 < p.Q) (hη : 0 ≤ p.eta) (hA : 0 ≤ A) (_hAM : A ≤ M)
    (hM : M ≤ (nc : ℤ) * p.Q) (hnc : nc ≤ 2 ^ (n - p.k)) :
    0 ≤ Program.stepFiveUpper n p A M nc ∧
      Program.stepFiveLower n p A nc ≤ Program.stepFiveUpper n p A M nc ∧
      0 ≤ Program.stepFiveLower n p A nc + Program.stepFiveUpper n p A M nc := by
  have hq : (0 : ℚ) < p.Q := by exact_mod_cast hQ
  have hm : (M : ℚ) / p.Q ≤ nc := (div_le_iff₀ hq).mpr (by exact_mod_cast hM)
  have ha : (0 : ℚ) ≤ (A : ℚ) / p.Q := div_nonneg (by exact_mod_cast hA) hq.le
  have hc : (0 : ℚ) ≤ ((2 ^ (n - p.k) : ℕ) : ℚ) - nc :=
    sub_nonneg.mpr (by exact_mod_cast hnc)
  have he : (0 : ℚ) ≤ (nc : ℚ) * p.eta := mul_nonneg (by positivity) hη
  have hf : (0 : ℚ) ≤ (p.MF : ℚ) * ((nc : ℚ) * p.eta) := mul_nonneg (by positivity) he
  have hd : (0 : ℚ) < (2 ^ (n - p.k) : ℕ) := by positivity
  unfold Program.stepFiveLower Program.stepFiveUpper
  refine ⟨div_nonneg ?_ hd.le, (div_le_div_iff_of_pos_right hd).mpr ?_, ?_⟩
  · nlinarith
  · nlinarith
  · rw [← add_div]
    exact div_nonneg (by nlinarith) hd.le

end NearQuarticWires.Cells
