import Proof.Quartic.StageOutput.Semantics

/-!
# Arithmetic invariants of the scalar requests

Paper: `sec:algorithm`, paper/paper.tex. The selected
requests have a positive common denominator, `k ≤ n`, and nonnegative
upper, center and radius numerators. These are numerical consequences of
the sampled-total bounds, including the inconsistent-path branch.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageOutput

open NearCubicGates.Close.Interfaces

structure Input.Admissible (d : Input) : Prop where
  denominator_pos : 0 < d.denominator
  k_le_n : d.k ≤ d.n
  ceil_nonneg : 0 ≤ d.ceilValue
  center_nonneg : 0 ≤ d.floorValue + d.ceilValue
  radius_nonneg : 0 ≤ d.ceilValue - d.floorValue

def OutputRequest.Admissible : OutputRequest → Prop
  | .inl _ => True
  | .inr d => d.Admissible

def OutputRequest.result : OutputRequest → ℚ × ℚ
  | .inl q => q
  | .inr d => d.result

theorem selectedInput_admissible (c : Call) (p : Program.Selected c) (w : List Bool) :
    (selectedInput c p w).Admissible := by
  have hb := Cells.selected_output_bounds c p w
  have hr := selectedInput_nonneg c p w
  exact ⟨Cells.outputDenominator_pos p.1 hb.1, hb.2.1, hr.1, hr.2.1, hr.2.2⟩

theorem outputRequest_admissible (B1 B2 : ℕ) (c : Call) (w : List Bool) :
    (outputRequest B1 B2 c w).Admissible := by
  unfold outputRequest
  split
  · trivial
  · exact selectedInput_admissible c _ w

theorem outputRequest_result (B1 B2 : ℕ) (c : Call) (w : List Bool) :
    (outputRequest B1 B2 c w).result = Program.admittedValue B1 B2 Builder.value c w := by
  unfold outputRequest
  split
  · rfl
  · rename_i p hd
    exact selectedInput_result hd w

end NearQuarticWires.StageOutput
