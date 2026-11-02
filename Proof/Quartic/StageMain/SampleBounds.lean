import Proof.Quartic.StageMain.SampleRecipe
import Proof.Quartic.StageGamma.WriterBudget

/-!
# Finite width and time of the sampler record writer

`imp:seed`, paper/paper.tex, uses eight field coefficients.
For the main pass, all writer loops depend only on the
field degree. Field elements are binary payloads, not numerical loop bounds.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain.SampleCells

open NearCubicGates.Close.Cells
open NearCubicWires.WireExponent3_5
open StageGamma

theorem sampleRecipe_counts : ∀ x : Fin VV, x ∈ sampleRecipe.counts → x = ell := by decide

theorem sampleRecipe_params : ∀ x : Fin VV, x ∈ sampleRecipe.params →
    x ∈ [ell, modulus, label, vZ] ++ coefficientRegisters := by decide

theorem sampleRecipe_factor : sampleRecipe.clockFactor ≤ 10000 := by decide

theorem sampleRecipe_cost (r : SampleRequest) (a : DS VV MM) (h : SampleStored r a) :
    sampleRecipe.cost a ≤ 10000 * (r.ell + 1) := by
  have hc := Writer.cost_le sampleRecipe a r.ell (fun x hx => by
    rw [sampleRecipe_counts x hx, h.degree])
  exact hc.trans (Nat.mul_le_mul_right _ sampleRecipe_factor)

theorem sampleRecipe_params_fit (r : SampleRequest) (a : DS VV MM)
    (hc : Cst a) (h : SampleStored r a) (W : ℕ) (hW : r.ell + 2 ≤ W) :
    ∀ x ∈ sampleRecipe.params, a.env x < 2 ^ W := by
  intro x hx
  have hm := sampleRecipe_params x hx
  rcases List.mem_append.mp hm with hm | hm
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl
    · rw [h.degree]
      exact (show r.ell < W by omega).trans Nat.lt_two_pow_self
    · rw [h.field]
      exact r.modulus_ok.2.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
    · rw [h.sampleLabel]
      exact r.label_lt.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
    · rw [hc.z]
      positivity
  · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hm
    rw [h.coeff]
    exact (Sampler.seedCoeff_lt _ _ _).trans_le (Nat.pow_le_pow_right (by decide) (by omega))

end NearQuarticWires.StageMain.SampleCells
