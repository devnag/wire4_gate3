import Proof.Quartic.Sampler.Basic

set_option autoImplicit false

namespace NearQuarticWires.Sampler

open Finset Matrix
open NearCubicWires.WireExponent3_5.Shared

/-- `lem:tracebound`, paper/paper.tex, direct-moment version:
the concrete eighth walk moment needs only signed entry bounds. No Tropp input. -/
theorem signed_walkMoment_bound {N Q : ℕ} (hN : 1 ≤ N) (hNQ : N ≤ Q)
    (D : Cell N → ℝ) (hD : ∀ c, |D c| ≤ 1) :
    |∑ S : Fin Q → Cell N, walkMoment (L := 8) (by norm_num) D S| ≤
      (2 : ℝ) ^ 8 * 5 * 8 ^ 8 * (Q : ℝ) ^ 4 * (N : ℝ) ^ (2 * Q + 13) := by
  have h := sum_walkMoment_le_explicit (L := 8) (by norm_num) hN hNQ D hD
  norm_num at h ⊢
  exact h

/-- `lem:tracebound`, paper/paper.tex: the paper's dilation
trace at m=4 is twice the concrete half trace. -/
noncomputable def traceMoment {N Q : ℕ} (D : Cell N → ℝ)
    (S : Fin Q → Cell N) : ℝ :=
  2 * Matrix.trace ((errorMatrix D S * (errorMatrix D S)ᵀ) ^ 4)

/-- `lem:tracebound`, paper/paper.tex: nonnegativity for signed D. -/
theorem traceMoment_nonneg {N Q : ℕ} (D : Cell N → ℝ) (S : Fin Q → Cell N) :
    0 ≤ traceMoment D S := by
  exact mul_nonneg (by norm_num)
    (NearCubicWires.WireExponent3_5.Sampler.trace_pow4_nonneg _)

/-- `lem:tracebound`, paper/paper.tex: exact independent-uniform
mean bound for the concrete E_D, proved by finite walks with |D|≤1. -/
theorem mean_traceMoment_le {N Q : ℕ} (hN : 1 ≤ N) (hNQ : N ≤ Q)
    (D : Cell N → ℝ) (hD : ∀ c, |D c| ≤ 1) :
    uMean (fun S : Fin Q → Cell N => traceMoment D S) ≤
      2 * NearCubicWires.WireExponent3_5.Sampler.C8 * (Q : ℝ) ^ 4 * (N : ℝ) ^ 13 := by
  have h := NearCubicWires.WireExponent3_5.Sampler.uMean_potential_le
    (Z := Unit) (T := Unit) hN hNQ (fun _ _ => D) (fun _ _ => hD)
  simp only [Fintype.card_unit, Nat.cast_one, one_mul,
    NearCubicWires.WireExponent3_5.Sampler.potential, Fintype.sum_unique] at h
  have h2 := mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 2)
  simpa only [traceMoment, uMean, ← Finset.mul_sum, mul_div_assoc,
    mul_assoc] using h2

end NearQuarticWires.Sampler
