import Proof.Quartic.Cycle.Basic
import Proof.Wire_3_5.SamplerFix

set_option autoImplicit false

namespace NearQuarticWires.Cycle
open Finset

abbrev SeedParameters := NearCubicWires.WireExponent3_5.Sampler.SeedParams

/-- Paper `cor:conditional`: the concrete eight-wise generator seed length. -/
def seedLength (P : SeedParameters) : ℕ := 8 * P.ell

/-- Paper `cor:conditional`: the actual generated sample list of an integer seed. -/
noncomputable def seedSample (P : SeedParameters) (s : ℕ) :
    Fin P.Q → NearQuarticWires.Sampler.Cell P.N :=
  P.pos (NearCubicWires.WireExponent3_5.Sampler.decodeNat P s)

/-- Paper `cor:conditional`: signed integer Γ_w summed over the actual prefix completions. -/
noncomputable def gammaCompletionSum (P : SeedParameters) (plen pre : ℕ)
    (w : Walk P.N 4) : ℤ :=
  ∑ r ∈ Finset.range (2 ^ (seedLength P - plen)),
    walkGammaInt (by norm_num) (seedSample P
      (NearCubicWires.WireExponent3_5.Sampler.completion plen pre r)) w

/-- Paper `cor:conditional`: c_π(w), independent of the column, as an exact rational. -/
noncomputable def conditionalGamma (P : SeedParameters) (plen pre : ℕ)
    (w : Walk P.N 4) : ℚ :=
  (gammaCompletionSum P plen pre w : ℚ) / (2 : ℚ) ^ (seedLength P - plen)

/-- Paper `cor:conditional`: the concrete signed integer 2^S c_π(w). -/
noncomputable def scaledGamma (P : SeedParameters) (plen pre : ℕ)
    (w : Walk P.N 4) : ℤ :=
  (2 : ℤ) ^ plen * gammaCompletionSum P plen pre w

/-- Paper `cor:conditional`: exact dyadic integrality, including negative walk weights. -/
theorem scaledGamma_spec (P : SeedParameters) (plen pre : ℕ)
    (hplen : plen ≤ seedLength P) (w : Walk P.N 4) :
    (2 : ℚ) ^ seedLength P * conditionalGamma P plen pre w =
      (scaledGamma P plen pre w : ℚ) := by
  have hp : (2 : ℚ) ^ seedLength P =
      (2 : ℚ) ^ plen * (2 : ℚ) ^ (seedLength P - plen) := by
    rw [← pow_add, Nat.add_sub_of_le hplen]
  simp only [conditionalGamma, scaledGamma, Int.cast_mul, Int.cast_pow, Int.cast_ofNat]
  rw [hp]
  field_simp

/-- Paper `cor:conditional`: the concrete signed sample factor Γ is uniformly bounded. -/
theorem abs_gamma_le {N Q : ℕ} (hN : 1 ≤ N)
    (S : Fin Q → NearQuarticWires.Sampler.Cell N) (c : NearQuarticWires.Sampler.Cell N) :
    |NearQuarticWires.Sampler.gamma S c| ≤ (Q : ℝ) * (N : ℝ) ^ 2 := by
  unfold NearQuarticWires.Sampler.gamma
  calc
    |∑ j, NearCubicWires.WireExponent3_5.Shared.yc N (S j) c| ≤
        ∑ j, |NearCubicWires.WireExponent3_5.Shared.yc N (S j) c| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin Q, (N : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro j _
      exact NearCubicWires.WireExponent3_5.Sampler.abs_yc_le hN _ _
    _ = _ := by simp

/-- Paper `cor:conditional`: |Γ_w|≤(N²Q)^8 on every actual sample list. -/
theorem abs_walkGamma_le {N Q : ℕ} (hN : 1 ≤ N)
    (S : Fin Q → NearQuarticWires.Sampler.Cell N) (w : Walk N 4) :
    |walkGamma (by norm_num) S w| ≤ ((Q : ℝ) * (N : ℝ) ^ 2) ^ 8 := by
  unfold walkGamma
  rw [Finset.abs_prod]
  calc
    (∏ l, |NearQuarticWires.Sampler.gamma S (edge (by norm_num) w l)|) ≤
        ∏ _l : Fin 8, ((Q : ℝ) * (N : ℝ) ^ 2) := by
      exact Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun _ _ => abs_gamma_le hN S _)
    _ = _ := by simp

/-- Paper `cor:conditional`: the same bound for the concrete integer walk product. -/
theorem abs_walkGammaInt_le {N Q : ℕ} (hN : 1 ≤ N)
    (S : Fin Q → NearQuarticWires.Sampler.Cell N) (w : Walk N 4) :
    |walkGammaInt (by norm_num) S w| ≤ ((Q : ℤ) * (N : ℤ) ^ 2) ^ 8 := by
  have h := abs_walkGamma_le hN S w
  rw [← walkGammaInt_cast] at h
  exact_mod_cast h

/-- Paper `cor:conditional`: |c_π(w)|≤(N²Q)^8 for the actual generator. -/
theorem abs_conditionalGamma_le (P : SeedParameters) (plen pre : ℕ)
    (w : Walk P.N 4) :
    |conditionalGamma P plen pre w| ≤ ((P.Q : ℚ) * (P.N : ℚ) ^ 2) ^ 8 := by
  have hN : 1 ≤ P.N := Nat.one_le_two_pow
  have hs : |gammaCompletionSum P plen pre w| ≤
      (2 : ℤ) ^ (seedLength P - plen) * ((P.Q : ℤ) * (P.N : ℤ) ^ 2) ^ 8 := by
    unfold gammaCompletionSum
    calc
      |∑ r ∈ Finset.range (2 ^ (seedLength P - plen)),
          walkGammaInt (by norm_num) (seedSample P
            (NearCubicWires.WireExponent3_5.Sampler.completion plen pre r)) w| ≤
          ∑ r ∈ Finset.range (2 ^ (seedLength P - plen)),
            |walkGammaInt (by norm_num) (seedSample P
              (NearCubicWires.WireExponent3_5.Sampler.completion plen pre r)) w| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _r ∈ Finset.range (2 ^ (seedLength P - plen)),
          ((P.Q : ℤ) * (P.N : ℤ) ^ 2) ^ 8 :=
        Finset.sum_le_sum (fun _ _ => abs_walkGammaInt_le hN _ w)
      _ = _ := by simp
  have hsq : |(gammaCompletionSum P plen pre w : ℚ)| ≤
      (2 : ℚ) ^ (seedLength P - plen) * ((P.Q : ℚ) * (P.N : ℚ) ^ 2) ^ 8 := by
    exact_mod_cast hs
  unfold conditionalGamma
  rw [abs_div, abs_of_pos (by positivity : (0 : ℚ) < 2 ^ (seedLength P - plen))]
  apply (div_le_iff₀ (by positivity : (0 : ℚ) < 2 ^ (seedLength P - plen))).2
  simpa only [mul_comm] using hsq

end NearQuarticWires.Cycle
