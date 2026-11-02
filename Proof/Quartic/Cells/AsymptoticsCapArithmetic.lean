import Proof.Quartic.Cells.AsymptoticsWindow

set_option autoImplicit false

namespace NearQuarticWires.Cells.ParameterArithmetic

/-- The fixed coefficient in the fourth-power wire-cap comparison
of `thm:counter`, paper/paper.tex. -/
def populationWindowCoefficient (K Ct : ℕ) : ℕ :=
  (64 ^ 4 * 16 * NearCubicGates.Close.Counter.pairGrowthConstant * K ^ 10) *
    (249344 ^ 4 * Ct ^ 4 * (4 * 96 ^ 2 * 16 ^ 3) ^ 2) + 1

/-- The population branch of the quartic cap, `thm:counter`,
paper/paper.tex: the exact fourth-power comparison
`W⁴ lambda¹⁷ mu³⁰ < const · beta⁴ n¹⁶` pays the population window. -/
theorem quartic_population_window
    (n L M P h s T beta W U : ℝ) (K Ct : ℕ)
    (hn : 0 < n) (hL : 0 < L) (hM : 0 < M) (hP : 0 ≤ P)
    (hh : 0 < h) (hs : 0 < s) (hT : 0 ≤ T) (hb : 0 < beta)
    (hW : 0 < W) (hU : 0 ≤ U) (hK : 0 < K) (hCt : 0 < Ct)
    (hprime : n ≤ K * L * M ^ 2 * P)
    (hheight : P ≤ 64 * h)
    (hside : P ^ 6 ≤ NearCubicGates.Close.Counter.pairGrowthConstant * L ^ 3 * (2 * s) ^ 4)
    (htime : T ≤ Ct * L * M)
    (hpop : beta ^ 2 * n ^ 3 * U ^ 2 ≤ 4 * 96 ^ 2 * (16 * M) ^ 3 * W ^ 2)
    (hcap : ((populationWindowCoefficient K Ct : ℕ) * W) ^ 4 * L ^ 17 * M ^ 30 <
      beta ^ 4 * n ^ 16) :
    249344 * T * U < h * s := by
  let F : ℝ := 64 ^ 4 * 16 * NearCubicGates.Close.Counter.pairGrowthConstant * (K : ℝ) ^ 10
  let H : ℝ := 249344 ^ 4 * (Ct : ℝ) ^ 4 * (4 * 96 ^ 2 * 16 ^ 3) ^ 2
  let C : ℝ := (populationWindowCoefficient K Ct : ℕ)
  have hF : 0 < F := by
    dsimp [F, NearCubicGates.Close.Counter.pairGrowthConstant]
    positivity
  have hH : 0 < H := by dsimp [H]; positivity
  have hC : C = F * H + 1 := by
    dsimp [C, F, H, populationWindowCoefficient]
    push_cast
    ring
  have hCone : 1 ≤ C := by rw [hC]; have := mul_pos hF hH; linarith
  have hCpow : C ≤ C ^ 4 := by
    simpa only [pow_one] using pow_le_pow_right₀ hCone (by norm_num : (1 : ℕ) ≤ 4)
  have hcoeff : F * H < C ^ 4 := by rw [hC] at hCpow ⊢; linarith
  have hten : P ^ 10 ≤
      64 ^ 4 * 16 * (NearCubicGates.Close.Counter.pairGrowthConstant : ℝ) * L ^ 3 * (h * s) ^ 4 := by
    calc
      P ^ 10 = P ^ 4 * P ^ 6 := by ring
      _ ≤ (64 * h) ^ 4 *
          (NearCubicGates.Close.Counter.pairGrowthConstant * L ^ 3 * (2 * s) ^ 4) := by
        gcongr
      _ = _ := by ring
  have hnupper : n ^ 10 ≤ F * L ^ 13 * M ^ 20 * (h * s) ^ 4 := by
    calc
      n ^ 10 ≤ ((K : ℝ) * L * M ^ 2 * P) ^ 10 := pow_le_pow_left₀ hn.le hprime 10
      _ = ((K : ℝ) ^ 10 * L ^ 10 * M ^ 20) * P ^ 10 := by ring
      _ ≤ ((K : ℝ) ^ 10 * L ^ 10 * M ^ 20) *
          (64 ^ 4 * 16 * NearCubicGates.Close.Counter.pairGrowthConstant * L ^ 3 * (h * s) ^ 4) :=
        mul_le_mul_of_nonneg_left hten (by positivity)
      _ = _ := by dsimp [F]; ring
  have hpopulation : beta ^ 4 * n ^ 6 * (249344 * T * U) ^ 4 ≤
      H * L ^ 4 * M ^ 10 * W ^ 4 := by
    calc
      _ = 249344 ^ 4 * T ^ 4 * (beta ^ 2 * n ^ 3 * U ^ 2) ^ 2 := by ring
      _ ≤ 249344 ^ 4 * ((Ct : ℝ) * L * M) ^ 4 *
          (4 * 96 ^ 2 * (16 * M) ^ 3 * W ^ 2) ^ 2 := by gcongr
      _ = _ := by dsimp [H]; ring
  let A := F * L ^ 13 * M ^ 20
  let V := beta ^ 4 * n ^ 6
  have hAV : 0 < A * V := by dsimp [A, V]; positivity
  have hscaled : A * (V * (249344 * T * U) ^ 4) < A * (V * (h * s) ^ 4) := by
    calc
      _ ≤ A * (H * L ^ 4 * M ^ 10 * W ^ 4) :=
        mul_le_mul_of_nonneg_left hpopulation (by dsimp [A]; positivity)
      _ = F * H * (W ^ 4 * L ^ 17 * M ^ 30) := by dsimp [A]; ring
      _ < C ^ 4 * (W ^ 4 * L ^ 17 * M ^ 30) :=
        mul_lt_mul_of_pos_right hcoeff (by positivity)
      _ = (C * W) ^ 4 * L ^ 17 * M ^ 30 := by ring
      _ < beta ^ 4 * n ^ 16 := hcap
      _ = V * n ^ 10 := by dsimp [V]; ring
      _ ≤ V * (A * (h * s) ^ 4) := mul_le_mul_of_nonneg_left hnupper (by dsimp [V]; positivity)
      _ = _ := by ring
  have hfour : (249344 * T * U) ^ 4 < (h * s) ^ 4 := by
    apply (mul_lt_mul_iff_right₀ hAV).mp
    simpa only [mul_assoc] using hscaled
  exact (pow_lt_pow_iff_left₀ (by positivity) (by positivity) (by norm_num : (4 : ℕ) ≠ 0)).mp hfour

end NearQuarticWires.Cells.ParameterArithmetic
