import Proof.Quartic.GateCorollary.Main

set_option autoImplicit false

namespace NearQuarticWires.GateCorollary

open NearCubicGates.Target NearQuarticWires.Statement

/-- `thm:gates`, paper/paper.tex: the exact
integer fourth-power form of the charged top-weight cap. -/
def GateBudget (K n w : ℕ) : Prop :=
  (2 * K * w) ^ 4 * lambda n ^ 17 * mu n ^ 30 ≤ n ^ 12

/-- `thm:gates`, paper/paper.tex: for positive K
and lengths at least four, the real floor cap and its exact integer
test are equivalent, with the factor two retained. -/
theorem le_gateCap_iff_budget {K n w : ℕ} (hK : 0 < K) (hn : 4 ≤ n) :
    w ≤ gateCap K n ↔ GateBudget K n w := by
  have hL : (0 : ℝ) < lambda n := by
    have := lambda_ge_two hn
    exact_mod_cast (show 0 < lambda n by omega)
  have hM : (0 : ℝ) < mu n := by
    have := mu_ge_one hn
    exact_mod_cast (show 0 < mu n by omega)
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  set L : ℝ := (lambda n : ℝ) ^ ((17 : ℝ) / 4) with hLeq
  set M : ℝ := (mu n : ℝ) ^ ((15 : ℝ) / 2) with hMeq
  have hL0 : 0 < L := Real.rpow_pos_of_pos hL _
  have hM0 : 0 < M := Real.rpow_pos_of_pos hM _
  have hL4 : L ^ (4 : ℕ) = (lambda n : ℝ) ^ (17 : ℕ) := by
    rw [hLeq, ← Real.rpow_natCast, ← Real.rpow_mul hL.le]
    norm_num
  have hM4 : M ^ (4 : ℕ) = (mu n : ℝ) ^ (30 : ℕ) := by
    rw [hMeq, ← Real.rpow_natCast, ← Real.rpow_mul hM.le]
    norm_num
  have hden : 0 < 2 * (K : ℝ) * L * M := by positivity
  unfold gateCap
  rw [Nat.le_floor_iff (by positivity), le_div_iff₀ hden]
  have hkey : ((w : ℝ) * (2 * (K : ℝ) * L * M)) ^ (4 : ℕ) =
      (((2 * K * w) ^ 4 * lambda n ^ 17 * mu n ^ 30 : ℕ) : ℝ) := by
    push_cast
    rw [← hL4, ← hM4]
    ring
  have hn3 : ((n : ℝ) ^ 3) ^ (4 : ℕ) = ((n ^ 12 : ℕ) : ℝ) := by
    push_cast
    ring
  unfold GateBudget
  rw [← Nat.cast_le (α := ℝ), ← hkey, ← hn3]
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).symm

/-- `thm:gates`, paper/paper.tex: the iterated
binary logarithm never exceeds the first binary logarithm. -/
theorem mu_le_lambda (n : ℕ) : mu n ≤ lambda n := by
  unfold mu
  exact Nat.clog_le_of_le_pow (Nat.lt_two_pow_self (n := lambda n)).le

/-- `thm:gates`, paper/paper.tex: the earlier
gate theorem's exact integer budget with constant 2K is contained
in the improved charged top-weight budget at every n at least four. -/
theorem mainBudget_implies_gateBudget {K n w : ℕ} (hn : 4 ≤ n)
    (h : MainBudget (2 * K) n w) : GateBudget K n w := by
  have hL : 1 ≤ lambda n := (show 1 ≤ 2 by decide).trans (lambda_ge_two hn)
  have hmu : mu n ^ 2 ≤ lambda n ^ 4 :=
    (Nat.pow_le_pow_left (mu_le_lambda n) 2).trans
      (Nat.pow_le_pow_right hL (by decide : 2 ≤ 4))
  unfold GateBudget
  calc
    (2 * K * w) ^ 4 * lambda n ^ 17 * mu n ^ 30 =
        ((2 * K * w) ^ 4 * mu n ^ 28 * lambda n ^ 17) * mu n ^ 2 := by ring
    _ ≤ ((2 * K * w) ^ 4 * mu n ^ 28 * lambda n ^ 17) * lambda n ^ 4 :=
      Nat.mul_le_mul_left _ hmu
    _ = (2 * K * w * mu n ^ 7) ^ 4 * lambda n ^ 21 := by ring
    _ ≤ n ^ 12 := h

/-- `thm:gates`, paper/paper.tex: the improved
charged top-weight theorem implies the earlier near-cubic gate
statement, preserving its language and gap and doubling only K. -/
theorem mainStatement_of_gateStatement4 : GateStatement4 → MainStatement := by
  rintro ⟨gamma, hgamma, hgamma1, hgate⟩
  refine ⟨gamma, hgamma, hgamma1, ?_⟩
  intro d hd hdgamma
  obtain ⟨K, hK, F, hF, n₀, hn₀, hlength⟩ := hgate d hd hdgamma
  refine ⟨2 * K, by omega, F, hF, n₀, hn₀, ?_⟩
  intro n hn C hC
  apply (hlength n hn).2 C
  apply (le_gateCap_iff_budget hK (hn₀.trans hn)).mpr
  exact mainBudget_implies_gateBudget (hn₀.trans hn) hC

end NearQuarticWires.GateCorollary
