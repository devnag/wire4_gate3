import Proof.Quartic.Cells.ParametersSampler

set_option autoImplicit false

namespace NearQuarticWires.Cells.CoreRules

open ParameterArithmetic

variable {x : ParameterInput} {p : Parameters}

/-- `sec:params`, paper/paper.tex: the actual matrix
dimension is at least two. -/
theorem N_ge_two (hs : CoreRules x p) : 2 ≤ p.N := by
  have hs1 : 1 ≤ p.s := by rw [← hs.star_s]; exact hs.starParams.one_le_s
  have hr := hs.r_even_large.2
  have hk : 2 ≤ p.k := by rw [hs.k_eq]; nlinarith
  rw [hs.N_eq]
  calc
    2 = 2 ^ (1 : ℕ) := rfl
    _ ≤ 2 ^ (p.k / 2) := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- `sec:params`, paper/paper.tex: the actual sampler
tolerance is at most one. -/
theorem eta_le_one (hs : CoreRules x p) : p.eta ≤ 1 := by
  rw [hs.eta_eq]
  have hm := hs.MF_pos
  have hden : 0 < (16 * p.MF : ℚ) := by positivity
  apply (div_le_iff₀ hden).mpr
  have hb := hs.input_valid.2.2.2.2.2.1
  have hmr : (1 : ℚ) ≤ p.MF := by exact_mod_cast hm
  nlinarith

/-- `lem:root` and `sec:params`, paper/paper.tex: the actual sample count is at least the actual matrix side. -/
theorem N_le_Q (hs : CoreRules x p) : p.N ≤ p.Q := by
  have hC : p.N ≤ 1024 * p.N * p.m := by rw [hs.m_eq]; omega
  have hX : 0 < 4 * p.N ^ 2 * (2 * (p.omega1 * p.omega2)) := by
    have hN : 0 < p.N := by have := hs.N_ge_two; omega
    obtain ⟨hO1, hO2⟩ := hs.omega_pos
    positivity
  have hA : p.N ^ 4 ≤ (1024 * p.N * p.m) ^ 4 *
      (4 * p.N ^ 2 * (2 * (p.omega1 * p.omega2))) := by
    calc
      p.N ^ 4 ≤ (1024 * p.N * p.m) ^ 4 := Nat.pow_le_pow_left hC _
      _ ≤ _ := Nat.le_mul_of_pos_right _ hX
  have he : p.eta ^ 8 ≤ 1 := pow_le_one₀ hs.eta_pos.le hs.eta_le_one
  have hq4 : (p.N : ℚ) ^ 4 ≤ (p.Q : ℚ) ^ 4 := by
    calc
      (p.N : ℚ) ^ 4 ≤ ((1024 * p.N * p.m : ℕ) : ℚ) ^ 4 *
          (4 * p.N ^ 2 * (2 * (p.omega1 * p.omega2)) : ℕ) := by exact_mod_cast hA
      _ ≤ (p.Q : ℚ) ^ 4 * p.eta ^ 8 := hs.sample_budget
      _ ≤ (p.Q : ℚ) ^ 4 := by
        simpa using mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ (p.Q : ℚ) ^ 4)
  have hNQ := (pow_le_pow_iff_left₀ (by positivity : 0 ≤ (p.N : ℚ))
    (by positivity : 0 ≤ (p.Q : ℚ)) (by norm_num : (4 : ℕ) ≠ 0)).mp hq4
  exact_mod_cast hNQ

end NearQuarticWires.Cells.CoreRules

namespace NearQuarticWires.Cells.ParameterRules

open ParameterArithmetic

variable {x : ParameterInput} {p : Parameters}

/-- `sec:params`, paper/paper.tex: every selected modulus
is prime and exceeds the entire signed digit window. -/
theorem selected_prime_guards (hs : ParameterRules x p) (q : ℕ) (hq : q ∈ p.primes) :
    q.Prime ∧ 2 * p.hE - 1 ≤ q := by
  rw [hs.primes_eq, NearCubicGates.Close.Counter.mem_dyadicPrimes] at hq
  have he : 4 * p.hE ≤ p.P := by
    rw [hs.hE_eq]
    exact Nat.mul_div_le p.P 4
  exact ⟨hq.2.1, by omega⟩

/-- `sec:params`, paper/paper.tex: the lifted modulus
has positive exponent. -/
theorem e_pos (hs : ParameterRules x p) : 1 ≤ p.e := hs.lift_spec.1.1

/-- `eq:prime-budget`, paper/paper.tex: the selected
prime scale pays the literal residue polynomial degree. -/
theorem prime_budget (hs : ParameterRules x p) :
    (2 * p.e - 1) * (2 * p.Jmax + 2) * (p.P - 1) + 4 * p.m * p.Xmax ≤ p.Dmax := by
  have h := hs.prime_candidate.2.2
  rw [hs.e_eq] at h
  exact h

/-- `imp:chain` and `sec:params`, paper/paper.tex:
the first rational rate ratio is positive at every successful selection. -/
theorem firstRatio_pos (hs : ParameterRules x p) :
    0 < NearCubicGates.Close.Counter.firstRatio p.ell0 p.h p.T := by
  by_contra hneg
  have hstop := (NearCubicGates.Close.Counter.leastUpTo_spec _ _ _ hs.chain_eq).1
  have hnon := NearCubicGates.Close.Counter.ratio_nonpos _ (not_lt.mp hneg) (p.J - 1)
  have : (1 : ℚ) / 256 ≤ 0 := hstop.trans hnon
  norm_num at this

/-- `imp:chain` and `sec:params`, paper/paper.tex:
all active rate multipliers are positive, so their exact product is positive. -/
theorem A_pos (hs : ParameterRules x p) : 0 < p.A := by
  rw [hs.A_eq, hs.factors_eq]
  unfold NearCubicGates.Close.Counter.chainFactors
  apply List.prod_pos
  intro a ha
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
  have hi' : i < p.J - 1 := List.mem_range.mp hi
  have hp := NearCubicGates.Close.Counter.ratio_pos _ hs.firstRatio_pos i
  have hmin := (NearCubicGates.Close.Counter.leastUpTo_spec _ _ _ hs.chain_eq).2.2 i hi'
  have hfour := NearCubicGates.Close.Counter.factorRat_ge_four _ hp (not_le.mp hmin)
  omega

/-- `imp:window` and `sec:params`, paper/paper.tex:
the single-score and pair-score windows are positive, and the single-score
window is at least the pair-score window. -/
theorem window_bounds (hs : ParameterRules x p) :
    1 ≤ p.L2 ∧ p.L2 ≤ p.Dprime ∧ p.L2 ≤ p.Lw := by
  have hd : 1 ≤ p.Dprime := by
    rw [hs.Dprime_eq]
    exact NearCubicGates.Close.Counter.window_pos _
  have hl : 1 ≤ p.L2 := by
    rw [hs.L2_eq]
    exact NearCubicGates.Close.Counter.pairSide_pos _
  have hld : p.L2 ≤ p.Dprime := by
    rw [hs.L2_eq]
    rcases NearCubicGates.Close.Counter.pairSide_le_window p.Dprime with h | h
    · exact h
    · omega
  refine ⟨hl, hld, ?_⟩
  rw [hs.Lw_eq]
  unfold NearCubicGates.Close.Counter.windowInUse
  split_ifs
  · exact le_rfl
  · exact hld

/-- `sec:params`, paper/paper.tex: the actual matrix
dimension is at least two. -/
theorem N_ge_two (hs : ParameterRules x p) : 2 ≤ p.N :=
  CoreRules.N_ge_two (hs : CoreRules x p)

/-- `sec:params`, paper/paper.tex: the actual sampler
tolerance is at most one. -/
theorem eta_le_one (hs : ParameterRules x p) : p.eta ≤ 1 :=
  CoreRules.eta_le_one (hs : CoreRules x p)

/-- `lem:root` and `sec:params`, paper/paper.tex: the actual sample count is at least the actual matrix side. -/
theorem N_le_Q (hs : ParameterRules x p) : p.N ≤ p.Q :=
  CoreRules.N_le_Q (hs : CoreRules x p)

end NearQuarticWires.Cells.ParameterRules

