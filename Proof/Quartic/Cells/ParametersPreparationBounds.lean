import Proof.Quartic.Cells.AsymptoticsResources
import Proof.Quartic.Builder.Chain

set_option autoImplicit false

namespace NearQuarticWires.Cells.CoreRules

variable {x : ParameterInput} {p : Parameters}

/-- `sec:params` and `prop:time`, paper/paper.tex: the exact public binary logarithm is at most the arity. -/
theorem lambda_le_n (hs : CoreRules x p) : p.lambda ≤ x.n := by
  rw [hs.lambda_eq]
  exact NearCubicGates.Close.Counter.clog_le_self _

/-- The polynomial scale used for serializing parameters in
`prop:time`, paper/paper.tex, before any late guard. -/
theorem tau_preparation_bound (hs : CoreRules x p) (B1 : ℕ)
    (hb : 1 ≤ x.beta * (x.n : ℚ) ^ B1) : p.tau ≤ (B1 + 20) * x.n ^ 2 := by
  have hL := hs.lambda_le_n
  have hM := hs.mu_le_lambda.trans hL
  calc
    p.tau ≤ (B1 + 20) * p.mu * p.lambda := hs.tau_upper B1 hb
    _ ≤ (B1 + 20) * x.n * x.n := by gcongr
    _ = _ := by ring

/-- `sec:params` and `prop:time`, paper/paper.tex: the exact population ceiling has a uniform polynomial
value bound at every admitted precision, including its integer ceiling. -/
theorem U_preparation_bound (hs : CoreRules x p) (B1 : ℕ)
    (hb : 1 ≤ x.beta * (x.n : ℚ) ^ B1) :
    p.U ≤ (B1 + 20000) * x.n ^ (B1 + 4) := by
  let t := (B1 + 20000) * x.n ^ (B1 + 4)
  have hn := hs.n_pos
  have hL := hs.lambda_le_n
  have hM := hs.mu_le_lambda.trans hL
  have hr : p.r ≤ 16 * x.n := by rw [hs.r_eq]; exact Nat.mul_le_mul_left _ hM
  have hW := hs.input_valid.2.2.2.1
  have hτ : p.tau ≤ t := by
    calc
      p.tau ≤ (B1 + 20) * x.n ^ 2 := hs.tau_preparation_bound B1 hb
      _ ≤ (B1 + 20000) * x.n ^ (B1 + 4) :=
        Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right hn (by omega))
  apply (hs.U_le_iff t).mpr
  refine ⟨hτ, ?_⟩
  have hden : 0 < x.beta ^ 2 * (x.n : ℚ) ^ 3 := by
    have := hs.beta_pos
    have hnr : (0 : ℚ) < x.n := by exact_mod_cast hn
    positivity
  apply (div_le_iff₀ hden).mpr
  have hrQ : (p.r : ℚ) ≤ 16 * x.n := by exact_mod_cast hr
  have hWQ : (x.W : ℚ) ≤ 2 * (x.n : ℚ) ^ 4 := by exact_mod_cast hW
  have hb2 : (1 : ℚ) ≤ (x.beta * (x.n : ℚ) ^ B1) ^ 2 := by
    simpa only [one_pow] using pow_le_pow_left₀ (by norm_num : (0 : ℚ) ≤ 1) hb 2
  have hC : (12288 : ℚ) ≤ ((B1 + 20000 : ℕ) : ℚ) := by exact_mod_cast (by omega : 12288 ≤ B1 + 20000)
  calc
    96 ^ 2 * (p.r : ℚ) ^ 3 * (x.W : ℚ) ^ 2 ≤
        96 ^ 2 * (16 * (x.n : ℚ)) ^ 3 * (2 * (x.n : ℚ) ^ 4) ^ 2 := by gcongr
    _ = 12288 ^ 2 * (x.n : ℚ) ^ 11 := by ring
    _ ≤ (((B1 + 20000 : ℕ) : ℚ)) ^ 2 * (x.n : ℚ) ^ 11 :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hC 2) (by positivity)
    _ ≤ (((B1 + 20000 : ℕ) : ℚ)) ^ 2 * (x.n : ℚ) ^ 11 *
        (x.beta * (x.n : ℚ) ^ B1) ^ 2 := le_mul_of_one_le_right (by positivity) hb2
    _ = (t : ℚ) ^ 2 * (x.beta ^ 2 * (x.n : ℚ) ^ 3) := by
      dsimp [t]
      push_cast
      rw [pow_add]
      ring

end NearQuarticWires.Cells.CoreRules

namespace NearQuarticWires.Cells.ParameterRules

variable {x : ParameterInput} {p : Parameters}

/-- The initial denominator in `sec:params`, paper/paper.tex, is polynomially bounded in the population scale and arity. -/
theorem M1_preparation_bound (hs : ParameterRules x p) : p.M1 ≤ 512 * p.U + 4 * x.n ^ 2 := by
  have hT := hs.T_pos
  have hhpos : 0 < p.h := by have := hs.height; omega
  have hhn : p.h ≤ x.n := by
    have := hs.prime_candidate.2.1
    rw [hs.h_eq, hs.hE_eq, hs.m_eq]
    omega
  have hhQ : (0 : ℚ) < p.h := by exact_mod_cast hhpos
  have hh1 : (1 : ℚ) ≤ p.h := by exact_mod_cast (show 1 ≤ p.h from hhpos)
  have hT1 : (1 : ℚ) ≤ p.T := by exact_mod_cast (show 1 ≤ p.T from hT)
  have hhnQ : (p.h : ℚ) ≤ x.n := by exact_mod_cast hhn
  have hbar : NearCubicGates.Close.Counter.ellBar p.ell0 p.h p.T ≤ 128 * p.U + (x.n : ℚ) ^ 2 := by
    unfold NearCubicGates.Close.Counter.ellBar
    apply max_le
    · rw [hs.ell0_eq, hs.m_eq]
      push_cast
      exact le_add_of_nonneg_right (by positivity)
    · apply (div_le_iff₀ (by positivity : (0 : ℚ) < 256 * p.T)).mpr
      calc
        (p.h : ℚ) ^ 2 ≤ (x.n : ℚ) ^ 2 := pow_le_pow_left₀ (by positivity) hhnQ _
        _ ≤ 128 * p.U + (x.n : ℚ) ^ 2 := le_add_of_nonneg_left (by positivity)
        _ ≤ (128 * p.U + (x.n : ℚ) ^ 2) * (256 * p.T) :=
          le_mul_of_one_le_right (by positivity) (by linarith only [hT1])
  rw [hs.M1_eq]
  unfold NearCubicGates.Close.Counter.firstDen
  apply Nat.ceil_le.mpr
  apply (div_le_iff₀ hhQ).mpr
  have hscale : (512 * (p.U : ℚ) + 4 * (x.n : ℚ) ^ 2) ≤
      (512 * (p.U : ℚ) + 4 * (x.n : ℚ) ^ 2) * p.h := le_mul_of_one_le_right (by positivity) hh1
  push_cast
  nlinarith only [hbar, hscale]

/-- The exact finite chain product in `sec:params`, paper/paper.tex, fits the initial denominator at every selected stage. -/
theorem A_le_M1 (hs : ParameterRules x p) : p.A ≤ p.M1 := by
  rw [Builder.A_eq_product hs, Builder.M1_eq_denominator hs]
  apply NearCubicGates.PublicSamplingRates.product_fits_denominator
  · exact_mod_cast hs.T_pos
  · exact_mod_cast hs.height

/-- Every exact rational-chain factor search in `sec:params`,
paper/paper.tex, uses at most the public arity as
its finite search bound, at every stage of the stabilized chain. -/
theorem chain_factor_search_bound (hs : ParameterRules x p) (i : ℕ) :
    ⌈1 / NearCubicGates.RationalRateChain.ratio
      (NearCubicGates.Close.Counter.firstRatio p.ell0 p.h p.T) i⌉₊ ≤ x.n := by
  have hT : (0 : ℝ) < p.T := by exact_mod_cast hs.T_pos
  have hheight : (64 : ℝ) * p.T ≤ p.h := by exact_mod_cast hs.height
  have hinit := NearCubicGates.PublicSamplingRates.initial_bounds
    (p.T : ℝ) p.h p.ell0 hT hheight
  have hmono := NearCubicGates.NestedRateChain.ratio_mono _ hinit.2.2.1 (Nat.zero_le i)
  change NearCubicGates.PublicSamplingRates.initialRatio (p.T : ℝ) p.h p.ell0 ≤
    NearCubicGates.NestedRateChain.rateRatio
      (NearCubicGates.PublicSamplingRates.initialRatio (p.T : ℝ) p.h p.ell0) i at hmono
  have hhpos : (0 : ℝ) < p.h := by have := hs.height; have := hs.T_pos; exact_mod_cast (by omega : 0 < p.h)
  have hhn : p.h ≤ x.n := by
    have := hs.prime_candidate.2.1
    rw [hs.h_eq, hs.hE_eq, hs.m_eq]
    omega
  have hhnR : (p.h : ℝ) ≤ x.n := by exact_mod_cast hhn
  have hT1 : (1 : ℝ) ≤ p.T := by exact_mod_cast (show 1 ≤ p.T from hs.T_pos)
  have hrpos := NearCubicGates.NestedRateChain.ratio_positive _ hinit.2.2.1 i
  have hratio : (1 : ℝ) / NearCubicGates.NestedRateChain.rateRatio
      (NearCubicGates.PublicSamplingRates.initialRatio (p.T : ℝ) p.h p.ell0) i ≤ x.n := by
    apply (div_le_iff₀ hrpos).mpr
    have hmul := (div_le_iff₀ hhpos).mp (hinit.1.trans hmono)
    have hscale := mul_le_mul_of_nonneg_left hhnR hrpos.le
    nlinarith only [hmul, hscale, hT1]
  rw [← Builder.ratio_cast_chain hs] at hratio
  have hq : (1 : ℚ) / NearCubicGates.RationalRateChain.ratio
      (NearCubicGates.Close.Counter.firstRatio p.ell0 p.h p.T) i ≤ (x.n : ℚ) := by
    exact_mod_cast hratio
  exact Nat.ceil_le.mpr hq

/-- The actual chain multipliers in `sec:params`, paper/paper.tex, are bounded by the arity, so writing a factor does
not require the size of the full product. -/
theorem chain_factor_le_n (hs : ParameterRules x p) (i : ℕ) :
    NearCubicGates.RationalRateChain.factorRat
      (NearCubicGates.RationalRateChain.ratio
        (NearCubicGates.Close.Counter.firstRatio p.ell0 p.h p.T) i) ≤ x.n := by
  exact (Nat.findGreatest_le _).trans (hs.chain_factor_search_bound i)

/-- The factor-list length in `sec:params`, paper/paper.tex, is polynomially bounded in the arity for serialization. -/
theorem factors_length_preparation_bound (hs : ParameterRules x p) : p.factors.length ≤ x.n + 1 := by
  rw [hs.factors_eq]
  unfold NearCubicGates.Close.Counter.chainFactors
  simp only [List.length_map, List.length_range]
  have hJ := hs.J_bound
  have hmu := CoreRules.mu_le_lambda (hs : CoreRules x p)
  have hL := CoreRules.lambda_le_n (hs : CoreRules x p)
  rw [hs.Jmax_eq] at hJ
  omega

/-- The lifted window parameter in `sec:params`, paper/paper.tex, has a polynomial value bound controlled by the initial
denominator, rather than a product of separately bounded factors. -/
theorem Lambda_preparation_bound (hs : ParameterRules x p) : p.Lambda ≤ x.n ^ 2 * p.M1 + 1 := by
  have hL : p.Lw ≤ p.Dprime := by
    rw [hs.Lw_eq]
    unfold NearCubicGates.Close.Counter.windowInUse
    split_ifs
    · exact hs.window_bounds.2.1
    · exact le_rfl
  have hLn : p.Lw ≤ x.n ^ 2 := hL.trans
    (hs.scalar_window_upper.trans (Nat.pow_le_pow_left hs.prime_candidate.2.1 _))
  rw [hs.Lambda_eq]
  calc
    (p.Lw - 1) * p.A / 2 + 1 ≤ (p.Lw - 1) * p.A + 1 :=
      Nat.add_le_add_right (Nat.div_le_self _ _) _
    _ ≤ x.n ^ 2 * p.M1 + 1 := Nat.add_le_add_right
      (Nat.mul_le_mul ((Nat.sub_le p.Lw 1).trans hLn) hs.A_le_M1) _

end NearQuarticWires.Cells.ParameterRules
