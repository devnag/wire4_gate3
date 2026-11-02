import Proof.Quartic.Cells.ParametersCore

set_option autoImplicit false

namespace NearQuarticWires.Cells.CoreRules

open ParameterArithmetic

variable {x : ParameterInput} {p : Parameters}

/-- `sec:params`, paper/paper.tex: every selected call has
positive precision. -/
theorem beta_pos (hs : CoreRules x p) : 0 < x.beta := hs.input_valid.2.2.2.2.1

/-- `sec:params`, paper/paper.tex: every selected input
length is positive. -/
theorem n_pos (hs : CoreRules x p) : 0 < x.n := by
  have := hs.input_valid.1
  omega

/-- `sec:params`, paper/paper.tex: both Fourier periods
are positive, including an inactive second group. -/
theorem omega_pos (hs : CoreRules x p) : 0 < p.omega1 ∧ 0 < p.omega2 := by
  rw [hs.omega1_eq, hs.omega2_eq]
  omega

/-- `sec:params`, paper/paper.tex: the Fourier mass
upper bound is positive. -/
theorem MF_pos (hs : CoreRules x p) : 0 < p.MF := by
  have hw := hs.omega_pos
  have hr := le_ceilSqrt_sq (p.omega1 * p.omega2)
  rw [← hs.MF_eq] at hr
  nlinarith

/-- `sec:params`, paper/paper.tex: the selected sampler
tolerance is positive. -/
theorem eta_pos (hs : CoreRules x p) : 0 < p.eta := by
  rw [hs.eta_eq]
  have := hs.beta_pos
  have := hs.MF_pos
  positivity

/-- `sec:params`, paper/paper.tex: literal least-positive
characterization of the selected concentration exponent. -/
theorem T_le_iff (hs : CoreRules x p) (t : ℕ) :
    p.T ≤ t ↔ 1 ≤ t ∧
      ((2 ^ (p.m * p.k + 2 * p.m + 5) * p.Jmax : ℕ) : ℚ) ≤ 2 ^ t * x.beta := by
  rw [hs.T_eq]
  exact concentrationT_le_iff _ _ _ hs.beta_pos t

/-- `sec:params`, paper/paper.tex: positivity of `T`. -/
theorem T_pos (hs : CoreRules x p) : 0 < p.T := by
  have := ((hs.T_le_iff p.T).mp le_rfl).1
  omega

/-- `sec:params`, paper/paper.tex: the literal integer
square comparison characterizes the least selected value of `Xmax`. -/
theorem Xmax_le_iff (hs : CoreRules x p) (t : ℕ) :
    p.Xmax ≤ t ↔ 9 * p.tau ^ 2 * x.n * p.r ≤ t ^ 2 := by
  rw [hs.Xmax_eq]
  exact ceilSqrt_le_iff _ _

/-- `sec:params`, paper/paper.tex: the literal Fourier
group cardinality characterizes the least value of `MF`. -/
theorem MF_le_iff (hs : CoreRules x p) (t : ℕ) :
    p.MF ≤ t ↔ p.omega1 * p.omega2 ≤ t ^ 2 := by
  rw [hs.MF_eq]
  exact ceilSqrt_le_iff _ _

/-- `sec:params`, paper/paper.tex: the least upper
population scale is exactly selected by a rational squared comparison. -/
theorem U_le_iff (hs : CoreRules x p) (t : ℕ) :
    p.U ≤ t ↔ p.tau ≤ t ∧
      (96 ^ 2 * (p.r : ℚ) ^ 3 * (x.W : ℚ) ^ 2) /
        (x.beta ^ 2 * (x.n : ℚ) ^ 3) ≤ (t : ℚ) ^ 2 := by
  rw [hs.U_eq, max_le_iff, ceilSqrtRat_le_iff]

/-- `sec:params`, paper/paper.tex: the least dyadic
sample exponent satisfies the exact fourth-power test. -/
theorem Qexp_le_iff (hs : CoreRules x p) (q : ℕ) :
    p.Qexp ≤ q ↔
      ((1024 * p.N * p.m : ℕ) : ℚ) ^ 4 * (4 * p.N ^ 2 * (2 * (p.omega1 * p.omega2)) : ℕ) ≤
        (((2 ^ q : ℕ) : ℚ) ^ 4) * p.eta ^ 8 := by
  rw [hs.Qexp_eq]
  exact sampleExponent_le_iff _ _ _ hs.eta_pos q

/-- `sec:params`, paper/paper.tex: the selected sample
size pays the concrete raised-power Fourier budget. -/
theorem sample_budget (hs : CoreRules x p) :
    ((1024 * p.N * p.m : ℕ) : ℚ) ^ 4 * (4 * p.N ^ 2 * (2 * (p.omega1 * p.omega2)) : ℕ) ≤
      (p.Q : ℚ) ^ 4 * p.eta ^ 8 := by
  rw [hs.Q_eq]
  exact ((hs.Qexp_le_iff p.Qexp).mp le_rfl)

/-- `sec:params`, paper/paper.tex: the occurrence factor
is at least two at every selected input. -/
theorem Uocc_two (hs : CoreRules x p) : 2 ≤ p.Uocc := by
  have hn := hs.n_pos
  have hc : 0 < p.childCap := by
    rw [hs.childCap_eq]
    unfold Cells.childCap
    positivity
  have ha : 0 < p.NatAtoms := by
    rw [hs.NatAtoms_eq]
    positivity
  rw [hs.Uocc_eq]
  have := Nat.mul_pos ha hc
  omega

/-- `sec:params`, paper/paper.tex: the common numerator
exponent is exactly the product bound used for signed residue uniqueness. -/
theorem numerator_power_identity (hs : CoreRules x p) :
    2 ^ p.BN = 2 * 2 ^ p.S * 2 ^ (p.m * p.k) * (p.N ^ 2 * p.Q) ^ (2 * p.m) := by
  have hp : p.N ^ 2 * p.Q = 2 ^ ((p.k / 2) * 2 + p.Qexp) := by
    rw [hs.N_eq, hs.Q_eq, ← pow_mul, ← pow_add]
  have hl : Nat.clog 2 (p.N ^ 2 * p.Q) = (p.k / 2) * 2 + p.Qexp := by
    rw [hp, Nat.clog_pow 2 _ (by norm_num)]
  rw [hs.BN_eq, hl, hp]
  rw [← pow_mul, Nat.mul_comm ((p.k / 2) * 2 + p.Qexp) (2 * p.m)]
  simp only [pow_add, pow_one]
  ring

end NearQuarticWires.Cells.CoreRules

namespace NearQuarticWires.Cells.ParameterRules

open ParameterArithmetic

variable {x : ParameterInput} {p : Parameters}

/-- `sec:params`, paper/paper.tex: every selected call has
positive precision. -/
theorem beta_pos (hs : ParameterRules x p) : 0 < x.beta :=
  CoreRules.beta_pos (hs : CoreRules x p)

/-- `sec:params`, paper/paper.tex: every selected input
length is positive. -/
theorem n_pos (hs : ParameterRules x p) : 0 < x.n :=
  CoreRules.n_pos (hs : CoreRules x p)

/-- `sec:params`, paper/paper.tex: both Fourier periods
are positive, including an inactive second group. -/
theorem omega_pos (hs : ParameterRules x p) : 0 < p.omega1 ∧ 0 < p.omega2 :=
  CoreRules.omega_pos (hs : CoreRules x p)

/-- `sec:params`, paper/paper.tex: the Fourier mass
upper bound is positive. -/
theorem MF_pos (hs : ParameterRules x p) : 0 < p.MF :=
  CoreRules.MF_pos (hs : CoreRules x p)

/-- `sec:params`, paper/paper.tex: the selected sampler
tolerance is positive. -/
theorem eta_pos (hs : ParameterRules x p) : 0 < p.eta :=
  CoreRules.eta_pos (hs : CoreRules x p)

/-- `sec:params`, paper/paper.tex: literal least-positive
characterization of the selected concentration exponent. -/
theorem T_le_iff (hs : ParameterRules x p) (t : ℕ) :
    p.T ≤ t ↔ 1 ≤ t ∧
      ((2 ^ (p.m * p.k + 2 * p.m + 5) * p.Jmax : ℕ) : ℚ) ≤ 2 ^ t * x.beta :=
  CoreRules.T_le_iff (hs : CoreRules x p) t

/-- `sec:params`, paper/paper.tex: positivity of `T`. -/
theorem T_pos (hs : ParameterRules x p) : 0 < p.T :=
  CoreRules.T_pos (hs : CoreRules x p)

/-- `sec:params`, paper/paper.tex: the literal integer
square comparison characterizes the least selected value of `Xmax`. -/
theorem Xmax_le_iff (hs : ParameterRules x p) (t : ℕ) :
    p.Xmax ≤ t ↔ 9 * p.tau ^ 2 * x.n * p.r ≤ t ^ 2 :=
  CoreRules.Xmax_le_iff (hs : CoreRules x p) t

/-- `sec:params`, paper/paper.tex: the literal Fourier
group cardinality characterizes the least value of `MF`. -/
theorem MF_le_iff (hs : ParameterRules x p) (t : ℕ) :
    p.MF ≤ t ↔ p.omega1 * p.omega2 ≤ t ^ 2 :=
  CoreRules.MF_le_iff (hs : CoreRules x p) t

/-- `sec:params`, paper/paper.tex: the least upper
population scale is exactly selected by a rational squared comparison. -/
theorem U_le_iff (hs : ParameterRules x p) (t : ℕ) :
    p.U ≤ t ↔ p.tau ≤ t ∧
      (96 ^ 2 * (p.r : ℚ) ^ 3 * (x.W : ℚ) ^ 2) /
        (x.beta ^ 2 * (x.n : ℚ) ^ 3) ≤ (t : ℚ) ^ 2 :=
  CoreRules.U_le_iff (hs : CoreRules x p) t

/-- `sec:params`, paper/paper.tex: the least dyadic
sample exponent satisfies the exact fourth-power test. -/
theorem Qexp_le_iff (hs : ParameterRules x p) (q : ℕ) :
    p.Qexp ≤ q ↔
      ((1024 * p.N * p.m : ℕ) : ℚ) ^ 4 * (4 * p.N ^ 2 * (2 * (p.omega1 * p.omega2)) : ℕ) ≤
        (((2 ^ q : ℕ) : ℚ) ^ 4) * p.eta ^ 8 :=
  CoreRules.Qexp_le_iff (hs : CoreRules x p) q

/-- `sec:params`, paper/paper.tex: the selected sample
size pays the concrete raised-power Fourier budget. -/
theorem sample_budget (hs : ParameterRules x p) :
    ((1024 * p.N * p.m : ℕ) : ℚ) ^ 4 * (4 * p.N ^ 2 * (2 * (p.omega1 * p.omega2)) : ℕ) ≤
      (p.Q : ℚ) ^ 4 * p.eta ^ 8 :=
  CoreRules.sample_budget (hs : CoreRules x p)

/-- `sec:params`, paper/paper.tex: even the degree-zero
printing guard forces a nonempty outer input block. -/
theorem k_lt_n (hs : ParameterRules x p) : p.k < x.n := by
  have hd := hs.initial_degree
  unfold DegreePass at hd
  omega

/-- `sec:params`, paper/paper.tex: the occurrence factor
is at least two at every selected input. -/
theorem Uocc_two (hs : ParameterRules x p) : 2 ≤ p.Uocc :=
  CoreRules.Uocc_two (hs : CoreRules x p)

/-- `sec:params`, paper/paper.tex: `Dmax` is the largest
degree satisfying the actual logarithmic printing budget. -/
theorem degree_maximal (hs : ParameterRules x p) :
    DegreePass x.n p.m p.k p.Uocc p.Dmax ∧
      ∀ D, DegreePass x.n p.m p.k p.Uocc D → D ≤ p.Dmax := by
  rw [hs.Dmax_eq]
  refine ⟨Nat.findGreatest_spec (Nat.zero_le _) hs.initial_degree, ?_⟩
  intro D hD
  apply Nat.le_findGreatest ?_ hD
  have hlog : 1 ≤ Nat.clog 2 p.Uocc :=
    Nat.clog_pos (by norm_num) (by have := hs.Uocc_two; omega)
  unfold DegreePass at hD
  have hmul := Nat.mul_le_mul_left D hlog
  nlinarith [Nat.sub_le x.n p.k]

/-- `eq:prime-budget`, paper/paper.tex: `P` is the largest
passing candidate throughout the whole prescribed interval. -/
theorem prime_maximal (hs : ParameterRules x p) :
    100 ≤ p.P ∧ p.P ≤ x.n ∧
      ∀ P, PrimeCandidate x.n p.BN p.Jmax p.m p.Xmax p.Dmax P → P ≤ p.P := by
  refine ⟨hs.prime_candidate.1, hs.prime_candidate.2.1, ?_⟩
  intro P hP
  rw [hs.P_eq]
  exact Nat.le_findGreatest hP.2.1 hP

/-- `sec:params`, paper/paper.tex: the selected exponent
is positive and is least for the exact lift inequality. -/
theorem lift_spec (hs : ParameterRules x p) :
    LiftPass p.BN p.P p.e ∧ p.e ≤ p.BN + 1 ∧
      ∀ t, t < p.e → ¬ LiftPass p.BN p.P t :=
  liftExponent_spec _ _ _ hs.e_eq

/-- `sec:params`, paper/paper.tex: every selected prime
strictly lifts past the common signed numerator bound. -/
theorem selected_prime_pow_gt (hs : ParameterRules x p) (q : ℕ) (hq : q ∈ p.primes) :
    2 ^ p.BN < q ^ p.e := by
  rw [hs.primes_eq, NearCubicGates.Close.Counter.mem_dyadicPrimes] at hq
  exact ParameterArithmetic.prime_pow_gt _ _ _ _ hs.lift_spec.1 hq.2.2

/-- `sec:params`, paper/paper.tex: the common numerator
exponent is exactly the product bound used for signed residue uniqueness. -/
theorem numerator_power_identity (hs : ParameterRules x p) :
    2 ^ p.BN = 2 * 2 ^ p.S * 2 ^ (p.m * p.k) * (p.N ^ 2 * p.Q) ^ (2 * p.m) :=
  CoreRules.numerator_power_identity (hs : CoreRules x p)

/-- `lem:print` and `sec:params`, paper/paper.tex: every permitted table fits the prescribed exponential entry cap. -/
theorem printing_entries (hs : ParameterRules x p) (D : ℕ) (hD : D ≤ p.Dmax) :
    2 ^ (p.m * p.k) * p.Uocc ^ D ≤ 2 ^ ((x.n - p.k) / 100) := by
  have hb := hs.degree_maximal.1
  unfold DegreePass at hb
  have hd := Nat.mul_le_mul_right (Nat.clog 2 p.Uocc) hD
  have he : p.m * p.k + D * Nat.clog 2 p.Uocc ≤ (x.n - p.k) / 100 := by
    apply (Nat.le_div_iff_mul_le (by norm_num : 0 < (100 : ℕ))).mpr
    nlinarith
  calc
    2 ^ (p.m * p.k) * p.Uocc ^ D ≤
        2 ^ (p.m * p.k) * (2 ^ Nat.clog 2 p.Uocc) ^ D := by
          gcongr
          exact Nat.le_pow_clog (by norm_num) _
    _ = 2 ^ (p.m * p.k + D * Nat.clog 2 p.Uocc) := by
      rw [← pow_mul, ← pow_add, Nat.mul_comm (Nat.clog 2 p.Uocc) D]
    _ ≤ 2 ^ ((x.n - p.k) / 100) := by gcongr; norm_num

end NearQuarticWires.Cells.ParameterRules
