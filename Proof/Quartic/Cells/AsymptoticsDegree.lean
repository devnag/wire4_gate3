import Proof.Quartic.Cells.ParametersPublic

set_option autoImplicit false

namespace NearQuarticWires.Cells.CoreRules

open ParameterArithmetic

variable {x : ParameterInput} {p : Parameters}

/-- `lem:asymptotics`, paper/paper.tex: the initial
printing-degree test follows from an explicit quadratic logarithmic threshold. -/
theorem degree_zero_of_log (hs : CoreRules x p) (hn : 7000 * p.lambda ^ 2 ≤ x.n) :
    DegreePass x.n p.m p.k p.Uocc 0 := by
  have hk0 := hs.k_le
  have hm := hs.mu_le_lambda
  have hmul := Nat.mul_le_mul_right (16 * p.lambda) hm
  have hk : p.k ≤ 16 * p.lambda ^ 2 := by nlinarith
  have hl := hs.logarithms_pos.1
  have htot : 100 * (4 * p.k + 2) + p.k ≤ x.n := by nlinarith
  unfold DegreePass
  rw [hs.m_eq]
  simp only [zero_mul, add_zero]
  omega

/-- `lem:asymptotics`, paper/paper.tex: a concrete
degree of order `n/lambda` satisfies the actual finite printing inequality. -/
theorem degree_trial (hs : CoreRules x p) (hn : 30000 * p.lambda ^ 2 ≤ x.n) :
    DegreePass x.n p.m p.k p.Uocc (x.n / (10000 * p.lambda)) := by
  let D := x.n / (10000 * p.lambda)
  have hk0 := hs.k_le
  have hm := hs.mu_le_lambda
  have hmul := Nat.mul_le_mul_right (16 * p.lambda) hm
  have hk : p.k ≤ 16 * p.lambda ^ 2 := by nlinarith
  have hl := hs.logarithms_pos.1
  have hhead : 2 * (100 * (4 * p.k + 2) + p.k) ≤ x.n := by nlinarith
  have hlog := hs.clog_Uocc_bounds.2
  have hdiv : D * (10000 * p.lambda) ≤ x.n := Nat.div_mul_le_self _ _
  have htail : 8 * (100 * D * Nat.clog 2 p.Uocc) ≤ x.n := by
    have h := Nat.mul_le_mul_left (800 * D) hlog
    nlinarith
  have htot : 100 * (4 * p.k + 2 + D * Nat.clog 2 p.Uocc) + p.k ≤ x.n := by
    nlinarith
  unfold DegreePass
  rw [hs.m_eq]
  change 100 * (4 * p.k + 2 + D * Nat.clog 2 p.Uocc) ≤ x.n - p.k
  omega

/-- `lem:asymptotics`, paper/paper.tex: the greatest
passing degree has matching explicit bounds before any prime or chain test. -/
theorem greatest_degree_bounds (hs : CoreRules x p) (hn : 30000 * p.lambda ^ 2 ≤ x.n) :
    x.n / (10000 * p.lambda) ≤ Nat.findGreatest (DegreePass x.n p.m p.k p.Uocc) x.n ∧
      Nat.findGreatest (DegreePass x.n p.m p.k p.Uocc) x.n ≤ x.n / (100 * p.lambda) := by
  constructor
  · exact Nat.le_findGreatest (Nat.div_le_self _ _) (hs.degree_trial hn)
  · have hz := hs.degree_zero_of_log (by nlinarith : 7000 * p.lambda ^ 2 ≤ x.n)
    have hpass := Nat.findGreatest_spec (Nat.zero_le x.n) hz
    have hlog := hs.clog_Uocc_bounds.1
    have hl := hs.logarithms_pos.1
    apply (Nat.le_div_iff_mul_le (by positivity : 0 < 100 * p.lambda)).mpr
    change 100 * (p.m * p.k + 2 +
      Nat.findGreatest (DegreePass x.n p.m p.k p.Uocc) x.n * Nat.clog 2 p.Uocc) ≤
        x.n - p.k at hpass
    have hm := Nat.mul_le_mul_left
      (Nat.findGreatest (DegreePass x.n p.m p.k p.Uocc) x.n) hlog
    nlinarith [Nat.sub_le x.n p.k]

end NearQuarticWires.Cells.CoreRules

namespace NearQuarticWires.Cells

open ParameterArithmetic

/-- `lem:asymptotics`, paper/paper.tex: every normalized
call eventually passes degree zero, and its greatest passing degree is of order
`n/lambda`, independently of all later acceptance conditions. -/
theorem eventual_publicScales_degree : ∃ onset : ℕ, 4 ≤ onset ∧
    ∀ x : ParameterInput, onset ≤ x.n → ValidInput x →
      let p := publicScales x
      DegreePass x.n p.m p.k p.Uocc 0 ∧
        (x.n / (10000 * p.lambda) ≤ Nat.findGreatest (DegreePass x.n p.m p.k p.Uocc) x.n ∧
          Nat.findGreatest (DegreePass x.n p.m p.k p.Uocc) x.n ≤ x.n / (100 * p.lambda)) := by
  obtain ⟨oc, hoc, hc⟩ := eventual_publicScales_core
  obtain ⟨od, hod, hd⟩ := NearCubicGates.Close.Closure.lambda_poly_lt 30000 2
  refine ⟨max oc od, by omega, ?_⟩
  intro x hn hv
  have hs := hc x (by omega) hv
  have hlarge : 30000 * (publicScales x).lambda ^ 2 ≤ x.n := by
    rw [hs.lambda_eq]
    exact (hd x.n (by omega)).le
  exact ⟨hs.degree_zero_of_log (by nlinarith : 7000 * (publicScales x).lambda ^ 2 ≤ x.n),
    hs.greatest_degree_bounds hlarge⟩

end NearQuarticWires.Cells
