import Proof.Quartic.Cells.AsymptoticsDegree
import Proof.Quartic.Cells.AsymptoticsNumerator
import Proof.Quartic.Cells.AsymptoticsMaskScale

set_option autoImplicit false

namespace NearQuarticWires.Cells

open ParameterArithmetic

/-- `sec:params`, paper/paper.tex: the greatest degree
allowed by the public scale data. -/
def availableDegree (x : ParameterInput) (p : Parameters) : ℕ :=
  Nat.findGreatest (DegreePass x.n p.m p.k p.Uocc) x.n

/-- `sec:params`, paper/paper.tex: the greatest prime
scale allowed by the public scale data and its printing-degree budget. -/
def availablePrime (x : ParameterInput) (p : Parameters) : ℕ :=
  Nat.findGreatest (PrimeCandidate x.n p.BN p.Jmax p.m p.Xmax (availableDegree x p)) x.n

namespace ParameterArithmetic

/-- `lem:asymptotics`, paper/paper.tex: an explicit
constant for the uniform lower bound on the chosen prime scale. -/
def primeScaleCoefficient (B1 : ℕ) : ℕ := 3840000 * (32 * B1 + 2200)

end ParameterArithmetic

namespace CoreRules

variable {x : ParameterInput} {p : Parameters}

/-- `lem:asymptotics`, paper/paper.tex: an explicit
affordable candidate proves that the maximal prime scale passes its finite
test, grows at least as a binary quarter power, and pays the `lambda mu²` price. -/
theorem prime_candidate_at (hs : CoreRules x p) (B1 : ℕ)
    (hb : 1 ≤ x.beta * (x.n : ℚ) ^ B1) (hL : 32 ≤ p.lambda)
    (hpoly : primeScaleCoefficient B1 * p.lambda ^ 3 ≤ 2 ^ (p.lambda / 4))
    (hdegree : 30000 * p.lambda ^ 2 ≤ x.n)
    (hmask : 2 * (4 * p.m * p.Xmax + 1) ≤ x.n / (10000 * p.lambda)) :
    PrimeCandidate x.n p.BN p.Jmax p.m p.Xmax (availableDegree x p) (availablePrime x p) ∧
      2 ^ (p.lambda / 4 + 1) ≤ availablePrime x p ∧
      x.n ≤ primeScaleCoefficient B1 * p.lambda * p.mu ^ 2 * availablePrime x p := by
  let L := p.lambda
  let M := p.mu
  let C := 32 * B1 + 2200
  let B := 384 * C * M ^ 2
  let D0 := x.n / (10000 * L)
  let P0 := 1 + D0 / B
  have hLp : 0 < L := by change 32 ≤ L at hL; omega
  have hMp : 0 < M := by have := hs.logarithms_pos.2; change 1 ≤ M at this; omega
  have hML : M ≤ L := hs.mu_le_lambda
  have hBp : 0 < B := by dsimp [B, C]; positivity
  have hden : 0 < 10000 * L := by positivity
  have hM2 := Nat.pow_le_pow_left hML 2
  have hpaid : 10000 * L * B ≤ 2 ^ (L / 4) := by
    calc
      10000 * L * B ≤ 10000 * L * (384 * C * L ^ 2) := by
        dsimp [B]
        exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hM2)
      _ = primeScaleCoefficient B1 * L ^ 3 := by dsimp [primeScaleCoefficient, C]; ring
      _ ≤ _ := hpoly
  have hnlow : 2 ^ (L - 1) < x.n := by
    change 2 ^ (p.lambda - 1) < x.n
    rw [hs.lambda_eq]
    simpa only [NearCubicGates.Target.lambda, Nat.pred_eq_sub_one] using
      (Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) (by have := hs.input_valid.1; omega : 1 < x.n))
  have hexp : L / 4 + (L / 4 + 1) ≤ L - 1 := by change 32 ≤ L at hL; omega
  have hroom : B * 2 ^ (L / 4 + 1) ≤ D0 := by
    apply (Nat.le_div_iff_mul_le hden).mpr
    calc
      (B * 2 ^ (L / 4 + 1)) * (10000 * L) =
          (10000 * L * B) * 2 ^ (L / 4 + 1) := by ring
      _ ≤ 2 ^ (L / 4) * 2 ^ (L / 4 + 1) := Nat.mul_le_mul_right _ hpaid
      _ = 2 ^ (L / 4 + (L / 4 + 1)) := (pow_add _ _ _).symm
      _ ≤ 2 ^ (L - 1) := Nat.pow_le_pow_right (by norm_num) hexp
      _ ≤ x.n := hnlow.le
  have hPbin : 2 ^ (L / 4 + 1) ≤ P0 := by
    have hquot : 2 ^ (L / 4 + 1) ≤ D0 / B := by
      apply (Nat.le_div_iff_mul_le hBp).mpr
      simpa only [Nat.mul_comm] using hroom
    dsimp [P0]
    omega
  have hP100 : 100 ≤ P0 := by
    have hpow : 2 ^ (7 : ℕ) ≤ 2 ^ (L / 4 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by change 32 ≤ L at hL; omega)
    norm_num at hpow
    omega
  have hDn : D0 * (10000 * L) ≤ x.n := Nat.div_mul_le_self _ _
  have hD2 : 2 * D0 ≤ x.n := by
    have h := Nat.mul_le_mul_left D0 (by omega : 2 ≤ 10000 * L)
    nlinarith
  have hPn : P0 ≤ x.n := by
    have hdiv : D0 / B ≤ D0 := Nat.div_le_self _ _
    have hn := hs.input_valid.1
    dsimp [P0]
    omega
  obtain ⟨e, he, hepos, hebound⟩ := hs.liftExponent_le_trial B1 hb P0 hPbin (by omega)
  have hJ : p.Jmax = M + 1 := hs.Jmax_eq
  have hfactor : 4 * ((2 * e - 1) * (2 * p.Jmax + 2)) ≤ B := by
    have hfirst : 2 * e - 1 ≤ 16 * C * M := by
      change e ≤ 8 * C * M at hebound
      calc
        2 * e - 1 ≤ 2 * e := Nat.sub_le _ _
        _ ≤ 2 * (8 * C * M) := Nat.mul_le_mul_left 2 hebound
        _ = 16 * C * M := by ring
    have hsecond : 2 * p.Jmax + 2 ≤ 6 * M := by rw [hJ]; omega
    calc
      4 * ((2 * e - 1) * (2 * p.Jmax + 2)) ≤ 4 * ((16 * C * M) * (6 * M)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul hfirst hsecond)
      _ = B := by dsimp [B]; ring
  have hbudget : 4 * ((2 * e - 1) * (2 * p.Jmax + 2) * (P0 - 1)) ≤ D0 := by
    calc
      4 * ((2 * e - 1) * (2 * p.Jmax + 2) * (P0 - 1)) =
          (4 * ((2 * e - 1) * (2 * p.Jmax + 2))) * (D0 / B) := by
            dsimp [P0]
            simp only [Nat.add_sub_cancel_left]
            ring
      _ ≤ B * (D0 / B) := Nat.mul_le_mul_right _ hfactor
      _ ≤ D0 := Nat.mul_div_le D0 B
  have hfit : D0 ≤ availableDegree x p := (hs.greatest_degree_bounds hdegree).1
  have hfull : (2 * e - 1) * (2 * p.Jmax + 2) * (P0 - 1) + 4 * p.m * p.Xmax ≤
      availableDegree x p := by
    have hm : 2 * (4 * p.m * p.Xmax + 1) ≤ D0 := hmask
    nlinarith
  have hcand : PrimeCandidate x.n p.BN p.Jmax p.m p.Xmax (availableDegree x p) P0 := by
    refine ⟨hP100, hPn, ?_⟩
    change (match liftExponent p.BN P0 with
      | none => False
      | some f => (2 * f - 1) * (2 * p.Jmax + 2) * (P0 - 1) + 4 * p.m * p.Xmax ≤
          availableDegree x p)
    rw [he]
    exact hfull
  have hgreater : P0 ≤ availablePrime x p := Nat.le_findGreatest hPn hcand
  have hselected : PrimeCandidate x.n p.BN p.Jmax p.m p.Xmax (availableDegree x p)
      (availablePrime x p) := Nat.findGreatest_spec hPn hcand
  have hnrem := Nat.mod_lt x.n hden
  have hndiv := Nat.mod_add_div x.n (10000 * L)
  have hnprice : x.n ≤ 10000 * L * (D0 + 1) := by
    dsimp only [D0]
    nlinarith
  have hBrem := Nat.mod_lt D0 hBp
  have hBdiv := Nat.mod_add_div D0 B
  have hquot : D0 + 1 ≤ B * P0 := by dsimp only [P0]; nlinarith
  have hprice : x.n ≤ primeScaleCoefficient B1 * L * M ^ 2 * P0 := by
    calc
      x.n ≤ 10000 * L * (D0 + 1) := hnprice
      _ ≤ 10000 * L * (B * P0) := Nat.mul_le_mul_left _ hquot
      _ = primeScaleCoefficient B1 * L * M ^ 2 * P0 := by
        dsimp [B, C, primeScaleCoefficient]
        ring
  refine ⟨hselected, hPbin.trans hgreater, ?_⟩
  exact hprice.trans (Nat.mul_le_mul_left _ hgreater)

/-- `lem:asymptotics`, paper/paper.tex: uniformly over
all admitted public scale data, the maximal prime choice eventually passes and
has the required quantitative lower bounds. -/
theorem eventual_prime_candidates (B1 : ℕ) : ∃ onset : ℕ, 4 ≤ onset ∧
    ∀ (x : ParameterInput) (p : Parameters), onset ≤ x.n → CoreRules x p →
      1 ≤ x.beta * (x.n : ℚ) ^ B1 →
      PrimeCandidate x.n p.BN p.Jmax p.m p.Xmax (availableDegree x p) (availablePrime x p) ∧
        2 ^ (p.lambda / 4 + 1) ≤ availablePrime x p ∧
        x.n ≤ primeScaleCoefficient B1 * p.lambda * p.mu ^ 2 * availablePrime x p := by
  obtain ⟨op, hop, hp⟩ := NearCubicGates.Close.Counter.polynomial_lambda_binary (primeScaleCoefficient B1) 3
  obtain ⟨od, hod, hd⟩ := NearCubicGates.Close.Closure.lambda_poly_lt 30000 2
  obtain ⟨om, hom, hm⟩ := NearCubicGates.Close.Closure.lambda_poly_lt
    ((640000 : ℕ) ^ 2 * (600 * (B1 + 20) ^ 2) + 3000000) 7
  refine ⟨max op (max od (max om (2 ^ 32))), by omega, ?_⟩
  intro x p hn hs hb
  have hL : 32 ≤ p.lambda := by
    rw [hs.lambda_eq]
    have h := Nat.clog_mono_right 2 (by omega : 2 ^ (32 : ℕ) ≤ x.n)
    simpa only [Nat.clog_pow 2 32 (by norm_num), NearCubicGates.Target.lambda] using h
  have hpoly : primeScaleCoefficient B1 * p.lambda ^ 3 ≤ 2 ^ (p.lambda / 4) := by
    rw [hs.lambda_eq]
    exact (hp x.n (by omega)).2
  have hdegree : 30000 * p.lambda ^ 2 ≤ x.n := by
    rw [hs.lambda_eq]
    exact (hd x.n (by omega)).le
  have hmask : 2 * (4 * p.m * p.Xmax + 1) ≤ x.n / (10000 * p.lambda) := by
    apply hs.mask_degree_of_log B1 hb
    rw [hs.lambda_eq]
    exact (hm x.n (by omega)).le
  exact hs.prime_candidate_at B1 hb hL hpoly hdegree hmask

end CoreRules

namespace ParameterRules

variable {x : ParameterInput} {p : Parameters}

/-- `sec:params`, paper/paper.tex: a selected degree
is exactly the degree computed from its public scale data. -/
theorem available_degree_eq (hs : ParameterRules x p) : availableDegree x p = p.Dmax :=
  hs.Dmax_eq.symm

/-- `sec:params`, paper/paper.tex: a selected prime
scale is exactly the maximal choice computed from the public scale data. -/
theorem available_prime_eq (hs : ParameterRules x p) : availablePrime x p = p.P := by
  unfold availablePrime
  rw [hs.available_degree_eq]
  exact hs.P_eq.symm

/-- `lem:asymptotics`, paper/paper.tex: the actual
selected prime scale obeys the uniform binary and `n/(lambda mu²)` lower bounds. -/
theorem eventual_prime_bounds (B1 : ℕ) : ∃ onset : ℕ, 4 ≤ onset ∧
    ∀ (x : ParameterInput) (p : Parameters), onset ≤ x.n → ParameterRules x p →
      1 ≤ x.beta * (x.n : ℚ) ^ B1 →
      2 ^ (p.lambda / 4 + 1) ≤ p.P ∧
        x.n ≤ primeScaleCoefficient B1 * p.lambda * p.mu ^ 2 * p.P := by
  obtain ⟨onset, hon, h⟩ := CoreRules.eventual_prime_candidates B1
  refine ⟨onset, hon, ?_⟩
  intro x p hn hs hb
  obtain ⟨_, hp, hprice⟩ := h x p hn (hs : CoreRules x p) hb
  rw [hs.available_prime_eq] at hp hprice
  exact ⟨hp, hprice⟩

end ParameterRules

/-- `lem:asymptotics`, paper/paper.tex: the computed
public scales eventually supply a passing maximal prime candidate before any
later rate-chain or prime-set acceptance condition is assumed. -/
theorem eventual_publicScales_prime (B1 : ℕ) : ∃ onset : ℕ, 4 ≤ onset ∧
    ∀ x : ParameterInput, onset ≤ x.n → ValidInput x → 1 ≤ x.beta * (x.n : ℚ) ^ B1 →
      let p := publicScales x
      PrimeCandidate x.n p.BN p.Jmax p.m p.Xmax (availableDegree x p) (availablePrime x p) ∧
        2 ^ (p.lambda / 4 + 1) ≤ availablePrime x p ∧
        x.n ≤ primeScaleCoefficient B1 * p.lambda * p.mu ^ 2 * availablePrime x p := by
  obtain ⟨oc, hoc, hc⟩ := eventual_publicScales_core
  obtain ⟨op, hop, hp⟩ := CoreRules.eventual_prime_candidates B1
  refine ⟨max oc op, by omega, ?_⟩
  intro x hn hv hb
  exact hp x (publicScales x) (by omega) (hc x (by omega) hv) hb

end NearQuarticWires.Cells
