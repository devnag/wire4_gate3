import Proof.Quartic.Cells.ParametersPreparationBits
import Proof.Quartic.StagePrep.PrintingSizes
import Proof.Quartic.StagePrep.PrimeBudget

set_option autoImplicit false

namespace NearQuarticWires.Cells.ParameterArithmetic

/-- `prop:time`, paper/paper.tex: any fixed
multiple of the cubic binary scale fits a fourth-power physical
register width after enlarging its fixed additive constant. -/
theorem preparationBitBase_mul_width (c B1 : ℕ) :
    ∃ K : ℕ, 0 < K ∧ ∀ L : ℕ, c * preparationBitBase B1 L ≤ (L + K) ^ 4 := by
  let C := c * (preparationCoefficient B1 + 33 * B1 + 4000)
  refine ⟨C + 2, by omega, fun L => ?_⟩
  calc
    c * preparationBitBase B1 L ≤ C * (L + 1) ^ 3 := by
      simpa only [C, Nat.mul_assoc] using Nat.mul_le_mul_left c (preparationBitBase_cubic B1 L)
    _ ≤ (L + (C + 2)) * (L + (C + 2)) ^ 3 :=
      Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left (by omega) 3)
    _ = (L + (C + 2)) ^ 4 := by ring

end NearQuarticWires.Cells.ParameterArithmetic

namespace NearQuarticWires.Cells.CoreRules

open ParameterArithmetic

variable {x : ParameterInput} {p : Parameters}

/-- `sec:params` and `prop:time`, paper/paper.tex: every early printer census and stored coefficient
scale has the common binary height before later selection guards. -/
theorem printing_operand_binary_bounds (hs : CoreRules x p) (B1 L : ℕ)
    (hn : x.n ≤ L) (hb : 1 ≤ x.beta * (x.n : ℚ) ^ B1) :
    let H := preparationBitBase B1 L
    p.NatAtoms ≤ 2 ^ H ∧ p.childCap ≤ 2 ^ H ∧ p.Uocc ≤ 2 ^ H ∧
      p.Jmax ≤ 2 ^ H ∧ p.k ≤ 2 ^ H ∧ p.S ≤ 2 ^ H ∧ p.BN ≤ 2 ^ H ∧
      p.N * p.N * p.Q ≤ 2 ^ H ∧ Nat.clog 2 p.Uocc ≤ H ∧
      Nat.clog 2 (p.N * p.N * p.Q) ≤ H := by
  generalize hHdef : preparationBitBase B1 L = H
  have hV := hs.preparationEnvelope_binary_height B1 L hn
  rw [hHdef] at hV
  have hscalar := hs.early_preparation_bounds B1 hb
  have hatom : p.NatAtoms ≤ preparationEnvelope B1 x.n := by
    calc
      p.NatAtoms = 34 * x.n ^ 4 := by rw [hs.NatAtoms_eq, hs.m_eq]; ring
      _ ≤ _ := preparation_envelope_base B1 x.n 34 4 (by simp [preparationCoefficients]) (by omega)
  have hchild : p.childCap ≤ preparationEnvelope B1 x.n := by
    calc
      p.childCap ≤ 8 * x.n ^ 2 * p.lambda := hs.childCap_le
      _ ≤ 8 * x.n ^ 2 * x.n := Nat.mul_le_mul_left _ hs.lambda_le_n
      _ = 8 * x.n ^ 3 := by ring
      _ ≤ _ := preparation_envelope_base B1 x.n 8 3 (by simp [preparationCoefficients]) (by omega)
  have hocc : p.Uocc ≤ preparationEnvelope B1 x.n := by
    calc
      p.Uocc ≤ 273 * x.n ^ 6 * p.lambda := hs.Uocc_polynomial
      _ ≤ 273 * x.n ^ 6 * x.n := Nat.mul_le_mul_left _ hs.lambda_le_n
      _ = 273 * x.n ^ 7 := by ring
      _ ≤ _ := preparation_envelope_base B1 x.n 273 7 (by simp [preparationCoefficients]) (by omega)
  have hJ : p.Jmax ≤ preparationEnvelope B1 x.n := by
    have hm := hs.mu_le_lambda.trans hs.lambda_le_n
    rw [hs.Jmax_eq]
    exact (by omega : p.mu + 1 ≤ x.n + 1).trans (preparation_envelope_arity B1 x.n)
  have hoccB : p.Uocc ≤ 2 ^ H := hocc.trans hV
  have hk := hs.k_preparation_bound
  have hq := hs.Qexp_preparation_bound B1 hb
  have hpow : x.n ^ 2 ≤ (L + 1) ^ 3 :=
    (Nat.pow_le_pow_left (hn.trans (Nat.le_succ L)) 2).trans
      (Nat.pow_le_pow_right (Nat.succ_pos L) (by omega))
  have hexp : p.k + p.Qexp ≤ H := by
    calc
      p.k + p.Qexp ≤ (2 * B1 + 128) * x.n ^ 2 := by nlinarith only [hk, hq]
      _ ≤ (32 * B1 + 2200) * (L + 1) ^ 3 := Nat.mul_le_mul (by omega) hpow
      _ ≤ H := by rw [← hHdef]; unfold preparationBitBase; omega
  have hNQ : p.N * p.N * p.Q ≤ 2 ^ H := by
    rw [← pow_two, hs.N_square, hs.Q_eq, ← pow_add]
    exact Nat.pow_le_pow_right (by norm_num) hexp
  exact ⟨hatom.trans hV, hchild.trans hV, hoccB, hJ.trans hV,
    hscalar.k.trans hV, hscalar.S.trans hV, hscalar.BN.trans hV, hNQ,
    (Nat.clog_le_iff_le_pow (by norm_num)).mpr hoccB,
    (Nat.clog_le_iff_le_pow (by norm_num)).mpr hNQ⟩

/-- `sec:params` and `prop:time`, paper/paper.tex: the exact occurrence computation and its initial
degree-logarithm guard fit the common cubic binary width. -/
theorem printingSizes_operand_binary_bound (hs : CoreRules x p) (B1 L : ℕ)
    (hn : x.n ≤ L) (hb : 1 ≤ x.beta * (x.n : ℚ) ^ B1) :
    let H := preparationBitBase B1 L
    p.NatAtoms * p.childCap + p.NatAtoms + p.childCap + 2 * x.n ^ 4 +
      (4 * p.m + 1) + (NearCubicGates.Close.Counter.B0 x.n + p.lambda + 3) + 128 <
        2 ^ (100 * H) ∧ 2 * p.Uocc + 2 < 2 ^ (100 * H) := by
  generalize hHdef : preparationBitBase B1 L = H
  have hH := preparationBitBase_bounds B1 L
  rw [hHdef] at hH
  have he := hs.printing_operand_binary_bounds B1 L hn hb
  simp only [hHdef] at he
  have hatom : p.NatAtoms ≤ 2 ^ H := he.1
  have hchild : p.childCap ≤ 2 ^ H := he.2.1
  have hocc : p.Uocc ≤ 2 ^ H := he.2.2.1
  have hparts : 2 * x.n ^ 4 ≤ p.NatAtoms ∧ 4 * p.m + 1 ≤ p.NatAtoms ∧
      NearCubicGates.Close.Counter.B0 x.n + p.lambda + 3 ≤ p.childCap := by
    have hnpos := hs.n_pos
    constructor
    · rw [hs.NatAtoms_eq]
      exact Nat.le_mul_of_pos_left _ (by omega)
    constructor
    · rw [hs.NatAtoms_eq]
      exact Nat.le_mul_of_pos_right _ (by positivity)
    · rw [hs.childCap_eq]
      unfold Cells.childCap
      rw [show Nat.clog 2 x.n = p.lambda from hs.lambda_eq.symm]
      exact Nat.le_mul_of_pos_left _ hnpos
  have h128 : 128 ≤ 2 ^ H := (by norm_num : 128 ≤ 2 ^ 7).trans
    (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hp : 0 < (2 : ℕ) ^ H := Nat.pow_pos (by norm_num)
  have hprod : p.NatAtoms * p.childCap ≤ 2 ^ (2 * H) := by
    calc
      _ ≤ 2 ^ H * 2 ^ H := Nat.mul_le_mul hatom hchild
      _ = _ := by rw [← pow_add]; exact congrArg (fun e : ℕ => 2 ^ e) (by omega)
  have hmono : 2 ^ H ≤ 2 ^ (2 * H) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hbig : 8 * 2 ^ (2 * H) ≤ 2 ^ (100 * H) := by
    calc
      _ = 2 ^ (2 * H + 3) := by rw [pow_add]; norm_num; ring
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hpositive : 0 < (2 : ℕ) ^ (2 * H) := Nat.pow_pos (by norm_num)
  have hsmall : 2 * p.Uocc + 2 < 2 ^ (H + 2) := by rw [pow_add]; norm_num; omega
  constructor
  · have ha := hatom.trans hmono
    have hc := hchild.trans hmono
    have hn4 := hparts.1.trans ha
    have hm := hparts.2.1.trans ha
    have hB := hparts.2.2.trans hc
    have hconst := h128.trans hmono
    omega
  · exact hsmall.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))

/-- `sec:params` and `prop:time`, paper/paper.tex: the finite greatest-degree scan uses only bounded
linear combinations of the cached occurrence logarithm. -/
theorem degreeSearch_operand_binary_bound (hs : CoreRules x p) (B1 L : ℕ)
    (hn : x.n ≤ L) (hb : 1 ≤ x.beta * (x.n : ℚ) ^ B1) :
    let H := preparationBitBase B1 L
    100 * (p.m * p.k + 2 + x.n * Nat.clog 2 p.Uocc) + x.n + p.k + 256 <
      2 ^ (100 * H) := by
  generalize hHdef : preparationBitBase B1 L = H
  have hH := preparationBitBase_bounds B1 L
  rw [hHdef] at hH
  have he := hs.printing_operand_binary_bounds B1 L hn hb
  simp only [hHdef] at he
  have hnB := (hs.early_operand_binary_bounds B1 L hn hb).1
  simp only [hHdef] at hnB
  have hk : p.k ≤ 2 ^ H := he.2.2.2.2.1
  have hell : Nat.clog 2 p.Uocc ≤ 2 ^ H := he.2.2.2.2.2.2.2.2.1.trans Nat.lt_two_pow_self.le
  have hmk : p.m * p.k ≤ (2 ^ H) ^ 2 := by
    have hm : p.m ≤ 2 ^ H := by
      rw [hs.m_eq]
      exact (by norm_num : 4 ≤ 2 ^ 2).trans (Nat.pow_le_pow_right (by norm_num) (by omega))
    simpa only [pow_two] using Nat.mul_le_mul hm hk
  have hnl : x.n * Nat.clog 2 p.Uocc ≤ (2 ^ H) ^ 2 := by
    simpa only [pow_two] using Nat.mul_le_mul hnB hell
  have hp : 1 ≤ (2 : ℕ) ^ H := Nat.one_le_two_pow
  have hp2 : 2 ^ H ≤ ((2 : ℕ) ^ H) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hp1024 : 1024 ≤ (2 : ℕ) ^ H := (by norm_num : 1024 ≤ 2 ^ 10).trans
    (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hcoef : 1024 * ((2 : ℕ) ^ H) ^ 2 ≤ ((2 : ℕ) ^ H) ^ 3 := by
    calc
      _ ≤ 2 ^ H * ((2 : ℕ) ^ H) ^ 2 := Nat.mul_le_mul_right _ hp1024
      _ = _ := by ring
  have hsmall : 100 * (p.m * p.k + 2 + x.n * Nat.clog 2 p.Uocc) + x.n + p.k + 256 <
      ((2 : ℕ) ^ H) ^ 3 := by
    nlinarith only [hmk, hnl, hnB, hk, hp, hp2, hcoef]
  have heq : ((2 : ℕ) ^ H) ^ 3 = 2 ^ (3 * H) := by
    rw [← pow_mul]
    exact congrArg (fun e : ℕ => 2 ^ e) (by omega)
  rw [heq] at hsmall
  exact hsmall.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))

/-- `sec:params` and `prop:time`, paper/paper.tex: the coefficient-height computation fits the common
cubic bit width while its matrix and sample sizes remain binary words. -/
theorem coefficientBits_operand_binary_bound (hs : CoreRules x p) (B1 L : ℕ)
    (hn : x.n ≤ L) (hb : 1 ≤ x.beta * (x.n : ℚ) ^ B1) :
    let H := preparationBitBase B1 L
    2 * p.N * p.N * p.Q + p.S + p.m * p.k +
      2 * p.m * Nat.clog 2 (p.N * p.N * p.Q) + 2 * p.m + 32 < 2 ^ (100 * H) := by
  generalize hHdef : preparationBitBase B1 L = H
  have hH := preparationBitBase_bounds B1 L
  rw [hHdef] at hH
  have he := hs.printing_operand_binary_bounds B1 L hn hb
  simp only [hHdef] at he
  have hk : p.k ≤ 2 ^ H := he.2.2.2.2.1
  have hS : p.S ≤ 2 ^ H := he.2.2.2.2.2.1
  have hNQ : p.N * p.N * p.Q ≤ 2 ^ H := he.2.2.2.2.2.2.2.1
  have hell : Nat.clog 2 (p.N * p.N * p.Q) ≤ 2 ^ H :=
    he.2.2.2.2.2.2.2.2.2.trans Nat.lt_two_pow_self.le
  rw [hs.m_eq]
  have hp : 1 ≤ (2 : ℕ) ^ H := Nat.one_le_two_pow
  have hsmall : 2 * p.N * p.N * p.Q + p.S + 4 * p.k +
      2 * 4 * Nat.clog 2 (p.N * p.N * p.Q) + 2 * 4 + 32 < 2 ^ (H + 6) := by
    rw [pow_add]
    norm_num
    nlinarith only [hk, hS, hNQ, hell, hp]
  exact hsmall.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))

/-- `sec:params` and `prop:time`, paper/paper.tex: the integer coefficient exponent fits the common
cubic height as a value, hence pays the lifted-search width guard. -/
theorem coefficientExponent_height_bound (hs : CoreRules x p) (B1 L : ℕ)
    (hn : x.n ≤ L) (hb : 1 ≤ x.beta * (x.n : ℚ) ^ B1) :
    let H := preparationBitBase B1 L
    p.BN ≤ H ∧ 3 * (p.BN - 1) + 4 < 100 * H := by
  generalize hHdef : preparationBitBase B1 L = H
  have hH : 1000 ≤ H := by rw [← hHdef]; exact (preparationBitBase_bounds B1 L).1
  have hpow : x.n ^ 2 ≤ (L + 1) ^ 3 :=
    (Nat.pow_le_pow_left (hn.trans (Nat.le_succ L)) 2).trans
      (Nat.pow_le_pow_right (Nat.succ_pos L) (by omega))
  have hBN : p.BN ≤ H := by
    calc
      p.BN ≤ (32 * B1 + 2200) * x.n ^ 2 := hs.BN_preparation_bound B1 hb
      _ ≤ (32 * B1 + 2200) * (L + 1) ^ 3 := Nat.mul_le_mul_left _ hpow
      _ ≤ H := by rw [← hHdef]; unfold preparationBitBase; omega
  exact ⟨hBN, by omega⟩

/-- `sec:params` and `prop:time`, paper/paper.tex: all operands of the exact lifted-mask degree
comparison fit the same cubic binary width for every scanned prime. -/
theorem primeBudget_operand_binary_bound (hs : CoreRules x p) (B1 L : ℕ)
    (hn : x.n ≤ L) (hb : 1 ≤ x.beta * (x.n : ℚ) ^ B1) :
    let H := preparationBitBase B1 L
    StagePrep.primeDegreeMaximum p.BN x.n p.Jmax p.m p.Xmax + 2 * (p.BN + 1) +
      (2 * p.Jmax + 2) + x.n + 4 * p.m + 256 < 2 ^ (100 * H) := by
  generalize hHdef : preparationBitBase B1 L = H
  have hH := preparationBitBase_bounds B1 L
  rw [hHdef] at hH
  have he := hs.printing_operand_binary_bounds B1 L hn hb
  simp only [hHdef] at he
  have hscalar := hs.early_preparation_bounds B1 hb
  have hV := hs.preparationEnvelope_binary_height B1 L hn
  rw [hHdef] at hV
  have hBN : p.BN ≤ 2 ^ H := he.2.2.2.2.2.2.1
  have hJ : p.Jmax ≤ 2 ^ H := he.2.2.2.1
  have hX : p.Xmax ≤ 2 ^ H := hscalar.Xmax.trans hV
  have hnB := (hs.early_operand_binary_bounds B1 L hn hb).1
  simp only [hHdef] at hnB
  have hZ : 1024 ≤ (2 : ℕ) ^ H := (by norm_num : 1024 ≤ 2 ^ 10).trans
    (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hBN2 : 2 * (p.BN + 1) - 1 ≤ 4 * 2 ^ H := by omega
  have hJ2 : 2 * p.Jmax + 2 ≤ 4 * 2 ^ H := by omega
  have hn1 : x.n - 1 ≤ 2 ^ H := (Nat.sub_le _ _).trans hnB
  have hprod : (2 * (p.BN + 1) - 1) * (2 * p.Jmax + 2) * (x.n - 1) ≤
      16 * ((2 : ℕ) ^ H) ^ 3 := by
    calc
      _ ≤ (4 * 2 ^ H) * (4 * 2 ^ H) * 2 ^ H := Nat.mul_le_mul (Nat.mul_le_mul hBN2 hJ2) hn1
      _ = _ := by ring
  have hZ3 : 2 ^ H ≤ ((2 : ℕ) ^ H) ^ 3 := Nat.le_self_pow (by norm_num) _
  have hsmall : StagePrep.primeDegreeMaximum p.BN x.n p.Jmax p.m p.Xmax + 2 * (p.BN + 1) +
      (2 * p.Jmax + 2) + x.n + 4 * p.m + 256 < 64 * ((2 : ℕ) ^ H) ^ 3 := by
    unfold StagePrep.primeDegreeMaximum
    rw [hs.m_eq]
    nlinarith only [hBN, hJ, hX, hnB, hZ, hZ3, hprod]
  have heq : 64 * ((2 : ℕ) ^ H) ^ 3 = 2 ^ (3 * H + 6) := by
    rw [show 3 * H + 6 = H * 3 + 6 by omega, pow_add, pow_mul]
    norm_num
    ring
  rw [heq] at hsmall
  exact hsmall.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))

/-- `sec:params` and `prop:time`, paper/paper.tex: the prime census and scalar-window cubic search
fit the common binary width before any rate-chain acceptance. -/
theorem primeWindows_operand_binary_bounds (_hs : CoreRules x p) (B1 L P D : ℕ)
    (hn : x.n ≤ L) (hP : P ≤ x.n) (hD : D ≤ (x.n + 1) ^ 2) :
    let H := preparationBitBase B1 L
    2 * (P + 1) * (P + 1) + 8 < 2 ^ (100 * H) ∧
      2 * (D * (D * D)) + 2 * D + 8 < 2 ^ (100 * H) := by
  generalize hHdef : preparationBitBase B1 L = H
  have hH := preparationBitBase_bounds B1 L
  rw [hHdef] at hH
  have hquad : (L + 1) ^ 2 ≤ H := by
    rw [← hHdef]
    unfold preparationBitBase
    omega
  have hPB : P ≤ 2 ^ H := (hP.trans (hn.trans hH.2.1)).trans Nat.lt_two_pow_self.le
  have hDB : D ≤ 2 ^ H := (hD.trans ((Nat.pow_le_pow_left (Nat.add_le_add_right hn 1) 2).trans hquad)).trans
    Nat.lt_two_pow_self.le
  have hZ : 16 ≤ (2 : ℕ) ^ H := (by norm_num : 16 ≤ 2 ^ 4).trans
    (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hZ2 : 2 ^ H ≤ ((2 : ℕ) ^ H) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hZ3 : 2 ^ H ≤ ((2 : ℕ) ^ H) ^ 3 := Nat.le_self_pow (by norm_num) _
  have hP1 : P + 1 ≤ 2 * 2 ^ H := by omega
  have hP2 : (P + 1) * (P + 1) ≤ 4 * ((2 : ℕ) ^ H) ^ 2 := by
    calc
      _ ≤ (2 * 2 ^ H) * (2 * 2 ^ H) := Nat.mul_le_mul hP1 hP1
      _ = _ := by ring
  have hD3 : D * (D * D) ≤ ((2 : ℕ) ^ H) ^ 3 := by
    calc
      _ ≤ 2 ^ H * (2 ^ H * 2 ^ H) := Nat.mul_le_mul hDB (Nat.mul_le_mul hDB hDB)
      _ = _ := by ring
  have hfirst : 2 * (P + 1) * (P + 1) + 8 < 16 * ((2 : ℕ) ^ H) ^ 2 := by
    nlinarith only [hP2, hZ, hZ2]
  have hsecond : 2 * (D * (D * D)) + 2 * D + 8 < 16 * ((2 : ℕ) ^ H) ^ 3 := by
    nlinarith only [hD3, hDB, hZ, hZ3]
  have heq2 : 16 * ((2 : ℕ) ^ H) ^ 2 = 2 ^ (2 * H + 4) := by
    rw [show 2 * H + 4 = H * 2 + 4 by omega, pow_add, pow_mul]
    norm_num
    ring
  have heq3 : 16 * ((2 : ℕ) ^ H) ^ 3 = 2 ^ (3 * H + 4) := by
    rw [show 3 * H + 4 = H * 3 + 4 by omega, pow_add, pow_mul]
    norm_num
    ring
  rw [heq2] at hfirst
  rw [heq3] at hsecond
  exact ⟨hfirst.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega)),
    hsecond.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))⟩

/-- `imp:chain` and `prop:time`, paper/paper.tex: the rate-chain input fields have one common strict
binary height, and its sixfold arithmetic width fits the same scale. -/
theorem rateChain_operand_binary_bounds (hs : CoreRules x p) (B1 L h : ℕ)
    (hn : x.n ≤ L) (hb : 1 ≤ x.beta * (x.n : ℚ) ^ B1) (hh : h ≤ x.n) :
    let H := preparationBitBase B1 L
    128 * p.U < 2 ^ (H + 1) ∧ h < 2 ^ (H + 1) ∧ p.T < 2 ^ (H + 1) ∧
      p.Jmax < 2 ^ (H + 1) ∧ 6 * (H + 1) + 40 ≤ 100 * H := by
  generalize hHdef : preparationBitBase B1 L = H
  have hH := preparationBitBase_bounds B1 L
  rw [hHdef] at hH
  have hV := hs.preparationEnvelope_binary_height B1 L hn
  rw [hHdef] at hV
  have hscalar := hs.early_preparation_bounds B1 hb
  have he := hs.printing_operand_binary_bounds B1 L hn hb
  simp only [hHdef] at he
  have hell : 128 * p.U ≤ 2 ^ H := hscalar.ell0_numerator.trans hV
  have hT : p.T ≤ 2 ^ H := hscalar.T.trans hV
  have hJ : p.Jmax ≤ 2 ^ H := he.2.2.2.1
  have hhB : h ≤ 2 ^ H := (hh.trans (hn.trans hH.2.1)).trans Nat.lt_two_pow_self.le
  have hpow : (2 : ℕ) ^ H < 2 ^ (H + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  exact ⟨hell.trans_lt hpow, hhB.trans_lt hpow, hT.trans_lt hpow, hJ.trans_lt hpow, by omega⟩

end NearQuarticWires.Cells.CoreRules
