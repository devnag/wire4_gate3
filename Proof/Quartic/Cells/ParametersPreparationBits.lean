import Proof.Quartic.Cells.ParametersEarlyPreparation
import Proof.Quartic.StagePrep.UProgram
import Proof.Quartic.StagePrep.SampleArithmetic
import Proof.Quartic.StagePrep.ConcentrationRule

set_option autoImplicit false

namespace NearQuarticWires.Cells.ParameterArithmetic

/-- `sec:params` and `prop:time`, paper/paper.tex: a common binary-height scale for the scalar products,
sample comparison and lifted-prime powers computed before final selection. -/
def preparationBitBase (B1 L : ℕ) : ℕ :=
  preparationCoefficient B1 + (B1 + 12) * (L + 1) + 100 * (L + 1) ^ 2 +
    (32 * B1 + 2200) * (L + 1) ^ 3 + L + 1000

/-- `prop:time`, paper/paper.tex: the common
binary-height scale is cubic in the original serialized input length. -/
theorem preparationBitBase_cubic (B1 L : ℕ) :
    preparationBitBase B1 L ≤
      (preparationCoefficient B1 + 33 * B1 + 4000) * (L + 1) ^ 3 := by
  unfold preparationBitBase
  ring_nf
  omega

/-- `prop:time`, paper/paper.tex: one fixed additive
width constant absorbs the cubic binary scale in the physical
fourth-power register width for every serialized input length. -/
theorem preparationBitBase_width (B1 : ℕ) :
    ∃ K : ℕ, 0 < K ∧ ∀ L : ℕ, 100 * preparationBitBase B1 L ≤ (L + K) ^ 4 := by
  let C := 100 * (preparationCoefficient B1 + 33 * B1 + 4000)
  refine ⟨C + 2, by omega, fun L => ?_⟩
  calc
    100 * preparationBitBase B1 L ≤ C * (L + 1) ^ 3 := by
      simpa only [C, Nat.mul_assoc] using Nat.mul_le_mul_left 100 (preparationBitBase_cubic B1 L)
    _ ≤ (L + (C + 2)) * (L + (C + 2)) ^ 3 :=
      Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left (by omega) 3)
    _ = (L + (C + 2)) ^ 4 := by ring

/-- `prop:time`, paper/paper.tex: the common
binary-height scale dominates each elementary linear or quadratic
height occurring in the early parameter computations. -/
theorem preparationBitBase_bounds (B1 L : ℕ) :
    1000 ≤ preparationBitBase B1 L ∧
    L ≤ preparationBitBase B1 L ∧
    2 + 4 * L ≤ preparationBitBase B1 L ∧
    16 * L ^ 2 ≤ preparationBitBase B1 L ∧
    preparationCoefficient B1 + (B1 + 12) * (L + 1) ≤ preparationBitBase B1 L ∧
    (32 * B1 + 2200) * L ^ 3 ≤ preparationBitBase B1 L := by
  unfold preparationBitBase
  constructor
  · omega
  constructor
  · omega
  constructor
  · nlinarith only [Nat.zero_le (preparationCoefficient B1), Nat.zero_le B1,
      Nat.zero_le L, Nat.zero_le ((32 * B1 + 2200) * (L + 1) ^ 3),
      Nat.zero_le ((B1 + 12) * (L + 1))]
  constructor
  · nlinarith only [Nat.zero_le (preparationCoefficient B1), Nat.zero_le B1,
      Nat.zero_le L, Nat.zero_le ((32 * B1 + 2200) * (L + 1) ^ 3),
      Nat.zero_le ((B1 + 12) * (L + 1))]
  constructor
  · omega
  · have h := Nat.mul_le_mul_left (32 * B1 + 2200)
      (Nat.pow_le_pow_left (Nat.le_succ L) 3)
    simp only [Nat.succ_eq_add_one] at h
    omega

/-- `prop:time`, paper/paper.tex: three
nonnegative operands of a common binary height have a uniformly
bounded affine sum at the next two height positions. -/
theorem three_binary_sum_bound (a b c H : ℕ)
    (ha : a ≤ 2 ^ H) (hb : b ≤ 2 ^ H) (hc : c ≤ 2 ^ H) :
    a + b + c < 2 ^ (H + 2) := by
  have hp : 0 < (2 : ℕ) ^ H := Nat.pow_pos (by norm_num)
  rw [pow_add]
  norm_num
  omega

end NearQuarticWires.Cells.ParameterArithmetic

namespace NearQuarticWires.Cells.CoreRules

open ParameterArithmetic

variable {x : ParameterInput} {p : Parameters}

/-- `sec:params` and `prop:time`, paper/paper.tex: the literal integer root loop is bounded by the square
of the public population scale before any later acceptance test. -/
theorem uRootArgument_le_U_sq (hs : CoreRules x p) (num den : ℕ)
    (hnum : x.beta.num = num) (hden : x.beta.den = den)
    (hu : 0 < num) (hd : 0 < den) :
    StagePrep.uRootArgument x.n p.r x.W num den ≤ p.U ^ 2 := by
  unfold StagePrep.uRootArgument
  rw [← StagePrep.u_ratio_encoding x.n p.r x.W num den x.beta hnum hden hs.n_pos hu hd]
  apply Nat.ceil_le.mpr
  have h := ((hs.U_le_iff p.U).mp le_rfl).2
  exact_mod_cast h

/-- `sec:params` and `prop:time`, paper/paper.tex: the public scalar envelope has a common cubic
binary height in the original input length, including rejected calls. -/
theorem preparationEnvelope_binary_height (_hs : CoreRules x p) (B1 L : ℕ)
    (hn : x.n ≤ L) : preparationEnvelope B1 x.n ≤ 2 ^ preparationBitBase B1 L := by
  have he := preparation_envelope_binary_bound B1 x.n
  apply he.trans
  apply Nat.pow_le_pow_right (by norm_num)
  exact (Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.add_le_add_right hn 1)) _).trans
    (preparationBitBase_bounds B1 L).2.2.2.2.1

/-- `sec:params` and `prop:time`, paper/paper.tex: basic integer operands and the matrix side fit the
common binary height under the early public identities alone. -/
theorem early_operand_binary_bounds (hs : CoreRules x p) (B1 L : ℕ)
    (hn : x.n ≤ L) (hb : 1 ≤ x.beta * (x.n : ℚ) ^ B1) :
    let H := preparationBitBase B1 L
    x.n ≤ 2 ^ H ∧ p.r ≤ 2 ^ H ∧ x.W ≤ 2 ^ H ∧ p.N ≤ 2 ^ H ∧
      p.U ≤ 2 ^ H ∧ p.omega1 ≤ 2 ^ H ∧ p.omega2 ≤ 2 ^ H ∧
      16 * p.MF ≤ 2 ^ H := by
  let H := preparationBitBase B1 L
  have hH := preparationBitBase_bounds B1 L
  have hnH : x.n ≤ H := hn.trans hH.2.1
  have hnB : x.n ≤ 2 ^ H := hnH.trans Nat.lt_two_pow_self.le
  have hrB : p.r ≤ 2 ^ H := (by have := hs.r_bound; omega : p.r ≤ x.n).trans hnB
  have hW : x.W ≤ 2 ^ H := by
    calc
      x.W ≤ 2 * x.n ^ 4 := hs.input_valid.2.2.2.1
      _ ≤ 2 ^ (2 + 4 * x.n) := polynomial_value_binary_bound 2 x.n 4
      _ ≤ 2 ^ H := Nat.pow_le_pow_right (by norm_num)
        ((Nat.add_le_add_left (Nat.mul_le_mul_left 4 hn) 2).trans hH.2.2.1)
  have hN : p.N ≤ 2 ^ H := by
    rw [hs.N_eq]
    apply Nat.pow_le_pow_right (by norm_num)
    have hk := hs.k_preparation_bound
    have hn2 := Nat.mul_le_mul_left 16 (Nat.pow_le_pow_left hn 2)
    exact (Nat.div_le_self _ _).trans ((hk.trans hn2).trans hH.2.2.2.1)
  have hscalar := hs.early_preparation_bounds B1 hb
  have hV := hs.preparationEnvelope_binary_height B1 L hn
  exact ⟨hnB, hrB, hW, hN, hscalar.U.trans hV, hscalar.omega1.trans hV,
    hscalar.omega2.trans hV, hscalar.eta_divisor.trans hV⟩

/-- `sec:params` and `prop:time`, paper/paper.tex: canonical numerator and denominator reduction keeps
the sampler tolerance within twice the common binary height. -/
theorem eta_operand_binary_bounds (hs : CoreRules x p) (B1 L : ℕ)
    (hn : x.n ≤ L) (hb : 1 ≤ x.beta * (x.n : ℚ) ^ B1)
    (hnum : x.beta.num.natAbs ≤ 2 ^ L) (hden : x.beta.den ≤ 2 ^ L) :
    let H := preparationBitBase B1 L
    p.eta.num.natAbs ≤ 2 ^ (2 * H) ∧ p.eta.den ≤ 2 ^ (2 * H) := by
  let H := preparationBitBase B1 L
  have hLH : L ≤ H := (preparationBitBase_bounds B1 L).2.1
  have hη : p.eta = x.beta / ((16 * p.MF : ℕ) : ℚ) := by
    rw [hs.eta_eq]
    push_cast
    rfl
  have hbounds := div_natCast_size_bounds x.beta (16 * p.MF)
    (Nat.mul_pos (by norm_num) hs.MF_pos)
  have hMF := (hs.early_operand_binary_bounds B1 L hn hb).2.2.2.2.2.2.2
  rw [hη]
  constructor
  · exact hbounds.1.trans (hnum.trans (Nat.pow_le_pow_right (by norm_num) (by omega)))
  · calc
      (x.beta / ((16 * p.MF : ℕ) : ℚ)).den ≤ x.beta.den * (16 * p.MF) := hbounds.2
      _ ≤ 2 ^ L * 2 ^ H := Nat.mul_le_mul hden hMF
      _ = 2 ^ (L + H) := by rw [pow_add]
      _ ≤ 2 ^ (2 * H) := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- `sec:params` and `prop:time`, paper/paper.tex: the actual integer numerator, denominator and root
search guard all fit a cubic bit width before later acceptance tests. -/
theorem uProgram_operand_binary_bounds (hs : CoreRules x p) (B1 L num den : ℕ)
    (hn : x.n ≤ L) (hb : 1 ≤ x.beta * (x.n : ℚ) ^ B1)
    (hnum : x.beta.num = num) (hden : x.beta.den = den)
    (hu : 0 < num) (hd : 0 < den)
    (hnumBits : num ≤ 2 ^ L) (hdenBits : den ≤ 2 ^ L) :
    let H := preparationBitBase B1 L
    StagePrep.uNumerator p.r x.W den + 2 * StagePrep.uDenominator x.n num + 4 <
        2 ^ (100 * H) ∧
      StagePrep.uRootArgument x.n p.r x.W num den *
        StagePrep.uRootArgument x.n p.r x.W num den +
        StagePrep.uRootArgument x.n p.r x.W num den + 3 < 2 ^ (100 * H) := by
  generalize hHdef : preparationBitBase B1 L = H
  have hH := preparationBitBase_bounds B1 L
  rw [hHdef] at hH
  have hLH : L ≤ H := hH.2.1
  have he := hs.early_operand_binary_bounds B1 L hn hb
  simp only [hHdef] at he
  have hnB : x.n ≤ 2 ^ H := he.1
  have hrB : p.r ≤ 2 ^ H := he.2.1
  have hWB : x.W ≤ 2 ^ H := he.2.2.1
  have hUB : p.U ≤ 2 ^ H := he.2.2.2.2.1
  have huB : num ≤ 2 ^ H := hnumBits.trans (Nat.pow_le_pow_right (by norm_num) hLH)
  have hdB : den ≤ 2 ^ H := hdenBits.trans (Nat.pow_le_pow_right (by norm_num) hLH)
  have hcB : 9216 ≤ 2 ^ H := by
    calc
      9216 ≤ 2 ^ 14 := by norm_num
      _ ≤ 2 ^ H := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hA : StagePrep.uNumerator p.r x.W den ≤ 2 ^ (8 * H) := by
    calc
      StagePrep.uNumerator p.r x.W den ≤
          2 ^ H * (2 ^ H * 2 ^ H * 2 ^ H) * (2 ^ H * 2 ^ H) * (2 ^ H * 2 ^ H) := by
        unfold StagePrep.uNumerator
        gcongr
      _ = _ := by simp only [← pow_add]; congr 1; omega
  have hB : 2 * StagePrep.uDenominator x.n num ≤ 2 ^ (6 * H) := by
    have htwo : 2 ≤ 2 ^ H := by
      exact (by norm_num : 2 ≤ 2 ^ 1).trans
        (Nat.pow_le_pow_right (by norm_num) (by omega))
    calc
      2 * StagePrep.uDenominator x.n num ≤
          2 ^ H * ((2 ^ H * 2 ^ H) * (2 ^ H * 2 ^ H * 2 ^ H)) := by
        unfold StagePrep.uDenominator
        gcongr
      _ = _ := by simp only [← pow_add]; congr 1; omega
  have hpow (a : ℕ) (ha : a ≤ 8 * H) : 2 ^ a ≤ 2 ^ (8 * H) :=
    Nat.pow_le_pow_right (by norm_num) ha
  have hfour : 4 ≤ 2 ^ (8 * H) := (by norm_num : 4 ≤ 2 ^ 2).trans (hpow 2 (by omega))
  have hsum := three_binary_sum_bound _ _ _ (8 * H) hA (hB.trans (hpow _ (by omega))) hfour
  have hroot : StagePrep.uRootArgument x.n p.r x.W num den ≤ p.U ^ 2 :=
    hs.uRootArgument_le_U_sq num den hnum hden hu hd
  have hrootB : StagePrep.uRootArgument x.n p.r x.W num den ≤ 2 ^ (2 * H) := by
    calc
      _ ≤ p.U ^ 2 := hroot
      _ ≤ (2 ^ H) ^ 2 := Nat.pow_le_pow_left hUB _
      _ = _ := by rw [← pow_mul, Nat.mul_comm]
  have hrootSq : StagePrep.uRootArgument x.n p.r x.W num den *
      StagePrep.uRootArgument x.n p.r x.W num den ≤ 2 ^ (4 * H) := by
    calc
      _ ≤ 2 ^ (2 * H) * 2 ^ (2 * H) := Nat.mul_le_mul hrootB hrootB
      _ = _ := by rw [← pow_add]; exact congrArg (fun e : ℕ => 2 ^ e) (by omega)
  have hrmono : 2 ^ (2 * H) ≤ 2 ^ (4 * H) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hthree : 3 ≤ 2 ^ (4 * H) := by
    exact (by norm_num : 3 ≤ 2 ^ 2).trans (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hrootsum := three_binary_sum_bound _ _ _ (4 * H) hrootSq (hrootB.trans hrmono) hthree
  exact ⟨hsum.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega)),
    hrootsum.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))⟩

/-- `sec:params` and `prop:time`, paper/paper.tex: the exact eighth-power rational sample comparison
fits a cubic binary width, without enumerating its sample size. -/
theorem sampleProgram_operand_binary_bound (hs : CoreRules x p) (B1 L : ℕ)
    (hn : x.n ≤ L) (hb : 1 ≤ x.beta * (x.n : ℚ) ^ B1)
    (hnum : x.beta.num.natAbs ≤ 2 ^ L) (hden : x.beta.den ≤ 2 ^ L) :
    let H := preparationBitBase B1 L
    16 * (StagePrep.sampleNumerator p.N p.m (p.omega1 * p.omega2) p.eta.den +
      StagePrep.sampleDenominator p.eta.num.natAbs) + 256 < 2 ^ (100 * H) := by
  generalize hHdef : preparationBitBase B1 L = H
  have hH : 1000 ≤ H := by
    rw [← hHdef]
    exact (preparationBitBase_bounds B1 L).1
  have he := hs.early_operand_binary_bounds B1 L hn hb
  simp only [hHdef] at he
  have hN : p.N ≤ 2 ^ H := he.2.2.2.1
  have ho1 : p.omega1 ≤ 2 ^ H := he.2.2.2.2.2.1
  have ho2 : p.omega2 ≤ 2 ^ H := he.2.2.2.2.2.2.1
  have hη := hs.eta_operand_binary_bounds B1 L hn hb hnum hden
  simp only [hHdef] at hη
  have hηd : p.eta.den ≤ (2 ^ H) ^ 2 := by
    rw [← pow_mul, show H * 2 = 2 * H by omega]
    exact hη.2
  have hm : p.m ≤ 2 ^ H := by
    rw [hs.m_eq]
    exact (by norm_num : 4 ≤ 2 ^ 2).trans (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hc (a : ℕ) (ha : a ≤ 1024) : a ≤ 2 ^ H := by
    exact ha.trans ((by norm_num : 1024 ≤ 2 ^ 10).trans
      (Nat.pow_le_pow_right (by norm_num) (by omega)))
  have hA : StagePrep.sampleNumerator p.N p.m (p.omega1 * p.omega2) p.eta.den ≤
      2 ^ (33 * H) := by
    calc
      _ ≤ (2 ^ H * 2 ^ H * 2 ^ H) ^ 4 *
          (2 ^ H * 2 ^ H * 2 ^ H * (2 ^ H * 2 ^ H)) * ((2 ^ H) ^ 2) ^ 8 := by
        unfold StagePrep.sampleNumerator
        gcongr
        · exact hc 1024 le_rfl
        · exact hc 8 (by norm_num)
      _ = (2 ^ H) ^ 33 := by ring
      _ = _ := by rw [← pow_mul]; exact congrArg (fun e : ℕ => 2 ^ e) (by omega)
  have hB : StagePrep.sampleDenominator p.eta.num.natAbs ≤ 2 ^ (16 * H) := by
    calc
      _ ≤ (2 ^ (2 * H)) ^ 8 := Nat.pow_le_pow_left hη.1 _
      _ = _ := by rw [← pow_mul]; exact congrArg (fun e : ℕ => 2 ^ e) (by omega)
  have h16A : 16 * StagePrep.sampleNumerator p.N p.m (p.omega1 * p.omega2) p.eta.den ≤
      2 ^ (34 * H) := by
    calc
      _ ≤ 2 ^ H * 2 ^ (33 * H) := Nat.mul_le_mul (hc 16 (by norm_num)) hA
      _ = _ := by rw [← pow_add]; exact congrArg (fun e : ℕ => 2 ^ e) (by omega)
  have h16B : 16 * StagePrep.sampleDenominator p.eta.num.natAbs ≤ 2 ^ (34 * H) := by
    calc
      _ ≤ 2 ^ H * 2 ^ (16 * H) := Nat.mul_le_mul (hc 16 (by norm_num)) hB
      _ = 2 ^ (17 * H) := by rw [← pow_add]; exact congrArg (fun e : ℕ => 2 ^ e) (by omega)
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h256 : 256 ≤ 2 ^ (34 * H) := by
    exact (by norm_num : 256 ≤ 2 ^ 8).trans
      (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hsum := three_binary_sum_bound _ _ _ (34 * H) h16A h16B h256
  rw [Nat.mul_add]
  exact hsum.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))

/-- `sec:params` and `prop:time`, paper/paper.tex: every power examined in the lifted-prime search
fits a cubic original-input binary width before the prime succeeds. -/
theorem liftProgram_operand_binary_bound (hs : CoreRules x p) (B1 L P j : ℕ)
    (hn : x.n ≤ L) (hb : 1 ≤ x.beta * (x.n : ℚ) ^ B1)
    (hP : P ≤ x.n) (hj : j ≤ 2 * p.BN) :
    P ^ j < 2 ^ (100 * preparationBitBase B1 L) := by
  generalize hHdef : preparationBitBase B1 L = H
  have hH : 1000 ≤ H := by
    rw [← hHdef]
    exact (preparationBitBase_bounds B1 L).1
  have hBN := hs.BN_preparation_bound B1 hb
  have hscale := (preparationBitBase_bounds B1 L).2.2.2.2.2
  rw [hHdef] at hscale
  have hexp : x.n * j ≤ 2 * H := by
    calc
      x.n * j ≤ x.n * (2 * p.BN) := Nat.mul_le_mul_left _ hj
      _ ≤ x.n * (2 * ((32 * B1 + 2200) * x.n ^ 2)) := by gcongr
      _ = 2 * ((32 * B1 + 2200) * x.n ^ 3) := by ring
      _ ≤ 2 * ((32 * B1 + 2200) * L ^ 3) := by gcongr
      _ ≤ 2 * H := Nat.mul_le_mul_left _ hscale
  calc
    P ^ j ≤ (2 ^ x.n) ^ j := Nat.pow_le_pow_left (hP.trans Nat.lt_two_pow_self.le) _
    _ = 2 ^ (x.n * j) := by rw [← pow_mul]
    _ ≤ 2 ^ (2 * H) := Nat.pow_le_pow_right (by norm_num) hexp
    _ < _ := Nat.pow_lt_pow_right (by norm_num) (by omega)

/-- `sec:params` and `prop:time`, paper/paper.tex: the literal finite concentration search bound has
quadratic value in the original input length. -/
theorem concentration_search_preparation_bound (hs : CoreRules x p) (L : ℕ)
    (hn : x.n ≤ L) (hden : x.beta.den ≤ 2 ^ L) :
    NearCubicGates.Close.Counter.TBound (StagePrep.concentrationExponent p.m p.k)
      p.Jmax x.beta ≤ 66 * (L + 1) ^ 2 := by
  have hJ : p.Jmax ≤ x.n + 1 := by
    rw [hs.Jmax_eq]
    exact Nat.add_le_add_right (hs.mu_le_lambda.trans hs.lambda_le_n) _
  have hJB : p.Jmax ≤ 2 ^ (x.n + 1) := hJ.trans Nat.lt_two_pow_self.le
  have hprod : 4 * p.Jmax * x.beta.den ≤ 2 ^ (2 + (x.n + 1) + L) := by
    calc
      4 * p.Jmax * x.beta.den ≤ 2 ^ 2 * 2 ^ (x.n + 1) * 2 ^ L :=
        Nat.mul_le_mul (Nat.mul_le_mul (by norm_num) hJB) hden
      _ = _ := by rw [← pow_add, ← pow_add]
  have hlog : Nat.log 2 (4 * p.Jmax * x.beta.den) ≤ 2 + (x.n + 1) + L := by
    exact (Nat.log_mono_right hprod).trans (by rw [Nat.log_pow (by norm_num)])
  have hk := hs.k_preparation_bound
  have hn2 := Nat.pow_le_pow_left hn 2
  unfold NearCubicGates.Close.Counter.TBound StagePrep.concentrationExponent
  rw [hs.m_eq]
  nlinarith only [hlog, hk, hn, hn2, Nat.zero_le L]

/-- `sec:params` and `prop:time`, paper/paper.tex: every exponential operand and width guard used by
the physical concentration search fits the common cubic binary width. -/
theorem concentrationProgram_operand_binary_bounds (hs : CoreRules x p) (B1 L : ℕ)
    (hn : x.n ≤ L) (hnum : x.beta.num.natAbs ≤ 2 ^ L)
    (hden : x.beta.den ≤ 2 ^ L) :
    let H := preparationBitBase B1 L
    let A := StagePrep.concentrationExponent p.m p.k
    let T := NearCubicGates.Close.Counter.TBound A p.Jmax x.beta
    A < 100 * H ∧ 4 * p.Jmax * 2 ^ A * x.beta.den < 2 ^ (100 * H) ∧
      2 ^ T * x.beta.num.natAbs < 2 ^ (100 * H) ∧ T + 2 < 100 * H := by
  generalize hHdef : preparationBitBase B1 L = H
  let A := StagePrep.concentrationExponent p.m p.k
  let T := NearCubicGates.Close.Counter.TBound A p.Jmax x.beta
  have hH := preparationBitBase_bounds B1 L
  rw [hHdef] at hH
  have hLH : L ≤ H := hH.2.1
  have hquad : 100 * (L + 1) ^ 2 ≤ H := by
    rw [← hHdef]
    unfold preparationBitBase
    omega
  have hk := hs.k_preparation_bound
  have hn2 := Nat.pow_le_pow_left hn 2
  have hA : A ≤ H := by
    dsimp [A, StagePrep.concentrationExponent]
    rw [hs.m_eq]
    nlinarith only [hk, hn2, hquad, Nat.zero_le L]
  have hT : T ≤ H := (hs.concentration_search_preparation_bound L hn hden).trans
    (by nlinarith only [hquad, Nat.zero_le ((L + 1) ^ 2)])
  have hJ : p.Jmax ≤ 2 ^ H := by
    have hm := hs.mu_le_lambda.trans hs.lambda_le_n
    have hJh : p.Jmax ≤ H := by rw [hs.Jmax_eq]; omega
    exact hJh.trans Nat.lt_two_pow_self.le
  have hfour : 4 ≤ 2 ^ H := (by norm_num : 4 ≤ 2 ^ 2).trans
    (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hnumH : x.beta.num.natAbs ≤ 2 ^ H :=
    hnum.trans (Nat.pow_le_pow_right (by norm_num) hLH)
  have hdenH : x.beta.den ≤ 2 ^ H :=
    hden.trans (Nat.pow_le_pow_right (by norm_num) hLH)
  have hleft : 4 * p.Jmax * 2 ^ A * x.beta.den ≤ 2 ^ (4 * H) := by
    calc
      _ ≤ 2 ^ H * 2 ^ H * 2 ^ H * 2 ^ H :=
        Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hfour hJ)
          (Nat.pow_le_pow_right (by norm_num) hA)) hdenH
      _ = (2 ^ H) ^ 4 := by ring
      _ = _ := by rw [← pow_mul]; exact congrArg (fun e : ℕ => 2 ^ e) (by omega)
  have hright : 2 ^ T * x.beta.num.natAbs ≤ 2 ^ (2 * H) := by
    calc
      _ ≤ 2 ^ H * 2 ^ H := Nat.mul_le_mul
        (Nat.pow_le_pow_right (by norm_num) hT) hnumH
      _ = _ := by rw [← pow_add]; exact congrArg (fun e : ℕ => 2 ^ e) (by omega)
  refine ⟨by omega, hleft.trans_lt (Nat.pow_lt_pow_right (by norm_num) (by omega)),
    hright.trans_lt (Nat.pow_lt_pow_right (by norm_num) (by omega)), ?_⟩
  change T + 2 < 100 * H
  omega

end NearQuarticWires.Cells.CoreRules
