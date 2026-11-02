import Proof.Quartic.Cells.ParametersPreparationTailBits
import Proof.Quartic.StagePrep.ConcentrationProgram

set_option autoImplicit false

namespace NearQuarticWires.Cells.CoreRules

open ParameterArithmetic

variable {x : ParameterInput} {p : Parameters}

/-- `sec:params` and `prop:time`, paper/paper.tex: the actual linear root search has polynomially
bounded loop count, even if a later acceptance test fails. -/
theorem uRootArgument_preparation_bound (hs : CoreRules x p) (B1 num den : ℕ)
    (hb : 1 ≤ x.beta * (x.n : ℚ) ^ B1)
    (hnum : x.beta.num = num) (hden : x.beta.den = den)
    (hu : 0 < num) (hd : 0 < den) :
    StagePrep.uRootArgument x.n p.r x.W num den ≤
      (B1 + 20000) ^ 2 * x.n ^ (2 * B1 + 8) := by
  calc
    _ ≤ p.U ^ 2 := hs.uRootArgument_le_U_sq num den hnum hden hu hd
    _ ≤ ((B1 + 20000) * x.n ^ (B1 + 4)) ^ 2 :=
      Nat.pow_le_pow_left (hs.U_preparation_bound B1 hb) _
    _ = _ := by rw [mul_pow, ← pow_mul]; congr 2; omega

/-- `sec:params` and `prop:time`, paper/paper.tex: the physical incidence-bound program's charged
root-loop time is polynomial in the admitted arity. -/
theorem uProgram_budget_preparation_bound (hs : CoreRules x p) (B1 num den : ℕ)
    (hb : 1 ≤ x.beta * (x.n : ℚ) ^ B1)
    (hnum : x.beta.num = num) (hden : x.beta.den = den)
    (hu : 0 < num) (hd : 0 < den) :
    20 * StagePrep.uRootArgument x.n p.r x.W num den + 20000 ≤
      (20 * (B1 + 20000) ^ 2 + 20000) * (x.n + 1) ^ (2 * B1 + 8) := by
  have hr := hs.uRootArgument_preparation_bound B1 num den hb hnum hden hu hd
  have hpow := Nat.pow_le_pow_left (Nat.le_succ x.n) (2 * B1 + 8)
  have hone : 1 ≤ (x.n + 1) ^ (2 * B1 + 8) := Nat.pow_pos (Nat.succ_pos x.n)
  calc
    _ ≤ 20 * ((B1 + 20000) ^ 2 * x.n ^ (2 * B1 + 8)) + 20000 := by omega
    _ ≤ 20 * ((B1 + 20000) ^ 2 * (x.n + 1) ^ (2 * B1 + 8)) +
        20000 * (x.n + 1) ^ (2 * B1 + 8) :=
      Nat.add_le_add (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hpow))
        (by nlinarith only [hone])
    _ = _ := by ring

/-- `sec:params` and `prop:time`, paper/paper.tex: the logarithmic sample computation has cubic
loop count, although its integer quotient can have exponential value. -/
theorem sampleArgument_clog_preparation_bound (hs : CoreRules x p) (B1 L : ℕ)
    (hn : x.n ≤ L) (hb : 1 ≤ x.beta * (x.n : ℚ) ^ B1)
    (hnum : x.beta.num.natAbs ≤ 2 ^ L) (hden : x.beta.den ≤ 2 ^ L) :
    Nat.clog 2 (StagePrep.sampleArgument p.N p.m (p.omega1 * p.omega2)
      p.eta.num.natAbs p.eta.den) ≤ 100 * preparationBitBase B1 L := by
  have hp := hs.sampleProgram_operand_binary_bound B1 L hn hb hnum hden
  have hu : 0 < p.eta.num.natAbs := Int.natAbs_pos.mpr (Rat.num_pos.mpr hs.eta_pos).ne'
  have hd : 0 < StagePrep.sampleDenominator p.eta.num.natAbs := Nat.pow_pos hu
  have hceil : StagePrep.sampleArgument p.N p.m (p.omega1 * p.omega2)
      p.eta.num.natAbs p.eta.den ≤
      StagePrep.sampleNumerator p.N p.m (p.omega1 * p.omega2) p.eta.den +
        StagePrep.sampleDenominator p.eta.num.natAbs := by
    unfold StagePrep.sampleArgument
    rw [NearCubicGates.Close.Dispatch.ceil_div_nat _ _ hd]
    exact (Nat.div_le_self _ _).trans (Nat.sub_le _ _)
  apply (Nat.clog_le_iff_le_pow (by norm_num)).mpr
  exact hceil.trans (by omega)

/-- `sec:params` and `prop:time`, paper/paper.tex: every iteration of the exact finite concentration
search is paid within a quartic polynomial of the original input length. -/
theorem concentrationCost_preparation_bound (hs : CoreRules x p) (L : ℕ)
    (hn : x.n ≤ L) (hden : x.beta.den ≤ 2 ^ L) :
    StagePrep.concentrationCost p.m p.k p.Jmax x.beta ≤ 100000 * (L + 1) ^ 4 := by
  let a := StagePrep.concentrationExponent p.m p.k
  let t := NearCubicGates.Close.Counter.TBound a p.Jmax x.beta
  have ht : t ≤ 66 * (L + 1) ^ 2 := hs.concentration_search_preparation_bound L hn hden
  have hk := hs.k_preparation_bound
  have hn2 := Nat.pow_le_pow_left hn 2
  have ha : a ≤ 100 * (L + 1) ^ 2 := by
    dsimp [a, StagePrep.concentrationExponent]
    rw [hs.m_eq]
    nlinarith only [hk, hn2, Nat.zero_le L]
  have hp : 1 ≤ (L + 1) ^ 2 := Nat.pow_pos (Nat.succ_pos L)
  change 5 * a + 440 + 10 * t + (t + 3) * (5 * t + 60) ≤ _
  calc
    _ ≤ 5 * (100 * (L + 1) ^ 2) + 440 + 10 * (66 * (L + 1) ^ 2) +
        (66 * (L + 1) ^ 2 + 3) * (5 * (66 * (L + 1) ^ 2) + 60) := by gcongr
    _ ≤ _ := by nlinarith only [hp]

end NearQuarticWires.Cells.CoreRules
