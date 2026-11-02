import Proof.Quartic.Cells.ParametersExecutionWidths

set_option autoImplicit false

namespace NearQuarticWires.Cells.CoreRules

open ParameterArithmetic

variable {x : ParameterInput} {p : Parameters}

/-- `sec:params` and `prop:time`, paper/paper.tex: all arithmetic guards through the last possible
failing search follow from the public rules and the generic scanned
prime and window bounds, independently of the final chain success. -/
theorem attempt_widths (hs : CoreRules x p) (B1 L num den w1 w2 : ℕ)
    (hn : x.n ≤ L) (hb : 1 ≤ x.beta * (x.n : ℚ) ^ B1)
    (hnum : x.beta.num = num) (hden : x.beta.den = den)
    (hu : 0 < num) (hd : 0 < den)
    (hnumBits : num ≤ 2 ^ L) (hdenBits : den ≤ 2 ^ L)
    (hw1 : w1 ≤ 2 ^ L) (hw2 : w2 ≤ 2 ^ L)
    (hPP : p.P ≤ x.n) (hD : p.Dprime ≤ (x.n + 1) ^ 2) (hh : p.h ≤ x.n)
    (C : NearCubicGates.Close.Dispatch.Ctx)
    (hwidth : 100 * preparationBitBase B1 L ≤ C.Wd) :
    StagePrep.AttemptWidths C x p num den w1 w2 (preparationBitBase B1 L + 1) := by
  generalize hHdef : preparationBitBase B1 L = H at *
  have hH := preparationBitBase_bounds B1 L
  rw [hHdef] at hH
  have hp : 2 ^ (100 * H) ≤ 2 ^ C.Wd := Nat.pow_le_pow_right (by norm_num) hwidth
  have hprinting := hs.printingSizes_operand_binary_bound B1 L hn hb
  have hdegree := hs.degreeSearch_operand_binary_bound B1 L hn hb
  have hcoeff := hs.coefficientBits_operand_binary_bound B1 L hn hb
  have hlift := hs.coefficientExponent_height_bound B1 L hn hb
  have hprime := hs.primeBudget_operand_binary_bound B1 L hn hb
  have hwindows := hs.primeWindows_operand_binary_bounds B1 L p.P p.Dprime hn hPP hD
  have hchain := hs.rateChain_operand_binary_bounds B1 L p.h hn hb hh
  simp only [hHdef] at hprinting hdegree hcoeff hlift hprime hwindows hchain
  have hscalar := hs.early_preparation_bounds B1 hb
  have hV := hs.preparationEnvelope_binary_height B1 L hn
  rw [hHdef] at hV
  have hX : p.Xmax ≤ 2 ^ H := hscalar.Xmax.trans hV
  have hk : p.k ≤ 2 ^ H := hscalar.k.trans hV
  have hU : 128 * p.U ≤ 2 ^ H := hscalar.ell0_numerator.trans hV
  have hT : p.T ≤ 2 ^ H := hscalar.T.trans hV
  have hmoment : 4 * p.m * p.Xmax + 2 * p.m * p.k + 4 * p.m + 16 < 2 ^ (100 * H) := by
    rw [hs.m_eq]
    have heq : (2 : ℕ) ^ (H + 6) = 64 * 2 ^ H := by rw [pow_add]; norm_num; ring
    have hsmall : 4 * 4 * p.Xmax + 2 * 4 * p.k + 4 * 4 + 16 < 2 ^ (H + 6) := by
      rw [heq]
      omega
    exact hsmall.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hheight : 32 * p.m * p.U + 4 < 2 ^ (100 * H) := by
    rw [hs.m_eq]
    have hsmall : 32 * 4 * p.U + 4 < 2 ^ (H + 3) := by rw [pow_add]; norm_num; omega
    exact hsmall.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hheightGuard : 64 * p.T + 128 < 2 ^ (100 * H) := by
    have hsmall : 64 * p.T + 128 < 2 ^ (H + 8) := by rw [pow_add]; norm_num; omega
    exact hsmall.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))
  refine {
    header := ?_
    early := ?_
    print := hprinting.1.trans_le hp
    log := hprinting.2.trans_le hp
    degree := hdegree.trans_le hp
    coefficient := hcoeff.trans_le hp
    lift := hlift.2.trans_le hwidth
    powers := ?_
    prime := hprime.trans_le hp
    moment := hmoment.trans_le hp
    primeCensus := hwindows.1.trans_le hp
    pairWindow := hwindows.2.trans_le hp
    height := hheight.trans_le hp
    heightGuard := hheightGuard.trans_le hp
    ell := ?_
    h := hchain.2.1
    T := hchain.2.2.1
    J := hchain.2.2.2.1
    chain := hchain.2.2.2.2.trans hwidth }
  · have h := preparationHeader_operand_binary_bound B1 L x.n w1 w2 hn hw1 hw2
    rw [hHdef] at h
    exact h.trans_le hp
  · apply hs.publicScales_widths B1 L num den hn hb hnum hden hu hd hnumBits hdenBits C
    exact (le_of_eq (congrArg (fun z : ℕ => 100 * z) hHdef)).trans hwidth
  · intro j hj
    have h := hs.liftProgram_operand_binary_bound B1 L x.n j hn hb le_rfl hj
    rw [hHdef] at h
    exact h.trans_le hp
  · rw [hs.m_eq]
    exact hchain.1


end NearQuarticWires.Cells.CoreRules
