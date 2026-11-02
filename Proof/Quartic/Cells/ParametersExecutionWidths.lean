import Proof.Quartic.Cells.ParametersPublicFixedBits
import Proof.Quartic.Cells.ParametersPreparationHeaderBits
import Proof.Quartic.Cells.ParametersScalarBounds
import Proof.Quartic.StagePrep.ExecutionWidths

set_option autoImplicit false

namespace NearQuarticWires.Cells

open ParameterArithmetic

namespace CoreRules

variable {x : ParameterInput} {p : Parameters}

/-- `sec:params` and `prop:time`, paper/paper.tex: the exact early execution-width record follows
from the public identities and the original input encoding alone. -/
theorem publicScales_widths (hs : CoreRules x p) (B1 L num den : ℕ)
    (hn : x.n ≤ L) (hb : 1 ≤ x.beta * (x.n : ℚ) ^ B1)
    (hnum : x.beta.num = num) (hden : x.beta.den = den)
    (hu : 0 < num) (hd : 0 < den)
    (hnumBits : num ≤ 2 ^ L) (hdenBits : den ≤ 2 ^ L)
    (C : NearCubicGates.Close.Dispatch.Ctx)
    (hwidth : 100 * preparationBitBase B1 L ≤ C.Wd) :
    StagePrep.PublicScalesWidths C x p num den := by
  have hnumB : x.beta.num.natAbs ≤ 2 ^ L := by simpa only [hnum, Int.natAbs_natCast] using hnumBits
  have hdenB : x.beta.den ≤ 2 ^ L := by rwa [hden]
  have hf := hs.publicScales_fixed_operand_binary_bounds B1 L num den hn hb hnumBits hdenBits
  have hc := hs.concentrationProgram_operand_binary_bounds B1 L hn hnumB hdenB
  simp only [hnum, hden, Int.natAbs_natCast] at hc
  have hU := hs.uProgram_operand_binary_bounds B1 L num den hn hb hnum hden hu hd hnumBits hdenBits
  have hsamp := hs.sampleProgram_operand_binary_bound B1 L hn hb hnumB hdenB
  have hp : 2 ^ (100 * preparationBitBase B1 L) ≤ 2 ^ C.Wd := Nat.pow_le_pow_right (by norm_num) hwidth
  exact {
    dims := hf.dimensions.trans hwidth
    cwidth := hc.1.trans_le hwidth
    cleft := hc.2.1.trans_le hp
    cbound := hc.2.2.1.trans_le hp
    cbits := hc.2.2.2.trans_le hwidth
    tauW := hf.tau.trans_le hp
    uratio := hU.1.trans_le hp
    uroot := hU.2.trans_le hp
    piW := hf.pi.trans_le hp
    xroot := hf.populationRoot.trans_le hp
    xcut := hf.populationCut.trans_le hp
    fourier := hf.fourier.trans_le hp
    etaW := hf.eta.trans_le hp
    sample := hsamp.trans_le hp
    Qexp := hf.exponent.trans_le hwidth
    seed := hf.seed.trans_le hp }

end CoreRules

namespace ParameterRules

variable {x : ParameterInput} {p : Parameters}

/-- `sec:params` and `prop:time`, paper/paper.tex: every successful literal parameter record has
all concrete fixed-word execution capacities at one uniform width. -/
theorem selected_widths (hs : ParameterRules x p) (B1 L num den w1 w2 : ℕ)
    (hn : x.n ≤ L) (hb : 1 ≤ x.beta * (x.n : ℚ) ^ B1)
    (hnum : x.beta.num = num) (hden : x.beta.den = den)
    (hu : 0 < num) (hd : 0 < den)
    (hnumBits : num ≤ 2 ^ L) (hdenBits : den ≤ 2 ^ L)
    (hw1 : w1 ≤ 2 ^ L) (hw2 : w2 ≤ 2 ^ L)
    (C : NearCubicGates.Close.Dispatch.Ctx)
    (hwidth : 100 * preparationBitBase B1 L ≤ C.Wd) :
    StagePrep.SelectedWidths C x p num den w1 w2 (preparationBitBase B1 L + 1) := by
  have hc : CoreRules x p := hs
  generalize hHdef : preparationBitBase B1 L = H at *
  have hH := preparationBitBase_bounds B1 L
  rw [hHdef] at hH
  have hp : 2 ^ (100 * H) ≤ 2 ^ C.Wd := Nat.pow_le_pow_right (by norm_num) hwidth
  have hPP : p.P ≤ x.n := hs.prime_candidate.2.1
  have hh : p.h ≤ x.n := by
    rw [hs.h_eq, hs.hE_eq]
    exact (Nat.div_le_self _ _).trans ((Nat.div_le_self _ _).trans hPP)
  have hD : p.Dprime ≤ (x.n + 1) ^ 2 :=
    hs.scalar_window_upper.trans (Nat.pow_le_pow_left (hPP.trans (Nat.le_succ x.n)) _)
  have hprinting := hc.printingSizes_operand_binary_bound B1 L hn hb
  have hdegree := hc.degreeSearch_operand_binary_bound B1 L hn hb
  have hcoeff := hc.coefficientBits_operand_binary_bound B1 L hn hb
  have hlift := hc.coefficientExponent_height_bound B1 L hn hb
  have hprime := hc.primeBudget_operand_binary_bound B1 L hn hb
  have hwindows := hc.primeWindows_operand_binary_bounds B1 L p.P p.Dprime hn hPP hD
  have hchain := hc.rateChain_operand_binary_bounds B1 L p.h hn hb hh
  simp only [hHdef] at hprinting hdegree hcoeff hlift hprime hwindows hchain
  have hscalar := hs.scalar_preparation_bounds B1 hb
  have hV := hc.preparationEnvelope_binary_height B1 L hn
  rw [hHdef] at hV
  have hX : p.Xmax ≤ 2 ^ H := hscalar.Xmax.trans hV
  have hk : p.k ≤ 2 ^ H := hscalar.k.trans hV
  have hU : 128 * p.U ≤ 2 ^ H := hscalar.ell0_numerator.trans hV
  have hT : p.T ≤ 2 ^ H := hscalar.T.trans hV
  have hLw : p.Lw ≤ 2 ^ H := hscalar.Lw.trans hV
  have hA : p.A ≤ 2 ^ H := hscalar.A.trans hV
  have hJ : p.J ≤ 2 ^ H := hscalar.J.trans hV
  have hZ : 1024 ≤ (2 : ℕ) ^ H := (by norm_num : 1024 ≤ 2 ^ 10).trans
    (Nat.pow_le_pow_right (by norm_num) (by omega))
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
  have hfinish : p.Lw * p.A + (p.J - 1) + 8 < 2 ^ (100 * H) := by
    have hprod := Nat.mul_le_mul hLw hA
    have hZ2 : 2 ^ H ≤ ((2 : ℕ) ^ H) ^ 2 := Nat.le_self_pow (by norm_num) _
    have hsmall : p.Lw * p.A + (p.J - 1) + 8 < 16 * ((2 : ℕ) ^ H) ^ 2 := by
      nlinarith only [hprod, hJ, hZ, hZ2, Nat.sub_le p.J 1]
    have heq : 16 * ((2 : ℕ) ^ H) ^ 2 = 2 ^ (2 * H + 4) := by
      rw [show 2 * H + 4 = H * 2 + 4 by omega, pow_add, pow_mul]
      norm_num
      ring
    rw [heq] at hsmall
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
    chain := hchain.2.2.2.2.trans hwidth
    finish := hfinish.trans_le hp }
  · have h := preparationHeader_operand_binary_bound B1 L x.n w1 w2 hn hw1 hw2
    rw [hHdef] at h
    exact h.trans_le hp
  · apply hc.publicScales_widths B1 L num den hn hb hnum hden hu hd hnumBits hdenBits C
    exact (le_of_eq (congrArg (fun z : ℕ => 100 * z) hHdef)).trans hwidth
  · intro j hj
    have h := hc.liftProgram_operand_binary_bound B1 L x.n j hn hb le_rfl hj
    rw [hHdef] at h
    exact h.trans_le hp
  · rw [hs.m_eq]
    exact hchain.1

end ParameterRules

end NearQuarticWires.Cells
