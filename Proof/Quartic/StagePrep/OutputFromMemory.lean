import Proof.Quartic.StagePrep.SuccessOutput
import Proof.Quartic.StagePrep.OutputCost
import Proof.Quartic.StagePrep.ParameterMemory
import Proof.Quartic.StagePrep.ChainWidths
import Proof.Quartic.Cells.ParametersExecutionWidths

/-!
# The complete successful preparation exit

Paper: `sec:params`, paper/paper.tex, and
the preparation cost in `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open NearCubicGates.Close.Dispatch
open NearCubicGates.Close.Counter
open NearCubicGates.Close.Interfaces
open NearCubicWires.RepairOrdinary

/-- The retained exact parameter memory of `sec:params`,
paper/paper.tex, suffices to run the actual
serializer and bounded witness reader at the original-input
word width, including the second paid factor-chain computation. -/
theorem successfulOutput_from_memory (C : Ctx) (a : DS VV)
    (hc : Cst a) (hv : Valid C a) (c : Call) (p : Cells.Parameters)
    (hs : Cells.ParameterRules (Builder.callInput c) p)
    (B1 L : ℕ) (hn : c.n ≤ L) (hL : (callWord c).length ≤ L)
    (hb : 1 ≤ c.radius*(c.n:ℚ)^B1)
    (hwidth : 100*Cells.ParameterArithmetic.preparationBitBase B1 L ≤ C.Wd)
    (hmem : RegisterValues a (parameterMemoryValues p))
    (hparse : ParseOut c a) (hcw : C.cw=callWord c) (hwq : a.wq=0)
    (hratio : firstRatio p.ell0 p.h p.T=(a.env pXN:ℚ)/a.env pXD)
    (hN : 0<a.env pXN) (hND : a.env pXN ≤ a.env pXD)
    (hD : a.env pXD ≤ (p.h+32)*a.env pXN)
    (hDbits : a.env pXD<2^(5*(Cells.ParameterArithmetic.preparationBitBase B1 L+1)+22)) :
    Hs C successfulPreparationOutput a (successOutputCost c p C.Wd)
      (fun b => b.out=a.out++(true::(callWord c++Program.parametersWord p++
        frame (Program.witnessPrefix c p C.wit))) ∧
        b.wq=min (Program.witnessReadLength c p) C.wit.length ∧
        b.cp=(callWord c).length ∧ Cst b) := by
  have hcore : Cells.CoreRules (Builder.callInput c) p := hs
  have hH := Cells.ParameterArithmetic.preparationBitBase_bounds B1 L
  have hP : p.P ≤ c.n := hs.prime_candidate.2.1
  have hh : p.h ≤ c.n := by
    rw [hs.h_eq,hs.hE_eq]
    exact (Nat.div_le_self _ _).trans ((Nat.div_le_self _ _).trans hP)
  have hchain := hcore.rateChain_operand_binary_bounds B1 L p.h hn hb hh
  have hLw : p.Lw<2^(Cells.ParameterArithmetic.preparationBitBase B1 L+1) :=
    ((hs.scalar_preparation_bounds B1 hb).Lw.trans
      (hcore.preparationEnvelope_binary_height B1 L hn)).trans_lt
      (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self _))
  have hJmax : p.Jmax=Jmax c.n := by rw [hs.Jmax_eq,hs.mu_eq]; rfl
  have hwidth' := chain_width_bounds _ (a.env pXD) p.h (Jmax c.n) p.Lw C.Wd
    hDbits hchain.2.1 (by rw [←hJmax]; exact hchain.2.2.2.1) hLw
    (hchain.2.2.2.2.trans hwidth)
  have hpi : 0 ≤ p.pi0 := by
    rw [hs.pi0_eq]
    exact div_nonneg (Nat.cast_nonneg _) (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
  have heta : 0 ≤ p.eta := hcore.eta_pos.le
  have hell : 0 ≤ p.ell0 := by rw [hs.ell0_eq]; exact Nat.cast_nonneg _
  have hden : p.ell0.den=1 := by rw [hs.ell0_eq]; exact Rat.den_natCast _
  obtain ⟨hhead,htail⟩ := parameterMemory_layout a hc p hmem hpi heta hell hden
  have hPv : a.env pP=p.P := hmem (pP,p.P) (by simp [parameterMemoryValues])
  have hkv : a.env pK=p.k := hmem (pK,p.k) (by simp [parameterMemoryValues])
  have hJv : a.env pJ=p.J := hmem (pJ,p.J) (by simp [parameterMemoryValues])
  have hJM : a.env pJM=Jmax c.n :=
    (hmem (pJM,p.Jmax) (by simp [parameterMemoryValues])).trans hJmax
  have hlen : p.factors.length=p.J-1 := by rw [hs.factors_eq]; simp [chainFactors]
  have hstop : stopIndex (firstRatio p.ell0 p.h p.T) c.n=some p.factors.length := by
    rw [hlen]; exact hs.chain_eq
  have hfac : chainFactors (firstRatio p.ell0 p.h p.T) p.factors.length=p.factors := by
    rw [hlen]; exact hs.factors_eq.symm
  have hpw : 2*(p.P+1)+8<2^C.Wd := by
    have hz : 2*(p.P+1)+8 ≤ C.Wd := by omega
    exact hz.trans_lt Nat.lt_two_pow_self
  have hcwB : C.cw.length<2^C.Wd := by
    rw [hcw]
    exact (hL.trans (hH.2.1.trans (by omega))).trans_lt Nat.lt_two_pow_self
  have hread := witnessReadLength_preparation_bound c p hs
  have hJsmall : p.J ≤ c.n+1 := by
    have hj := hs.J_bound
    rw [hs.Jmax_eq] at hj
    have hm := hs.mu_le_lambda.trans hcore.lambda_le_n
    change p.mu ≤ c.n at hm
    omega
  have hG : Builder.occurrences c 0+Builder.occurrences c 1 ≤ 2*c.n^4 := by
    have hg := hs.input_valid.2.2.1.trans hs.input_valid.2.2.2.1
    simpa [Builder.callInput,Builder.occurrences,Builder.gatesOf] using hg
  have h1R : 1 ≤ (c.n+1)^5 := Nat.one_le_pow _ _ (by omega)
  have hnR : c.n+1 ≤ (c.n+1)^5 := Nat.le_self_pow (by norm_num) _
  have h4R : c.n^4 ≤ (c.n+1)^5 :=
    (Nat.pow_le_pow_left (Nat.le_succ _) _).trans
      (Nat.pow_le_pow_right (by omega) (by norm_num))
  have hsmall : Program.witnessReadLength c p+p.J+
      Builder.occurrences c 0+Builder.occurrences c 1+16 ≤ 25*(c.n+1)^5 := by
    nlinarith only [hread,hJsmall,hG,h1R,hnR,h4R]
  have hbinary := Cells.ParameterArithmetic.polynomial_value_binary_bound 25 (c.n+1) 5
  have hprefix : Program.witnessReadLength c p+p.J+
      Builder.occurrences c 0+Builder.occurrences c 1+16<2^C.Wd :=
    (hsmall.trans hbinary).trans_lt (Nat.pow_lt_pow_right (by norm_num) (by omega))
  simpa only [successOutputCost,hcw] using
    successfulPreparationOutput_spec C a hc hv c p
      (by rw [hcw]; exact hparse.cl) hcw hhead htail hPv hs.primes_eq
      (a.env pXN) (a.env pXD) p.h (firstRatio p.ell0 p.h p.T)
      rfl rfl hJM hratio hN hND hD hstop hfac hkv hJv
      (by simpa [Builder.occurrences,Builder.gatesOf] using hparse.c1.g)
      (by simpa [Builder.occurrences,Builder.gatesOf] using hparse.c2.g)
      hwq hwidth'.1 hpw (by omega) hcwB hprefix

end NearQuarticWires.StagePrep
