import Proof.Quartic.StagePrep.ParameterRegisters
import Proof.Quartic.StagePrep.ConcentrationRule

/-!
# Physical computation of the concentration parameter

Paper: `sec:params`, paper/paper.tex, and
preparation in `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open NearCubicGates.Close.Dispatch NearCubicGates.Close.Counter
open AE

/-- A saved dimension for the concentration computation of
`sec:params`, paper/paper.tex. -/
def savedDimensionReg : Fin VV := ⟨91, by decide⟩

/-- The integer search of `sec:params`, paper/paper.tex, preserves the original star dimension. -/
def concentrationProgram : St VV :=
  .seq (.op (.copy savedDimensionReg pK))
    (.seq (assign pK (add (add (mul (var mReg) (var pK)) (mul (lit 2) (var mReg))) (lit 3)))
      (.seq pTee (.seq (.op (.copy pT pSI)) (.op (.copy pK savedDimensionReg)))))

/-- The exact finite-search work for `sec:params`,
paper/paper.tex. -/
def concentrationCost (m k J : ℕ) (beta : ℚ) : ℕ :=
  let a := concentrationExponent m k
  let t := TBound a J beta
  5 * a + 440 + 10 * t + (t + 3) * (5 * t + 60)

/-- The computation in `sec:params`, paper/paper.tex, writes the canonical positive concentration parameter
and restores the star dimension. -/
theorem concentrationProgram_spec (C : Ctx) (a : DS VV) (hc : Cst a)
    (m k J num den : ℕ) (beta : ℚ)
    (hm : a.env mReg = m) (hk : a.env pK = k) (hJ : a.env pJM = J)
    (hnum : a.env vNUM = num) (hden : a.env vDEN = den)
    (hbn : beta.num = num) (hbd : beta.den = den)
    (hbeta : 0 < beta) (hupper : beta ≤ 1 / 16) (hJpos : 1 ≤ J)
    (hwidth : concentrationExponent m k < C.Wd)
    (hleft : 4 * J * 2 ^ concentrationExponent m k * den < 2 ^ C.Wd)
    (hbound : 2 ^ TBound (concentrationExponent m k) J beta * num < 2 ^ C.Wd)
    (hboundWidth : TBound (concentrationExponent m k) J beta + 2 < C.Wd) :
    Hs C concentrationProgram a (concentrationCost m k J beta) (fun b =>
      b.env pT = Cells.ParameterArithmetic.concentrationT m k J beta ∧
      b.env pK = k ∧ b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧
      Cst b ∧ FrS a b (savedDimensionReg :: pK :: pT :: teeT)) := by
  have hsmall : m * k + 2 * m + 3 < 2 ^ C.Wd := by
    exact (show m * k + 2 * m + 3 < C.Wd from hwidth).trans Nat.lt_two_pow_self
  unfold concentrationProgram
  refine Hx.hs (Hs.then (hs_copy C savedDimensionReg pK a (by decide))
    (fun b0 hb0 n0 hn0 => ?_))
  subst hb0
  have hc0 : Cst (a.set savedDimensionReg (a.env pK)) := hc.set _ _ (by decide)
  have hm0 : (a.set savedDimensionReg (a.env pK)).env mReg = m := by
    rw [DS.set_env_ne _ _ (by decide), hm]
  have hk0 : (a.set savedDimensionReg (a.env pK)).env pK = k := by
    rw [DS.set_env_ne _ _ (by decide), hk]
  refine Hs.then (assign_spec pK (by decide) (by decide)
    (.add (.add (.mul (.var mReg) (.var pK)) (.mul (.lit 2) (.var mReg))) (.lit 3))
    _ (by aevar) (by aevar) hc0 (by aeok [hm0, hk0]))
    (fun d ⟨hdk, hdfr, hdcp, hdwq, hdout, hdc⟩ n1 hn1 => ?_)
  have hdk' : d.env pK = concentrationExponent m k := by
    simpa only [AE.eval, hm0, hk0, concentrationExponent] using hdk
  have hdJ : d.env pJM = J := by
    rw [hdfr _ (by decide) (by decide) (by decide), DS.set_env_ne _ _ (by decide), hJ]
  have hdnum : d.env vNUM = num := by
    rw [hdfr _ (by decide) (by decide) (by decide), DS.set_env_ne _ _ (by decide), hnum]
  have hdden : d.env vDEN = den := by
    rw [hdfr _ (by decide) (by decide) (by decide), DS.set_env_ne _ _ (by decide), hden]
  have hdsaved : d.env savedDimensionReg = k := by
    rw [hdfr _ (by decide) (by decide) (by decide), DS.set_env_self, hk]
  refine Hs.then (pTee_spec d hdc _ J num den beta hbn hbd hdk' hdJ hdnum hdden
    hwidth hleft hbound hboundWidth)
    (fun e ⟨hresult, hecp, hewq, heout, hec, hefr⟩ n2 hn2 => ?_)
  have heT : e.env pSI = Cells.ParameterArithmetic.concentrationT m k J beta := by
    rcases hresult with ⟨_, hsome⟩ | ⟨_, hnone⟩
    · rw [leastT_eq_concentrationT m k J beta hbeta hupper hJpos] at hsome
      exact (Option.some.inj hsome).symm
    · rw [leastT_eq_concentrationT m k J beta hbeta hupper hJpos] at hnone
      cases hnone
  have hesaved : e.env savedDimensionReg = k := by
    rw [hefr _ (by decide) (by decide), hdsaved]
  refine Hs.then (hs_copy C pT pSI e (by decide)) (fun f hf n3 hn3 => ?_)
  subst hf
  refine Hs.last (hs_copy C pK savedDimensionReg _ (by decide)) ?_
  rintro g rfl n4 hn4
  have hfr : FrS a ((e.set pT (e.env pSI)).set pK ((e.set pT (e.env pSI)).env savedDimensionReg))
      (savedDimensionReg :: pK :: pT :: teeT) :=
    FrS.trans (Fr.toS (Fr.set _ _ (by decide)))
      (FrS.trans (hdfr.toS _ (by decide) (by decide))
        (FrS.trans (FrS.weaken hefr (by decide))
          (FrS.trans (Fr.toS (Fr.set _ _ (by decide)))
            (Fr.toS (Fr.set _ _ (by decide))))))
  refine ⟨⟨?_, ?_, hecp.trans hdcp, hewq.trans hdwq, heout.trans hdout,
    (hec.set pT _ (by decide)).set pK _ (by decide), hfr⟩, ?_⟩
  · rw [DS.set_env_ne _ _ (by decide), DS.set_env_self, heT]
  · rw [DS.set_env_self, DS.set_env_ne _ _ (by decide), hesaved]
  · simp only [AE.cost] at hn1
    have hn2' : n2 ≤ 5 * concentrationExponent m k + 400 +
        10 * TBound (concentrationExponent m k) J beta +
        (TBound (concentrationExponent m k) J beta + 3) *
          (5 * TBound (concentrationExponent m k) J beta + 60) := by
      simpa only [AE.eval, hm0, hk0, concentrationExponent] using hn2
    dsimp only [concentrationCost]
    omega

end NearQuarticWires.StagePrep
