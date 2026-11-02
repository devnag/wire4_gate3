import Proof.Quartic.StagePrep.CanonicalProgram

/-!
# The executed concentration-height guard

Paper: `sec:params`, paper/paper.tex, and
preparation in `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open NearCubicGates.Close.Dispatch

/-- The new integer height test of `sec:params`,
paper/paper.tex, computes both exact height
fields and the initial chain scale before setting its flag. -/
theorem preparationHeightStage_spec (C : Ctx) (a : DS VV) (hc : Cst a)
    (P m U T : ℕ) (hPv : a.env pP=P) (hmv : a.env mReg=m)
    (hUv : a.env pU=U) (hTv : a.env pT=T) (ha : a.env vADM=1)
    (hm : 0 < m) (hU : 0 < U)
    (hW : 32*m*U+4 < 2^C.Wd) (hguard : 64*T+128 < 2^C.Wd) :
    Hs C preparationHeightStage a 400 (fun b =>
      b.env pHE=P/4 ∧ b.env pH=P/4/(2*m) ∧ b.env ellZeroReg=32*m*U ∧
      b.env vADM=bnat (64*T≤P/4/(2*m)) ∧
      b.cp=a.cp ∧ b.wq=a.wq ∧ b.out=a.out ∧ Cst b ∧
      FrS a b [pHE,pH,ellZeroReg,pX1,vADM,vJ]) := by
  unfold preparationHeightStage
  refine Hx.hs (Hs.then (chainHeightProgram_spec C a hc P m U hPv hmv hUv hm hU hW)
    (fun b ⟨hbE,hbH,hbell,hbcp,hbwq,hbout,hbc,hbfr⟩ n1 hn1 => ?_))
  have hbT : b.env pT=T := (hbfr _ (by decide) (by decide)).trans hTv
  have hbA : b.env vADM=bnat True := by
    rw [hbfr _ (by decide) (by decide),ha]
    decide
  refine Hs.last (checkedLe_spec C b hbc pX1 pH (.mul (.lit 64) (.var pT)) True hbA
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by aevar) (by aevar) (by aeok [hbT])) ?_
  rintro d ⟨hdA,hdcp,hdwq,hdout,hdc,hdfr⟩ n2 hn2
  refine ⟨⟨?_,?_,?_,?_,hdcp.trans hbcp,hdwq.trans hbwq,hdout.trans hbout,hdc,
    FrS.trans (FrS.weaken hbfr (by decide)) (FrS.weaken hdfr (by decide))⟩,?_⟩
  · exact (hdfr _ (by decide) (by decide)).trans hbE
  · exact (hdfr _ (by decide) (by decide)).trans hbH
  · exact (hdfr _ (by decide) (by decide)).trans hbell
  · simpa only [AE.eval,hbT,hbH,true_and] using hdA
  · simp only [AE.cost] at hn2
    omega

end NearQuarticWires.StagePrep
