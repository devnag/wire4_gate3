import Proof.Quartic.StagePrep.CanonicalProgram

/-!
# The executed final lift and moment guard

Paper: `sec:params`, paper/paper.tex, and
preparation in `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open NearCubicGates.Close.Dispatch

/-- The final prime lift and moment-degree test in
`sec:params`, paper/paper.tex, retain the actual
least exponent, restore the star dimension and set the exact
moment-guard flag. The repeated lift search is fully charged. -/
theorem preparationLiftStage_spec (C : Ctx) (a : DS VV) (hc : Cst a)
    (BN P k m X D : ℕ) (hBNv : a.env coefficientBitsReg=BN)
    (hPv : a.env pP=P) (hkv : a.env pK=k) (hmv : a.env mReg=m)
    (hXv : a.env xMaxReg=X) (hDv : a.env pDM=D) (ha : a.env vADM=1)
    (hBN : 1≤BN) (hP : 4≤P) (hlift : 3*(BN-1)+4<C.Wd)
    (hpow : ∀ j≤2*BN, P^j<2^C.Wd)
    (hm : 0 < m) (hX : 0 < X)
    (hW : 4*m*X+2*m*k+4*m+16<2^C.Wd) :
    Hs C preparationLiftStage a (liftCost (BN-1)+200) (fun b =>
      Cells.ParameterArithmetic.liftExponent BN P=some (b.env pE) ∧
      b.env pK=k ∧ b.env pP=P ∧ b.env vADM=bnat (4*m*X+2*m*k≤D) ∧
      b.cp=a.cp ∧ b.wq=a.wq ∧ b.out=a.out ∧ Cst b ∧
      FrS a b (pX1 :: vADM :: liftSavedKReg :: pK :: pEB :: liftVT)) := by
  unfold preparationLiftStage
  refine Hx.hs (Hs.then (liftExponentProgram_spec C a hc BN P k hBNv hPv hkv hBN hP hlift hpow)
    (fun b ⟨_,hbe,hbk,hbP,hbcp,hbwq,hbout,hbc,hbfr⟩ n1 hn1 => ?_))
  have hbm : b.env mReg=m := (hbfr _ (by decide) (by decide)).trans hmv
  have hbX : b.env xMaxReg=X := (hbfr _ (by decide) (by decide)).trans hXv
  have hbD : b.env pDM=D := (hbfr _ (by decide) (by decide)).trans hDv
  have hbA : b.env vADM=bnat True := by
    rw [hbfr _ (by decide) (by decide),ha]
    decide
  have h4m : 4*m≤4*m*X := Nat.le_mul_of_pos_right _ hX
  have h2m : 2*m≤4*m := Nat.mul_le_mul_right _ (by omega)
  refine Hs.last (checkedLe_spec C b hbc pX1 pDM
    (.add (.mul (.mul (.lit 4) (.var mReg)) (.var xMaxReg))
      (.mul (.mul (.lit 2) (.var mReg)) (.var pK))) True hbA
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by aevar) (by aevar) (by aeok [hbm,hbX,hbk])) ?_
  rintro d ⟨hdA,hdcp,hdwq,hdout,hdc,hdfr⟩ n2 hn2
  refine ⟨⟨?_,?_,?_,?_,hdcp.trans hbcp,hdwq.trans hbwq,hdout.trans hbout,hdc,
    FrS.trans (FrS.weaken hbfr (by decide)) (FrS.weaken hdfr (by decide))⟩,?_⟩
  · rw [hdfr _ (by decide) (by decide)]
    exact hbe
  · exact (hdfr _ (by decide) (by decide)).trans hbk
  · exact (hdfr _ (by decide) (by decide)).trans hbP
  · simpa only [AE.eval,hbm,hbX,hbk,hbD,true_and] using hdA
  · simp only [AE.cost] at hn2
    omega

end NearQuarticWires.StagePrep
