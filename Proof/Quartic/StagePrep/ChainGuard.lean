import Proof.Quartic.StagePrep.CanonicalProgram

/-!
# The executed rate-chain stopping guard

Paper: `imp:chain`, paper/paper.tex, and
`sec:params`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open NearCubicGates.Close.Dispatch
open NearCubicGates.Close.Counter

/-- The finite chain stage of `sec:params`, paper/paper.tex, accepts exactly when the literal stopping
search succeeds and retains the exact factors at that index. -/
theorem preparationChainStage_spec (C : Ctx) (a : DS VV) (hc : Cst a)
    (ell h T S n : ℕ) (hellv : a.env ellZeroReg=ell)
    (hhv : a.env pH=h) (hTv : a.env pT=T) (hJv : a.env pJM=Jmax n)
    (ha : a.env vADM=1) (hell : 0 < ell) (hh : 0 < h) (hT : 0 < T)
    (hguard : 64*T≤h) (hellS : ell<2^S) (hhS : h<2^S) (hTS : T<2^S)
    (hJS : Jmax n<2^S) (hSW : 6*S+40≤C.Wd) :
    let r := firstRatio (ell:ℚ) h T
    Hs C preparationChainStage a (3024+chainCost (Jmax n) h) (fun b =>
      b.env pM1=firstDen (ell:ℚ) h T ∧
      b.env vADM=bnat ((stopIndex r n).isSome=true) ∧
      ((stopIndex r n).isSome=true → stopIndex r n=some (b.env pCI)) ∧
      b.env pA=(chainFactors r (b.env pCI)).prod ∧
      b.env pA<2^(5*S+22) ∧ b.env pCI≤Jmax n-1 ∧
      r=(b.env pXN:ℚ)/b.env pXD ∧ 0<b.env pXN ∧ b.env pXN≤b.env pXD ∧
      b.env pXD≤(h+32)*b.env pXN ∧ b.env pXD<2^(5*S+22) ∧
      b.cp=a.cp ∧ b.wq=a.wq ∧ b.out=a.out ∧ Cst b ∧
      FrS a b (vADM :: pX1 :: pX2 :: barT++chT)) := by
  dsimp only
  let r := firstRatio (ell:ℚ) h T
  unfold preparationChainStage
  refine Hx.hs (Hs.then (rateChainProgram_spec C a hc ell h T S n hellv hhv hTv hJv
    hell hh hT hguard hellS hhS hTS hJS hSW)
    (fun b ⟨hbM,⟨i,hbi,hbA,hbstop⟩,hbcap,hbiJ,hbr,hbN0,hbND,hbDle,hbDcap,
      hbcp,hbwq,hbout,hbc,hbfr⟩ n1 hn1 => ?_))
  have hbFlag : b.env vADM=bnat True := by
    rw [hbfr _ (by decide) (by decide),ha]
    decide
  refine Hs.last (needEq_spec pCF v1 (by decide) b True hbFlag) ?_
  rintro d ⟨hdFlag,hdcp,hdwq,hdout,hdfr⟩ n2 hn2
  have hdFlag' : d.env vADM=bnat ((stopIndex r n).isSome=true) := by
    rw [hdFlag,hbc.one]
    rcases hbstop with ⟨hcf,hsome⟩ | ⟨hcf,hnone⟩
    · rw [hcf,hsome]
      rfl
    · rw [hcf,hnone]
      rfl
  have hdstop : (stopIndex r n).isSome=true → stopIndex r n=some (d.env pCI) := by
    intro hon
    rw [hdfr _ (by decide),hbi]
    rcases hbstop with ⟨_,hsome⟩ | ⟨_,hnone⟩
    · exact hsome
    · rw [hnone] at hon
      cases hon
  refine ⟨⟨?_,hdFlag',hdstop,?_,?_,?_,?_,?_,?_,?_,?_,
    hdcp.trans hbcp,hdwq.trans hbwq,hdout.trans hbout,
    Cst.of_fr hbc hdfr (by decide) (by rw [hdfr vPOS (by decide),hdcp]; exact hbc.pos),
    FrS.trans (FrS.weaken hbfr (by decide)) (FrS.weaken hdfr.toS (by decide))⟩,by omega⟩
  · rw [hdfr _ (by decide),hbM]
  · rw [hdfr _ (by decide),hdfr _ (by decide),hbi]
    exact hbA
  · rw [hdfr _ (by decide)]
    exact hbcap
  · rw [hdfr _ (by decide)]
    exact hbiJ
  · rw [hdfr _ (by decide),hdfr _ (by decide)]
    exact hbr
  · rw [hdfr _ (by decide)]
    exact hbN0
  · rw [hdfr _ (by decide),hdfr _ (by decide)]
    exact hbND
  · rw [hdfr _ (by decide),hdfr _ (by decide)]
    exact hbDle
  · rw [hdfr _ (by decide)]
    exact hbDcap

end NearQuarticWires.StagePrep
