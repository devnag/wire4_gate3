import Proof.Quartic.StagePrep.HeaderStage
import Proof.Quartic.StagePrep.ActiveGuard

/-!
# The initial rejected parameter exit

Paper: `sec:params`, paper/paper.tex, and
preparation in `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open NearCubicGates.Close.Dispatch

/-- A failed first size guard in `sec:params`,
paper/paper.tex, skips every subsequent
parameter operation by the actual guarded instruction sequence. -/
theorem canonicalPreparation_header_failure (C : Ctx) (a : DS VV) (hc : Cst a)
    (n w1 w2 : ℕ) (hn : a.env vN=n) (hw1 : a.env vTW1=w1)
    (hw2 : a.env vTW2=w2) (ha : a.env vADM=1)
    (hfail : ¬4*(16*NearCubicGates.Target.mu n)≤n)
    (hW : (3*n+4)*(n+1)+w1+w2+100*n+100<2^C.Wd) :
    Hs C canonicalPreparation a (20*n+300) (fun b =>
      b.env vADM=0 ∧ b.cp=a.cp ∧ b.wq=a.wq ∧ b.out=a.out ∧ Cst b) := by
  unfold canonicalPreparation
  rw [guardedPreparationStages]
  refine Hx.hs (Hs.then (activeGuard_spec C a hc preparationHeaderStage _ _ ha
    (preparationHeaderStage_spec C a hc n w1 w2 hn hw1 hw2 ha hW))
    (fun b ⟨_,_,_,_,_,_,hbflag,hbcp,hbwq,hbout,hbc,_⟩ n1 hn1 => ?_))
  have hbzero : b.env vADM=0 := by rw [hbflag]; exact bnat_zero_of_not hfail
  refine Hs.last (guardedPreparationStages_failed C
    [preparationScalesStage,preparationDegreeStage,preparationPrimeStage,
      preparationLiftStage,preparationWindowsStage,preparationHeightStage,
      preparationChainStage,preparationFinishStage]
    b hbc (by rw [hbzero]; decide)) ?_
  rintro d ⟨hdflag,hdcp,hdwq,hdout,hdc,_⟩ n2 hn2
  refine ⟨⟨hdflag.trans hbzero,hdcp.trans hbcp,hdwq.trans hbwq,hdout.trans hbout,hdc⟩,?_⟩
  simp only [List.length_cons,List.length_nil] at hn2
  omega

end NearQuarticWires.StagePrep
