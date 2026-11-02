import Proof.Quartic.StagePrep.CanonicalProgram

/-!
# The executed final parameter guard

Paper: `sec:params`, paper/paper.tex, and
preparation in `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open NearCubicGates.Close.Dispatch

/-- The final fields and guard in `sec:params`,
paper/paper.tex, are produced by actual integer
operations and an exact comparison, retaining the factor product. -/
theorem preparationFinishStage_spec (C : Ctx) (a : DS VV) (hc : Cst a)
    (i A L Jmax : ℕ) (hiv : a.env pCI=i) (hAv : a.env pA=A)
    (hLv : a.env pLW=L) (hJv : a.env pJM=Jmax) (ha : a.env vADM=1)
    (hW : L*A+i+8<2^C.Wd) :
    Hs C preparationFinishStage a 63 (fun b =>
      b.env pJ=i+1 ∧ b.env pLB=(L-1)*A/2+1 ∧ b.env pA=A ∧
      b.env vADM=bnat (i+1≤Jmax) ∧
      b.cp=a.cp ∧ b.wq=a.wq ∧ b.out=a.out ∧ Cst b ∧
      FrS a b [pJ,pLB,vADM,vJ]) := by
  unfold preparationFinishStage
  refine Hx.hs (Hs.then (chainFinishProgram_spec C a hc i A L hiv hAv hLv hW)
    (fun b ⟨hbJ,hbL,hbcp,hbwq,hbout,hbc,hbfr⟩ n1 hn1 => ?_))
  have hbMax : b.env pJM=Jmax := (hbfr _ (by decide) (by decide)).trans hJv
  have hbA : b.env vADM=bnat True := by
    rw [hbfr _ (by decide) (by decide),ha]
    decide
  refine Hs.last (needLe_spec pJ pJM (by decide) b True hbA) ?_
  rintro d ⟨hdA,hdcp,hdwq,hdout,hdfr⟩ n2 hn2
  refine ⟨⟨(hdfr _ (by decide)).trans hbJ,(hdfr _ (by decide)).trans hbL,?_,?_,
    hdcp.trans hbcp,hdwq.trans hbwq,hdout.trans hbout,
    Cst.of_fr hbc hdfr (by decide) (by rw [hdfr vPOS (by decide),hdcp]; exact hbc.pos),
    FrS.trans (FrS.weaken hbfr (by decide)) (FrS.weaken hdfr.toS (by decide))⟩,by omega⟩
  · rw [hdfr _ (by decide),hbfr _ (by decide) (by decide),hAv]
  · simpa only [hbJ,hbMax,true_and] using hdA

end NearQuarticWires.StagePrep
