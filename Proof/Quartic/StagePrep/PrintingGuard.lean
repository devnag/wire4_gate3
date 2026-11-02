import Proof.Quartic.StagePrep.CanonicalProgram

/-!
# The executed printing-degree guard

Paper: `sec:params`, paper/paper.tex, and
preparation in `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open NearCubicGates.Close.Dispatch

/-- The first printing test in `sec:params`, paper/paper.tex, retains the exact printer envelope and cached
logarithm, with an exact acceptance flag on both outcomes. -/
theorem preparationDegreeStage_spec (C : Ctx) (a : DS VV) (hc : Cst a)
    (n m B lam k : ℕ) (hnv : a.env vN = n) (hmv : a.env mReg = m)
    (hBv : a.env vB0 = B) (hlv : a.env pLAM = lam) (hkv : a.env pK = k)
    (ha : a.env vADM = 1) (hn : 0 < n)
    (hprint : printingAtomCount n m * printingChildCount n B lam +
      printingAtomCount n m + printingChildCount n B lam +
      2*n^4+(4*m+1)+(B+lam+3)+128 < 2^C.Wd)
    (hlog : 2*printingOccurrenceCount n m B lam+2 < 2^C.Wd)
    (hdeg : 100*(m*k+2+n*Nat.clog 2 (printingOccurrenceCount n m B lam))+
      n+k+256 < 2^C.Wd) :
    Hs C preparationDegreeStage a
      (5*Nat.clog 2 (printingOccurrenceCount n m B lam)+480) (fun b =>
      b.env atomsReg = printingAtomCount n m ∧
      b.env childCapReg = printingChildCount n B lam ∧
      b.env occurrenceCapReg = printingOccurrenceCount n m B lam ∧
      b.env degreeLogReg = Nat.clog 2 (printingOccurrenceCount n m B lam) ∧
      b.env vADM = bnat (Cells.ParameterArithmetic.DegreePass n m k
        (printingOccurrenceCount n m B lam) 0) ∧
      b.cp=a.cp ∧ b.wq=a.wq ∧ b.out=a.out ∧ Cst b ∧
      FrS a b [t3,t5,t6,atomsReg,childCapReg,occurrenceCapReg,vJ,
        degreeLogReg,pSI,pSF,pX5,pX6,vADM]) := by
  unfold preparationDegreeStage preparationSequence
  refine Hx.hs (Hs.then (printingSizesProgram_spec C a hc n m B lam
    hnv hmv hBv hlv hn hprint)
    (fun b ⟨hba,hbc,hbo,hbcp,hbwq,hbout,hbst,hbfr⟩ n1 hn1 => ?_))
  refine Hs.then (degreeLogProgram_spec C b hbst _ hbo hlog)
    (fun d ⟨hdl,hdcp,hdwq,hdout,hdc,hdfr⟩ n2 hn2 => ?_)
  refine Hs.then (hs_zero C pSI d) (fun e he n3 hn3 => ?_)
  subst he
  have hec : Cst (d.set pSI 0) := hdc.set _ _ (by decide)
  have hen : (d.set pSI 0).env vN = n := by
    simp (disch := decide) only [DS.set_env_ne,hdfr.ev,hbfr.ev]
    exact hnv
  have hem : (d.set pSI 0).env mReg = m := by
    simp (disch := decide) only [DS.set_env_ne,hdfr.ev,hbfr.ev]
    exact hmv
  have hek : (d.set pSI 0).env pK = k := by
    simp (disch := decide) only [DS.set_env_ne,hdfr.ev,hbfr.ev]
    exact hkv
  have hel : (d.set pSI 0).env degreeLogReg = Nat.clog 2 (printingOccurrenceCount n m B lam) := by
    rw [DS.set_env_ne _ _ (by decide),hdl]
  refine Hs.then (degreeTestProgram_spec C _ hec n m k _ 0
    hen hem hek hel (by rw [DS.set_env_self]) (Nat.zero_le _) hdeg)
    (fun f ⟨hff,_,hfcp,hfwq,hfout,hfc,hffr⟩ n4 hn4 => ?_)
  have hfA : f.env vADM = bnat True := by
    simp (disch := decide) only [hffr.ev,DS.set_env_ne,hdfr.ev,hbfr.ev]
    rw [ha]
    decide
  refine Hs.then (needEq_spec pSF v1 (by decide) f True hfA)
    (fun g ⟨hgA,hgcp,hgwq,hgout,hgfr⟩ n5 hn5 => ?_)
  have hgc : Cst g := Cst.of_fr hfc hgfr (by decide)
    (by rw [hgfr vPOS (by decide),hgcp]; exact hfc.pos)
  refine Hs.last (skip_spec g) ?_
  rintro z rfl n6 hn6
  have F : FrS a g [t3,t5,t6,atomsReg,childCapReg,occurrenceCapReg,vJ,
      degreeLogReg,pSI,pSF,pX5,pX6,vADM] :=
    FrS.trans (FrS.weaken hbfr (by decide))
      (FrS.trans (FrS.weaken hdfr (by decide))
        (FrS.trans (Fr.toS (Fr.set _ _ (by decide)))
          (FrS.trans (FrS.weaken hffr (by decide))
            (FrS.weaken hgfr.toS (by decide)))))
  refine ⟨⟨?_,?_,?_,?_,?_,hgcp.trans (hfcp.trans (hdcp.trans hbcp)),
    hgwq.trans (hfwq.trans (hdwq.trans hbwq)),hgout.trans (hfout.trans (hdout.trans hbout)),
    hgc.set _ _ (by decide),FrS.trans F (Fr.toS (Fr.set _ _ (by decide)))⟩,by omega⟩
  all_goals simp (disch := decide) only [DS.set_env_ne,hgfr.ev,hffr.ev,hdfr.ev]
  · exact hba
  · exact hbc
  · exact hbo
  · exact hdl
  · rw [hgA,hff,hfc.one]
    apply bnat_congr
    simp only [Cells.ParameterArithmetic.DegreePass,zero_mul,add_zero,true_and,bnat_eq_one]

end NearQuarticWires.StagePrep
