import Proof.Quartic.StagePrint.EntryWidthArithmetic

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StagePrint.GreedyEntry
open NearCubicWires NearCubicGates.Close.Cells

/-- `lem:print`, paper/paper.tex: actual binary
packing uses a fixed arithmetic prefix, comparison and final slack. -/
def packingWidthProgram : St VV MM :=
  .seq packingPrefix (.seq maximumProgram
    (.seq (.op (.add widthVar v2)) (.op (.add widthVar v2))))

/-- `lem:print`, paper/paper.tex: the complete
physical constant-length computation yields the literal packing width,
while retaining every source field and each original byte stream. -/
theorem packingWidthProgram_run (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (n L D c : ℕ) (hn : a.env Header.arity=n)
    (hl : a.env Header.Lout=L) (hd : a.env degreeVar=D)
    (hcb : a.env coefficientBitsVar=c)
    (hcap : (D+2)*(L+2*((n+1)/2)+D+4)+c+n+L+D+30<2^C.Wd) :
    Hs C packingWidthProgram a 40 (fun b =>
      b.env widthVar=NativeWidth.packedBits L (2*((n+1)/2)) D c ∧
      b.sh=a.sh ∧ Cst b ∧
      Fr a b [halfVar,sumVar,factorVar,productVar,widthVar,vJ]) := by
  change Hs C (.seq packingPrefix (.seq maximumProgram
    (.seq (.op (.add widthVar v2)) (.op (.add widthVar v2))))) a 40 _
  have hp:=packingPrefix_run C a hc n L D c hn hl hd hcap
  refine (Hs.seq (t2:=7) hp fun b ⟨bw,bp,bsh,bc,bfr⟩ => ?_).mono (by omega) (fun _ h=>h)
  have bcb : b.env coefficientBitsVar=c := by rw [bfr _ (by decide),hcb]
  refine (Hs.seq (t1:=2) (t2:=3) (maximumProgram_run C b bc (bw.trans bp.symm))
    fun d ⟨dw,dsh,dc,dfr⟩ => ?_).mono (by omega) (fun _ h=>h)
  have dw' : d.env widthVar=max c ((D+2)*(L+2*((n+1)/2)+D+4)) := by
    simpa only [bcb,bp] using dw
  have hwfit : d.env widthVar+4<2^C.Wd := by
    rw [dw']
    rcases le_total c ((D+2)*(L+2*((n+1)/2)+D+4)) with h|h
    · rw [max_eq_right h];omega
    · rw [max_eq_left h];omega
  refine Hs.seq (t2:=1) (hs_add C widthVar v2 d (by decide) (by rw [dc.two];omega)) fun e he => ?_
  subst e
  refine (hs_add C widthVar v2 _ (by decide) (by
    simp only [DS.set_env_self,DS.set_env_ne _ _ (show v2≠widthVar by decide)]
    rw [dc.two]
    omega)).mono le_rfl ?_
  rintro e rfl
  have hfr : Fr d ((d.set widthVar (d.env widthVar+d.env v2)).set widthVar
      ((d.set widthVar (d.env widthVar+d.env v2)).env widthVar+
        (d.set widthVar (d.env widthVar+d.env v2)).env v2)) [halfVar,sumVar,factorVar,productVar,widthVar,vJ] :=
    (Fr.set d _ (by simp)).trans (Fr.set _ _ (by simp))
  refine ⟨?_,dsh.trans bsh,Cst.of_fr dc hfr (by decide),
    (bfr.weaken (by simp)).trans ((dfr.weaken (by simp)).trans hfr)⟩
  simp only [DS.set_env_self,DS.set_env_ne _ _ (show v2≠widthVar by decide)]
  rw [dc.two,dw']
  simp only [NativeWidth.packedBits,Nat.add_assoc]

end NearQuarticWires.StagePrint.GreedyEntry
