import Proof.Quartic.StagePrint.AtomRole
import Proof.Gates.Cells.Kit

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StagePrint.Header
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells

/-- `lem:print`, paper/paper.tex: the next actual canonical monomial-variable field is physically read before its ORIGINAL occurrence and star-corner metadata are decoded. -/
def readAtomRole : St VV MM:=.seq rdNatI
  (.seq (.op (.copy atomValue t3)) atomRoleProgram)

/-- `lem:print` and `prop:time`, paper/paper.tex: one actual input field, not a decoded variable provider, supplies the exact atom role and original gate index while all witness/source memory is retained. -/
theorem readAtomRole_run (C : Ctx) (G : ℕ) (i : Fin (17*G)) (rest : List Bool)
    (a : DS VV MM) (hc : Cst a)
    (hin : C.inp.drop a.ip=natWord i.val++rest)
    (hwidth : natBitLength i.val+2≤C.Wd)
    (hG : a.env occurrenceCount=G) (hpos : 0<G) (hGfit : 2*G≤2^C.Wd)
    (hr : 0<a.env WalkDigits.radix) (hrfit : 2*a.env WalkDigits.radix≤2^C.Wd)
    (hsmall : 17<2^C.Wd) :
    Hs C readAtomRole a (30*natBitLength i.val+4600) (fun b=>
      RoleData (a.env WalkDigits.number) (a.env WalkDigits.radix)
        (finProdFinEquiv.symm i).1 b ∧
      b.env originalIndex=(finProdFinEquiv.symm i).2.val ∧
      b.ip=a.ip+(natWord i.val).length ∧ b.out=a.out ∧ b.ram=a.ram ∧ b.rc=a.rc ∧
      (b.kin,b.kout,b.kc)=(a.kin,a.kout,a.kc) ∧ Cst b) := by
  unfold readAtomRole
  refine (Hs.seq (t2:=4504) (rdNatI_spec (C:=C) a hc i.val rest hin hwidth) ?_).mono
    (by omega) (fun _ h=>h)
  rintro b ⟨bi,_bb,bip,bsh,bfr⟩
  have bc : Cst b:=Cst.of_fr hc bfr (by decide)
  refine Hs.seq (t2:=4502) (hs_copy C atomValue t3 b (by decide)) ?_
  rintro d rfl
  let d:=b.set atomValue (b.env t3)
  have dfr : Fr b d [atomValue]:=Fr.set b _ (by simp)
  have adfr : Fr a d (atomValue::rdNatT):=
    (bfr.weaken (by intro x hx;exact List.mem_cons.mpr (Or.inr hx))).trans
      (dfr.weaken (by simp))
  have dg : d.env occurrenceCount=G:=by rw [adfr occurrenceCount (by decide)];exact hG
  have drad : d.env WalkDigits.radix=a.env WalkDigits.radix:=adfr _ (by decide)
  have dnum : d.env WalkDigits.number=a.env WalkDigits.number:=adfr _ (by decide)
  have dc : Cst d:=Cst.of_fr bc dfr (by decide)
  have ed:=atomRoleProgram_run C G i d (by simp [d,bi]) dg hpos hGfit
    (by rw [drad];exact hr) (by rw [drad];exact hrfit) hsmall
  refine ed.mono le_rfl ?_
  rintro out ⟨od,oi,osh,ofr⟩
  have oip : out.ip=b.ip:=congrArg (fun t=>t.1) osh
  have oo : out.out=b.out:=congrArg (fun t=>t.2.1) osh
  have oram : out.ram=b.ram:=congrArg (fun t=>t.2.2.1) osh
  have orc : out.rc=b.rc:=congrArg (fun t=>t.2.2.2.1) osh
  have ostr : (out.kin,out.kout,out.kc)=(b.kin,b.kout,b.kc):=
    congrArg (fun t=>(t.2.2.2.2.1,t.2.2.2.2.2.1,t.2.2.2.2.2.2)) osh
  refine ⟨?_,oi,oip.trans bip,?_,?_,?_,?_,Cst.of_fr dc ofr (by decide)⟩
  · simpa only [dnum,drad] using od
  · exact oo.trans (congrArg (fun t=>t.1) bsh)
  · exact oram.trans (congrArg (fun t=>t.2.1) bsh)
  · exact orc.trans (congrArg (fun t=>t.2.2.1) bsh)
  · exact ostr.trans (congrArg (fun t=>(t.2.2.2.1,t.2.2.2.2.1,t.2.2.2.2.2)) bsh)

end NearQuarticWires.StagePrint.Header
