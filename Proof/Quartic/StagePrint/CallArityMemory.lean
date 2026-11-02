import Proof.Quartic.StageLift.MemorySource
import Proof.Quartic.StageLift.CallRetain
import Proof.Gates.Interfaces.Counter

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StagePrint.Header
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces

/-- `lem:print`, paper/paper.tex: the original input dimension is read from the physically retained finite call. -/
def arity : Fin VV:=84

/-- `lem:print`, paper/paper.tex: a real memory rewind and the standard binary source-field reader precede the arity assignment. -/
def readCallArity : St VV MM :=
  .seq (.op (.rwM StageLift.callStore))
    (.seq (StageLift.readMemoryNatural StageLift.callStore) (.op (.copy arity t3)))

/-- `lem:print`, paper/paper.tex: the raw finite source supplies the actual dimension, with its memory rewind and field scan fully charged. -/
theorem readCallArity_run (C : Ctx) (c : Call) (a : DS VV MM) (hc : Cst a)
    (hcall : a.ram StageLift.callStore=(callWord c).map Bool.toNat)
    (hwidth : natBitLength c.n+2≤C.Wd) :
    Hs C readCallArity a (a.rc StageLift.callStore+30*natBitLength c.n+40) (fun b=>
      b.env arity=c.n ∧ b.ip=a.ip ∧ b.out=a.out ∧ b.ram=a.ram ∧
      (b.kin,b.kout,b.kc)=(a.kin,a.kout,a.kc) ∧ Cst b ∧ Fr a b (arity::rdNatT)) := by
  let rest:=natWord (kindTag c.kind)++circuitWord c.first++circuitWord c.second++
    listWord natWord c.parity++ratWord c.radius
  unfold readCallArity
  refine (Hs.seq (t2:=30*natBitLength c.n+32) (hs_rwM C StageLift.callStore a) ?_).mono
    (by omega) (fun _ h=>h)
  rintro b rfl
  let b:=a.rew StageLift.callStore
  have bc : Cst b:=⟨hc.z,hc.one,hc.two⟩
  have ef:=StageLift.readMemoryNatural_spec C StageLift.callStore (callWord c) b bc hcall c.n rest
    (by simp [b,DS.rew,callWord,rest,List.append_assoc]) hwidth
  refine Hs.seq (t2:=1) ef ?_
  rintro d ⟨dv,_dw,_drc,dr,df⟩
  have dc : Cst d:=Cst.of_fr bc df (by decide)
  refine (hs_copy C arity t3 d (by decide)).mono le_rfl ?_
  rintro out rfl
  refine ⟨by simp [dv],?_,?_,?_,?_,?_,?_⟩
  · exact congrArg (fun t=>t.1) dr
  · exact congrArg (fun t=>t.2.1) dr
  · exact congrArg (fun t=>t.2.2.1) dr
  · exact congrArg (fun t=>(t.2.2.2.2.1,t.2.2.2.2.2.1,t.2.2.2.2.2.2)) dr
  · exact Cst.of_fr dc (show Fr d (d.set arity (d.env t3)) [arity] from Fr.set d _ (by simp)) (by decide)
  · exact (df.weaken (by intro y hy;exact List.mem_cons.mpr (Or.inr hy))).trans
      (Fr.set d _ (by simp))

end NearQuarticWires.StagePrint.Header
