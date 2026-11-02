import Proof.Quartic.StageLift.FrameWrite

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StagePrint.EntryFormat
open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells
open StageLift StageMain.CallSkip

/-- `lem:print`, paper/paper.tex: a retained
finite field is framed using its actually measured independent length. -/
def emitStoredField (store : Fin MM) (lengthVar : Fin VV) : St VV MM :=
  .seq (.op (.copy lengthCounter lengthVar)) (emitMemoryFrame store)

/-- `lem:print`, paper/paper.tex: the field
writer reads real retained bytes, charges the store rewind and keeps
all original input and other retained fields intact. -/
theorem emitStoredField_run (C : Ctx) (store : Fin MM) (lengthVar : Fin VV)
    (hl : lengthVar≠lengthCounter) (bits : List Bool) (a : DS VV MM) (hc : Cst a)
    (hbits : a.ram store=bits.map Bool.toNat)
    (hlen : a.env lengthVar=bits.length) (hfit : bits.length<2^C.Wd) :
    Hs C (emitStoredField store lengthVar) a (a.rc store+10*bits.length+10) (fun b =>
      b.out=a.out++frame bits ∧ b.ip=a.ip ∧ b.ram=a.ram ∧
      b.rc=Function.update a.rc store bits.length ∧
      (b.kin,b.kout,b.kc)=(a.kin,a.kout,a.kc) ∧ Cst b ∧
      Fr a b [lengthCounter,c0,t0]) := by
  unfold emitStoredField
  refine (Hs.seq (t2:=a.rc store+10*bits.length+8)
    (hs_copy C lengthCounter lengthVar a (Ne.symm hl)) fun d hd => ?_).mono
      (by omega) (fun _ h=>h)
  subst d
  let d:=a.set lengthCounter (a.env lengthVar)
  have hdc : Cst d:=Cst.of_fr hc (Fr.set a _ (T:=[lengthCounter]) (by simp)) (by decide)
  refine (emitMemoryFrame_spec C store bits d hdc hbits
    (by simpa only [d,DS.set_env_self] using hlen) hfit).mono le_rfl ?_
  rintro b ⟨bo,bi,br,brc,bk,bc,bfr⟩
  exact ⟨bo,bi,br,brc,bk,bc,
    (Fr.set a _ (T:=[lengthCounter,c0,t0]) (by simp)).trans (bfr.weaken (by simp))⟩

end NearQuarticWires.StagePrint.EntryFormat
