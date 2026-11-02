import Proof.Quartic.StagePrintTuple.RoleFlags

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageTuple

open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells
open StagePrint.Header

/-- `lem:print`, paper/paper.tex:
the selected original occurrence is followed by the actual nine natural
affine fields, before the final three raw corner flags. -/
def roleOutputFields : List (Fin VV) :=
  originalIndex :: baseHeaderRegisters ++ [leftPattern,rightPattern]

/-- `lem:print`, paper/paper.tex:
the row-role writer physically serializes all selected metadata, with
the original occurrence index kept separate from the affine header. -/
def writeRoleOutput : St VV MM :=
  .seq (emitHeaderFields roleOutputFields) emitRoleFlags

/-- `lem:print` and `prop:time`, paper/paper.tex: every selected scalar and raw flag is emitted
from its actual stored binary value, preserving all source stores. -/
theorem writeRoleOutput_spec (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (hW : 2 ≤ C.Wd)
    (hfit : ∀ x ∈ roleOutputFields, natBitLength (a.env x) + 2 < 2 ^ C.Wd) :
    Hs C writeRoleOutput a
      (headerEmitCost (roleOutputFields.map a.env) + 12) (fun b =>
      b.out = a.out ++ (roleOutputFields.map a.env).flatMap natWord ++
        [decide (a.env leftCorner = 1),decide (a.env rightCorner = 1),
          decide (a.env transpose = 1)] ∧
      (b.ip,b.ram,b.rc,b.kin,b.kout,b.kc) =
        (a.ip,a.ram,a.rc,a.kin,a.kout,a.kc) ∧ Cst b ∧
      Fr a b headerEmitScratch) := by
  unfold writeRoleOutput
  refine Hs.seq (t2:=11)
    (emitHeaderFields_run C roleOutputFields a hc hW (by decide) hfit) ?_
  rintro b ⟨bo,bs,bc,bfr⟩
  refine (emitRoleFlags_spec C b bc).mono le_rfl ?_
  rintro out rfl
  refine ⟨?_,bs,⟨bc.z,bc.one,bc.two⟩,bfr⟩
  rw [bo,bfr leftCorner (by decide),bfr rightCorner (by decide),bfr transpose (by decide)]

end NearQuarticWires.StageTuple
