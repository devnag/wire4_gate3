import Proof.Quartic.StagePrintTuple.RoleData
import Proof.Quartic.StagePrintTuple.RowFields

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageTuple

open NearCubicWires NearCubicWires.RepairRepresentation
open StagePrint.Header

/-- `lem:print`, paper/paper.tex:
the role source is obtained directly from the retained original affine
prefix, the two actual occurrence banks and the canonical walk code. -/
def RowContext.rolePacket (r : RowContext)
    (i : Fin (17*(Builder.allGates r.header.call).length)) : RolePacket where
  scalars := fun j=> (baseHeaderValues r.header)[j.val]'(by
    simp [baseHeaderValues])
  firstCount := r.header.call.first.gates.length
  secondCount := r.header.call.second.gates.length
  radix := r.header.prepared.seedParameters.N
  address := r.walkCode.val
  atom := ⟨i.val,by simpa [Builder.allGates,List.length_append] using i.isLt⟩

/-- `lem:print`, paper/paper.tex:
the role packet's seven scalar bytes are exactly the previously retained
common header, with neither reordering nor a changed translation. -/
theorem RowContext.rolePacket_scalars (r : RowContext)
    (i : Fin (17*(Builder.allGates r.header.call).length)) :
    List.ofFn (r.rolePacket i).scalars=baseHeaderValues r.header := by
  apply List.ext_getElem
  · simp [baseHeaderValues]
  · intro j hj hk
    simp only [List.getElem_ofFn,RowContext.rolePacket]

/-- `lem:print`, paper/paper.tex:
the actual source packet is the literal concatenation of the retained
affine prefix, actual four-field context, and selected atom codec. -/
theorem RowContext.rolePacket_word (r : RowContext)
    (i : Fin (17*(Builder.allGates r.header.call).length)) :
    (r.rolePacket i).word=(baseHeaderValues r.header).flatMap natWord ++
      (natWord r.header.call.first.gates.length ++ natWord r.header.call.second.gates.length ++
        natWord r.header.prepared.seedParameters.N ++ natWord r.walkCode.val) ++ natWord i.val := by
  simp only [RolePacket.word,RolePacket.values]
  rw [r.rolePacket_scalars i]
  simp only [RowContext.rolePacket,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,
    List.append_nil,List.append_assoc]

/-- `sec:walks` and `lem:print`, paper/paper.tex: the physical low-first radix division selects the exact
vertex of the canonical finite-function walk enumeration. -/
theorem RowContext.indexedWalk_value (r : RowContext) (slot : Fin 8) :
    (StagePrint.indexedWalk r.header.prepared.seedParameters.N r.walkCode slot).val=
      r.walkCode.val/r.header.prepared.seedParameters.N^slot.val%
        r.header.prepared.seedParameters.N := rfl

end NearQuarticWires.StageTuple
