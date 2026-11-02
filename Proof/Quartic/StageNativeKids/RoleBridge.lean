import Proof.Quartic.StageNativeKids.RoleBounds

set_option autoImplicit false

namespace NearQuarticWires.StageNativeKids

open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Interfaces
open StageTuple StagePrint.Header

/-- `lem:print`, paper/paper.tex: the original occurrence decoded from the two actual bank
sizes is the occurrence selected by the original formula atom. -/
theorem role_originalIndex (r : RowContext)
    (i : Fin (17 * (Builder.allGates r.header.call).length)) :
    (finProdFinEquiv.symm (r.rolePacket i).atom).2.val =
      (r.originalIndex i).val := by
  change i.val % (r.header.call.first.gates.length + r.header.call.second.gates.length) =
    i.val % (Builder.allGates r.header.call).length
  simp only [Builder.allGates, List.length_append]

/-- `lem:print`, paper/paper.tex: concatenating the two physical banks does not change the
original seventeen-role code. -/
theorem role_code (r : RowContext)
    (i : Fin (17 * (Builder.allGates r.header.call).length)) :
    (finProdFinEquiv.symm (r.rolePacket i).atom).1 =
      (finProdFinEquiv.symm i).1 := by
  apply Fin.ext
  change i.val / (r.header.call.first.gates.length + r.header.call.second.gates.length) =
    i.val / (Builder.allGates r.header.call).length
  simp only [Builder.allGates, List.length_append]

/-- `lem:print`, paper/paper.tex: the actual role decoder emits the original occurrence
codec followed by the exact child-independent affine row header. -/
theorem role_output (r : RowContext)
    (i : Fin (17 * (Builder.allGates r.header.call).length)) :
    (r.rolePacket i).output = natWord (r.originalIndex i).val ++ r.rowHeader i := by
  simp only [RolePacket.output, RolePacket.outputValues, role_originalIndex,
    role_code, r.rolePacket_scalars i, List.flatMap_cons, List.flatMap_append,
    List.flatMap_nil, List.append_nil, List.append_assoc, RowContext.rowHeader]
  simp only [RowContext.rolePacket, r.indexedWalk_value, roleLeftSlot, roleRightSlot,
    RowContext.role, Equiv.apply_symm_apply]

/-- `prop:time`, paper/paper.tex: the
role machine's workspace is determined by the original arity, read
from the actual first affine-header field. -/
theorem role_width (r : RowContext)
    (i : Fin (17 * (Builder.allGates r.header.call).length)) :
    (r.rolePacket i).widthBound = 64 * (r.header.call.n + 1) ^ 4 := rfl

end NearQuarticWires.StageNativeKids
