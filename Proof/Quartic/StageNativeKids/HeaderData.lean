import Proof.Quartic.StageNativeKids.RoleValid
import Proof.Quartic.StageNativeKids.AcquiredWord

set_option autoImplicit false

namespace NearQuarticWires.StageNativeKids

open NearCubicWires NearCubicWires.RepairRepresentation
open StageTuple StagePrint.Header

/-- `lem:print`, paper/paper.tex: the
nine actual affine-header natural fields retain the original geometry,
translation and the two canonically selected binary walk coordinates. -/
def NativeKidsRequest.headerNaturals (r : NativeKidsRequest) : List ℕ :=
  baseHeaderValues r.header ++
    [(StagePrint.indexedWalk r.header.prepared.seedParameters.N r.walkCode
        (roleLeftSlot (r.toRowContext.role r.atom))).val,
     (StagePrint.indexedWalk r.header.prepared.seedParameters.N r.walkCode
        (roleRightSlot (r.toRowContext.role r.atom))).val]

/-- `lem:print`, paper/paper.tex: the
actual raw flags select the two corners and the fixed transposed native
orientation, independently of whether the original child pool is empty. -/
def NativeKidsRequest.headerFlags (r : NativeKidsRequest) : List Bool :=
  [leftCornerCode (finProdFinEquiv.symm r.atom).1.val,
    rightCornerCode (finProdFinEquiv.symm r.atom).1.val, true]

/-- `lem:print`, paper/paper.tex: exactly
nine affine natural fields are copied in binary for every original row. -/
theorem headerNaturals_length (r : NativeKidsRequest) : r.headerNaturals.length = 9 := by
  simp [NativeKidsRequest.headerNaturals, baseHeaderValues]

/-- `lem:print`, paper/paper.tex: exactly
three original raw flags follow the nine affine natural fields. -/
theorem headerFlags_length (r : NativeKidsRequest) : r.headerFlags.length = 3 := rfl

/-- `lem:print`, paper/paper.tex: the
copied natural fields and raw flags are exactly the original retained
row header, with no new decoded corner or selected point premise. -/
theorem rowHeader_bytes (r : NativeKidsRequest) :
    r.toRowContext.rowHeader r.atom = r.headerNaturals.flatMap natWord ++ r.headerFlags := by
  simp only [RowContext.rowHeader, NativeKidsRequest.headerNaturals,
    NativeKidsRequest.headerFlags, List.flatMap_append, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.append_assoc]

/-- `lem:print`, paper/paper.tex: after
reading the computed original occurrence, the actual role source suffix
is the complete nine-field, three-flag affine row header. -/
theorem rolePayload_bytes (r : NativeKidsRequest) :
    r.rolePayload = natWord (r.toRowContext.originalIndex r.atom).val ++
      r.headerNaturals.flatMap natWord ++ r.headerFlags := by
  simp only [NativeKidsRequest.rolePayload, rowHeader_bytes, List.append_assoc]

end NearQuarticWires.StageNativeKids
