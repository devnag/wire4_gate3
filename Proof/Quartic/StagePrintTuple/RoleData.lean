import Proof.Quartic.StagePrintTuple.RoleOutput

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageTuple

open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells
open StagePrint.Header

/-- `lem:print`, paper/paper.tex:
the exact output natural fields contain the selected original occurrence
and the nine literal affine metadata values in their fixed order. -/
def RolePacket.outputValues (r : RolePacket) : List ℕ :=
  (finProdFinEquiv.symm r.atom).2.val :: List.ofFn r.scalars ++
    [r.address/r.radix^(leftSlotCode (finProdFinEquiv.symm r.atom).1.val)%r.radix,
     r.address/r.radix^(rightSlotCode (finProdFinEquiv.symm r.atom).1.val)%r.radix]

/-- `lem:print`, paper/paper.tex:
the complete role result uses nine natural affine fields and three raw
corner flags after its separate original-occurrence prefix. -/
def RolePacket.output (r : RolePacket) : List Bool :=
  r.outputValues.flatMap natWord ++
    [leftCornerCode (finProdFinEquiv.symm r.atom).1.val,
     rightCornerCode (finProdFinEquiv.symm r.atom).1.val,true]

/-- `lem:print`, paper/paper.tex:
the physically decoded affine-scalar registers give exactly their
retained seven-value prefix in source order. -/
theorem baseHeader_map (r : RolePacket) (a : DS VV MM)
    (h : ∀ j : Fin 7, a.env (baseHeaderRegisters[j.val]'(by
      simp [baseHeaderRegisters])) = r.scalars j) :
    baseHeaderRegisters.map a.env = List.ofFn r.scalars := by
  apply List.ext_getElem
  · simp [baseHeaderRegisters]
  · intro i hi hj
    have hx : i < 7 := by simpa [baseHeaderRegisters] using hi
    simpa only [List.getElem_map,List.getElem_ofFn] using h ⟨i,hx⟩

/-- `lem:print`, paper/paper.tex:
the genuine role decoder's stored values are precisely the complete
scalar list emitted by the physical serializer. -/
theorem roleOutput_map (r : RolePacket) (a : DS VV MM)
    (hb : ∀ j : Fin 7, a.env (baseHeaderRegisters[j.val]'(by
      simp [baseHeaderRegisters])) = r.scalars j)
    (hi : a.env originalIndex=(finProdFinEquiv.symm r.atom).2.val)
    (hd : RoleData r.address r.radix (finProdFinEquiv.symm r.atom).1 a) :
    roleOutputFields.map a.env = r.outputValues := by
  simp only [roleOutputFields,RolePacket.outputValues,List.map_cons,List.map_append,
    List.map_nil,hi,baseHeader_map r a hb,hd.left,hd.right]

/-- `lem:print`, paper/paper.tex:
the numeric Boolean flags produced by the role decoder are the exact
raw corner bits, including the fixed transposed native orientation. -/
theorem roleOutput_flags (r : RolePacket) (a : DS VV MM)
    (hd : RoleData r.address r.radix (finProdFinEquiv.symm r.atom).1 a) :
    [decide (a.env leftCorner=1),decide (a.env rightCorner=1),decide (a.env transpose=1)] =
    [leftCornerCode (finProdFinEquiv.symm r.atom).1.val,
      rightCornerCode (finProdFinEquiv.symm r.atom).1.val,true] := by
  rw [hd.useLeft,hd.useRight,hd.transposed]
  cases leftCornerCode (finProdFinEquiv.symm r.atom).1.val <;>
    cases rightCornerCode (finProdFinEquiv.symm r.atom).1.val <;> rfl

end NearQuarticWires.StageTuple
