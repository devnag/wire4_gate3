import Proof.Quartic.StagePrint.RoleAddress

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StagePrint.Header
open NearCubicWires NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.Compiler

/-- `lem:print`, paper/paper.tex: the numeric role's left slot is an actual original walk vertex. -/
def roleLeftSlot (r : Cells.OffsetRole 4) : Fin 8 :=
  ⟨leftSlotCode (Cells.offsetIndex 4 r).val,(roleSlots_lt _).1⟩

/-- `lem:print`, paper/paper.tex: the numeric role's right slot is an actual original walk vertex. -/
def roleRightSlot (r : Cells.OffsetRole 4) : Fin 8 :=
  ⟨rightSlotCode (Cells.offsetIndex 4 r).val,(roleSlots_lt _).2⟩

/-- `lem:print`, paper/paper.tex: the literal vertex decoder uses that same original vertex and its actual side parity. -/
theorem vertex_metadata (v : Fin 8) :
    roleLeftSlot (.inl (.inr v))=v ∧ roleRightSlot (.inl (.inr v))=v ∧
      leftCornerCode (Cells.offsetIndex 4 (.inl (.inr v))).val=decide (v.val%2=0) ∧
      rightCornerCode (Cells.offsetIndex 4 (.inl (.inr v))).val=decide (v.val%2≠0) := by
  have h0 : ¬8+v.val<8:=by omega
  have h1 : 8+v.val<16:=by have:=v.isLt;omega
  have hv : 8+v.val-8=v.val:=by omega
  refine ⟨?_,?_,?_,?_⟩
  · apply Fin.ext
    change leftSlotCode (8+v.val)=v.val
    simp [leftSlotCode,h0,h1,hv]
  · apply Fin.ext
    change rightSlotCode (8+v.val)=v.val
    simp [rightSlotCode,h0,h1,hv]
  · change leftCornerCode (8+v.val)=_
    simp [leftCornerCode,h0,h1,hv]
  · change rightCornerCode (8+v.val)=_
    simp [rightCornerCode,h0,h1,hv]

/-- `imp:pullback` and `lem:print`, paper/paper.tex: the physical numeric metadata determines the literal original-coordinate star point. -/
def numericRolePoint (P : StarParams) (w : Fin 8→P.Errors) (r : Cells.OffsetRole 4)
    (c : BitInput P.n) : BitInput P.n := fun x=>
  xor (xor (c x) (leftCornerCode (Cells.offsetIndex 4 r).val &&
    P.errorVector P.leftBlock (w (roleLeftSlot r)) x))
    (rightCornerCode (Cells.offsetIndex 4 r).val &&
      P.errorVector P.rightBlock (w (roleRightSlot r)) x)

/-- `imp:pullback` and `lem:print`, paper/paper.tex: every edge, every vertex and the center computed by the numeric role program is exactly the pooled Boolean atom's ORIGINAL point, including the unused center patterns. -/
theorem numericRolePoint_eq (P : StarParams) (w : Fin 8→P.Errors) (r : Cells.OffsetRole 4)
    (c : BitInput P.n) :
    numericRolePoint P w r c=(Cells.roleCoords P (by decide : 0<4) w r).point
      (P.leftPart c) (P.rightPart c) := by
  rcases r with (e|v)|z
  · have hslots:=edge_slots e
    have hl : roleLeftSlot (.inl (.inl e))=Cells.leftSlot (by decide : 0<4) e:=Fin.ext hslots.1
    have hr : roleRightSlot (.inl (.inl e))=Cells.rightSlot (by decide : 0<4) e:=Fin.ext hslots.2
    change numericRolePoint P w (.inl (.inl e)) c=
      (starCoords P (w (Cells.leftSlot (by decide : 0<4) e))
        (w (Cells.rightSlot (by decide : 0<4) e)) true true).point (P.leftPart c) (P.rightPart c)
    rw [starCoords_point]
    have hul : leftCornerCode (Cells.offsetIndex 4 (.inl (.inl e))).val=true := by
      change leftCornerCode e.val=true
      simp [leftCornerCode,e.isLt]
    have hur : rightCornerCode (Cells.offsetIndex 4 (.inl (.inl e))).val=true := by
      change rightCornerCode e.val=true
      simp [rightCornerCode,e.isLt]
    funext x
    simp only [numericRolePoint,hl,hr,hul,hur,Bool.true_and]
  · obtain ⟨hl,hr,hul,hur⟩:=vertex_metadata v
    change numericRolePoint P w (.inl (.inr v)) c=
      (starCoords P (w v) (w v) (decide (v.val%2=0)) (decide (v.val%2≠0))).point
        (P.leftPart c) (P.rightPart c)
    rw [starCoords_point]
    funext x
    simp only [numericRolePoint,hl,hr,hul,hur]
  · have hz : z=(0 : Fin 1):=Subsingleton.elim _ _
    subst hz
    change numericRolePoint P w (.inr 0) c=
      (starCoords P (fun _=>none) (fun _=>none) false false).point (P.leftPart c) (P.rightPart c)
    rw [starCoords_point]
    have hul : leftCornerCode (Cells.offsetIndex 4 (.inr 0)).val=false:=by decide
    have hur : rightCornerCode (Cells.offsetIndex 4 (.inr 0)).val=false:=by decide
    funext x
    simp only [numericRolePoint,hul,hur,Bool.false_and,Bool.xor_false]

end NearQuarticWires.StagePrint.Header
