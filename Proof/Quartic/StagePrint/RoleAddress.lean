import Proof.Quartic.Cells.Atoms

set_option autoImplicit false

namespace NearQuarticWires.StagePrint.Header
open NearCubicWires.WireExponent3_5.Shared

/-- `lem:print`, paper/paper.tex: the row-pattern slot selected by a literal edge, vertex or center offset. -/
def leftSlotCode (r : ℕ) : ℕ :=
  if r<8 then (if r%2=0 then r else (r+1)%8) else if r<16 then r-8 else 0

/-- `lem:print`, paper/paper.tex: the column-pattern slot selected by the same offset. -/
def rightSlotCode (r : ℕ) : ℕ :=
  if r<8 then (if r%2=0 then (r+1)%8 else r) else if r<16 then r-8 else 0

/-- `lem:print`, paper/paper.tex: an edge uses the left error, an even vertex uses only that error, and the center uses neither error. -/
def leftCornerCode (r : ℕ) : Bool :=decide (r<8 ∨ r<16 ∧ (r-8)%2=0)

/-- `lem:print`, paper/paper.tex: an edge uses the right error, an odd vertex uses only that error, and the center uses neither error. -/
def rightCornerCode (r : ℕ) : Bool :=decide (r<8 ∨ r<16 ∧ (r-8)%2≠0)

/-- `lem:print`, paper/paper.tex: every physically selected pattern slot belongs to the actual eight-step closed walk. -/
theorem roleSlots_lt (r : ℕ) : leftSlotCode r<8 ∧ rightSlotCode r<8 := by
  have hm : (r+1)%8<8:=Nat.mod_lt _ (by decide)
  unfold leftSlotCode rightSlotCode
  split_ifs <;> omega

/-- `lem:print`, paper/paper.tex: edge roles occupy the first eight actual pool offsets. -/
theorem offset_edge_value (e : Fin 8) :
    (Cells.offsetIndex 4 (.inl (.inl e))).val=e.val := rfl

/-- `lem:print`, paper/paper.tex: vertex roles occupy the next eight actual pool offsets. -/
theorem offset_vertex_value (v : Fin 8) :
    (Cells.offsetIndex 4 (.inl (.inr v))).val=8+v.val := rfl

/-- `lem:print`, paper/paper.tex: the sole center role is the seventeenth actual pool offset. -/
theorem offset_center_value :
    (Cells.offsetIndex 4 (.inr 0)).val=16 := rfl

/-- `lem:print`, paper/paper.tex: the numeric role decoder has exactly the row and column walk slots of the actual edge geometry. -/
theorem edge_slots (e : Fin 8) :
    leftSlotCode (Cells.offsetIndex 4 (.inl (.inl e))).val=(Cells.leftSlot (by decide : 0<4) e).val ∧
    rightSlotCode (Cells.offsetIndex 4 (.inl (.inl e))).val=(Cells.rightSlot (by decide : 0<4) e).val := by
  rw [offset_edge_value]
  simp only [leftSlotCode,rightSlotCode,if_pos e.isLt,Cells.leftSlot,Cells.rightSlot,nextSlot]
  split_ifs <;> constructor <;> rfl

end NearQuarticWires.StagePrint.Header
