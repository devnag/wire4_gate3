import Proof.Quartic.StageEqualityRows.Naturals
import Proof.Quartic.StageEqualityRows.RawNaturals

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageEqualityRows

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey
open NearCubicWires.RepairRepresentation NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open StagePrint

def weakStream (r : NativeStreamRequest) : List Bool :=
  (EquationRow.doubled false r.cuts).flatMap (MatrixScoreBatch.cutWord (r.fieldWidth+1))
def temporaryColumns (r : NativeStreamRequest) : List (List Bool) :=
  (List.range (width r)).map (fun j=>binary (width r) (2^j))
def temporaryNaturals (r : NativeStreamRequest) : List ℕ :=
  [width r,r.fieldWidth+1,2*r.cuts.length,width r]
def temporaryWord (r : NativeStreamRequest) : List Bool :=
  MatrixScoreBatch.word (EquationRow.request r.equalityInput)
def stripCapacity (r : NativeStreamRequest) : ℕ := capacity r+100*(width r+1)^2

/-- `lem:print`, paper/paper.tex: the temporary
constructor header consists of four genuine encoded naturals and its
actual framed columns, followed by the unchanged two-cut body. -/
theorem temporaryWord_shape (r : NativeStreamRequest) :
    temporaryWord r=(temporaryNaturals r).flatMap natWord++
      (temporaryColumns r).flatMap frame++weakStream r := by
  simp [temporaryWord,temporaryNaturals,temporaryColumns,weakStream,MatrixScoreBatch.word,
    MatrixScoreBatch.header,MatrixScoreBatch.Request.Gates,MatrixScoreBatch.Request.cols,
    EquationRow.request,NativeStreamRequest.equalityInput,EquationRow.doubled_length,
    MatrixScorePhi.columnsWord,List.flatMap_map,width,List.append_assoc]

/-- `lem:print`, paper/paper.tex: each actual
output field has one additional signed magnitude bit. -/
theorem weakStream_length (r : NativeStreamRequest) :
    (weakStream r).length=2*r.cuts.length*((2*width r+2)*(2*r.fieldWidth+5)) := by
  change (r.matrix.cuts.flatMap (MatrixScoreBatch.cutWord r.matrix.p)).length=_
  rw [List.length_flatMap]
  have h : r.matrix.cuts.map (fun c=>(MatrixScoreBatch.cutWord r.matrix.p c).length)=
      r.matrix.cuts.map (fun _=>(2*width r+2)*(2*r.fieldWidth+5)) := by
    apply List.map_congr_left
    intro c hc
    have he:=MatrixScoreBatch.cutWord_length r.matrix c hc
    simpa [NativeStreamRequest.matrix,width,Nat.mul_add,Nat.add_assoc] using he
  rw [h]
  simp [NativeStreamRequest.matrix_cuts_length]

/-- `prop:time`, paper/paper.tex: the complete
weak body remains linear in this same walk's equality stream. -/
theorem weakStream_le (r : NativeStreamRequest) : (weakStream r).length≤4*(stream r).length := by
  calc
    (weakStream r).length=r.cuts.length*(2*width r+2)*(2*(2*r.fieldWidth+5)) := by
      rw [weakStream_length];ring
    _≤r.cuts.length*(2*width r+2)*(4*(2*r.fieldWidth+3)) :=
      Nat.mul_le_mul_left _ (by omega)
    _=4*(stream r).length := by rw [stream_length];ring

theorem temporaryColumns_length (r : NativeStreamRequest) : (temporaryColumns r).length=width r := by
  simp [temporaryColumns]

theorem temporaryColumns_bitLength (r : NativeStreamRequest) :
    ∀ col∈temporaryColumns r,col.length=width r := by
  intro col hc
  obtain ⟨j,hj,rfl⟩:=List.mem_map.mp hc
  simp

end NearQuarticWires.StageEqualityRows
