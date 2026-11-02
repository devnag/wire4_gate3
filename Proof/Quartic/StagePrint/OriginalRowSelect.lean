import Proof.Quartic.StagePrint.BitRecordSelect
import Proof.Quartic.StagePrint.FramedOriginalChildren

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace NearQuarticWires.StagePrint
open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.TabMachine

/-- `lem:print`, paper/paper.tex: selecting an original disjoint child preserves the compiler's complete fixed-width record. -/
def originalRowRequest (r : OriginalChildRequest) (j : Fin (compileL r.weights r.target).length) :
    BitRecordSelectRequest where
  L:=(r.weights.length+1)*(r.W+1)
  records:=(compileL r.weights r.target).map (recBits r.W)
  index:=⟨j.val,by simpa using j.isLt⟩
  width_pos:=by nlinarith
  record_length:=by
    intro row hrow
    obtain ⟨c,hc,rfl⟩:=List.mem_map.mp hrow
    unfold recBits
    rw [List.length_flatMap]
    simp only [SignedSortKey.binary_length,List.map_const',List.sum_replicate,smul_eq_mul]
    rw [compileL_length _ _ c hc]

/-- `lem:print`, paper/paper.tex: the selector source is exactly the actual original child stream with its final record delimiter. -/
theorem originalRowRequest_word (r : OriginalChildRequest) (j : Fin (compileL r.weights r.target).length) :
    (originalRowRequest r j).word=Top.loadRec (r.output++[false])
      (List.replicate j.val true) [] [] [] [] [] [] [] [] [] := by
  unfold BitRecordSelectRequest.word originalRowRequest OriginalChildRequest.output compRecs recStream
  simp only [List.flatMap_map]

/-- `lem:print`, paper/paper.tex: the selected output is the original fixed signed row, before all affine pullback arithmetic. -/
theorem originalRowRequest_output (r : OriginalChildRequest) (j : Fin (compileL r.weights r.target).length) :
    (originalRowRequest r j).records[(originalRowRequest r j).index.val]=
      recBits r.W (compileL r.weights r.target)[j.val] := by
  simp [originalRowRequest]

/-- `lem:print`, paper/paper.tex: the actual serialized original-child list supports a cold exact row selector. -/
noncomputable def originalRowSelector :
    WordFunction (Σr : OriginalChildRequest,Fin (compileL r.weights r.target).length)
      (fun r=>(originalRowRequest r.1 r.2).word)
      (fun r=>frame (recBits r.1.W (compileL r.1.weights r.1.target)[r.2.val]))
      (fun r=>2*(originalRowRequest r.1 r.2).lower.budget+2) :=
  ⟨bitRecordSelector.program,by
    rintro ⟨r,j⟩
    simpa only [originalRowRequest_output] using bitRecordSelector.realizes (originalRowRequest r j)⟩

end NearQuarticWires.StagePrint
