import Proof.Quartic.StagePrintTuple.ReverseState
import Proof.Quartic.StagePrintTuple.KernelTransition

set_option autoImplicit false

namespace NearQuarticWires.StageTuple

open NearCubicGates.Close.TabMachine

/-- `lem:print`, paper/paper.tex: decrementing
the real reverse counter and prepending the selected original child
pool gives exactly the next suffix-tuple boundary, with the full old
history retained once and no reordering of child choices. -/
theorem MonomialData.reverseData_succ (r : TermCutRequest)
    (data : MonomialData (17*(Builder.allGates r.header.call).length))
    (done : ℕ) (hd : done<data.order.length) :
    let i := data.order[(reverseSupportIndex data.order done hd).val]
    data.reverseData r (done+1)=
      ({data.reverseData r done with reverseIndex := data.order.length-(done+1)}).nextCartesian
        (fieldsRecs (r.stackWidth+1)
          (tupleFields r.toRowContext.nativeKids (processedSupport data.order (done+1))))
        (r.toRowContext.nativeKids i).length (r.rowDimension+1) := by
  dsimp only
  have hhist := tupleHistory_succ (r.stackWidth+1) r.toRowContext.nativeKids data.order done
  have hpref : tupleHistoryPrefix (r.stackWidth+1) r.toRowContext.nativeKids data.order (done+1)=
      tupleHistory (r.stackWidth+1) r.toRowContext.nativeKids data.order done := rfl
  have hcount := r.toRowContext.tupleStepRequest_count (r.stackWidth+1) (by omega)
    data.order[(reverseSupportIndex data.order done hd).val] (processedSupport data.order done)
  rw [←reverseSupportIndex_suffix data.order done hd] at hcount
  simp only [RowContext.tupleStepRequest] at hcount
  simp only [MonomialData.reverseData,KernelData.nextCartesian,KernelData.mk.injEq]
  refine ⟨by trivial,by trivial,by trivial,by trivial,?_,?_,by trivial,?_,by trivial,hcount,by trivial,by trivial⟩
  · simp only [hhist,tupleSegment,List.append_assoc]
  · rw [hpref,List.length_append]
  · ring

end NearQuarticWires.StageTuple
