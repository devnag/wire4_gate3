import Proof.Quartic.StagePrintTuple.MonomialFinishContract

set_option autoImplicit false

namespace NearQuarticWires.StageTupleMonomialFinish

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.TabMachine
open StageTuple

/-- `lem:print`, paper/paper.tex: the completed
reverse support stream is exactly the flattened original Stack tuple
list, with the original ascending support order. -/
theorem complete_tuple_fields (r : TermCutRequest)
    (data : MonomialData (17*(Builder.allGates r.header.call).length))
    (t : Finset (Fin (17*(Builder.allGates r.header.call).length))×ℤ)
    (ht : t∈r.terms) (horder : data.order=t.1.sort (·≤·)) :
    tupleFields r.toRowContext.nativeKids (processedSupport data.order data.order.length)=
      (r.stackRequest t ht).tuples.map List.flatten := by
  rw [processedSupport_complete,horder]
  rfl

/-- `lem:print`, paper/paper.tex: the prefix
before the final tuple segment contains only retained earlier history;
its length is a cursor position, never a finish-loop runtime. -/
def finalHistoryPrefix (r : TermCutRequest)
    (data : MonomialData (17*(Builder.allGates r.header.call).length)) : List Bool :=
  data.historyPrefix++tupleHistoryPrefix (r.stackWidth+1) r.toRowContext.nativeKids
    data.order data.order.length

/-- `lem:print`, paper/paper.tex: the actual
history tape contains the final signed tuple fields followed by its
real delimiter, after the unchanged earlier history prefix. -/
theorem complete_history (r : TermCutRequest)
    (data : MonomialData (17*(Builder.allGates r.header.call).length))
    (t : Finset (Fin (17*(Builder.allGates r.header.call).length))×ℤ)
    (ht : t∈r.terms) (horder : data.order=t.1.sort (·≤·)) (span : ℕ) :
    (data.reverseState r span data.order.length).st (kernelLocal span 20)=
      finalHistoryPrefix r data++
        (fieldRecords ((r.stackRequest t ht).W+1)
          ((r.stackRequest t ht).tuples.map List.flatten)).flatMap frame++[false] := by
  simp [MonomialData.reverseState,KernelData.state,kernelLocal,
    MonomialData.reverseData,tupleHistory_eq,tupleSegment,fieldsRecs_eq_records,
    complete_tuple_fields r data t ht horder,finalHistoryPrefix,
    TermCutRequest.stackRequest,List.append_assoc]

/-- `lem:print`, paper/paper.tex: the final
history cursor is the actual retained-prefix length produced by the
reverse loop. -/
theorem complete_history_head (r : TermCutRequest)
    (data : MonomialData (17*(Builder.allGates r.header.call).length)) (span : ℕ) :
    (data.reverseState r span data.order.length).sh (kernelLocal span 20)=
      (finalHistoryPrefix r data).length := by
  simp [MonomialData.reverseState,KernelData.state,MonomialData.reverseData,
    kernelLocal,finalHistoryPrefix]

end NearQuarticWires.StageTupleMonomialFinish
