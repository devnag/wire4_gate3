import Proof.Quartic.StageTupleMonomialFinish.KernelReset
import Proof.Quartic.Control.GammaControl

set_option autoImplicit false

namespace NearQuarticWires.StageTupleMonomialFinish

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Interfaces
open StageTuple

/-- `prop:time`, paper/paper.tex: every actual
Stack output byte is paid by the genuine ordinary Stack clock, even
when the coefficient or tuple list yields an empty cut stream. -/
theorem stack_output_length (sr : StagePrint.StackRequest) :
    sr.output.length≤2*sr.budget+3 := by
  have h:=Control.output_length_le stackRecordPrinter sr
  simpa only [←stack_output_records] using h

/-- `prop:time`, paper/paper.tex: all finite
cache erasure clocks are linear in the three actual cached words. -/
theorem kernelCachesCost_le (r : TermCutRequest)
    (data : MonomialData (17*(Builder.allGates r.header.call).length)) :
    kernelCachesCost r data≤200*(
      ((data.reverseData r data.order.length).caches 0).length+
      ((data.reverseData r data.order.length).caches 1).length+
      ((data.reverseData r data.order.length).caches 2).length+1) := by
  have htail : (frame ((data.order.map Fin.val).flatMap natWord)).length≤
      (frame (listWord natWord (data.order.map Fin.val))).length := by
    rw [support_frame]
    simp only [List.length_append]
    omega
  unfold kernelCachesCost cachesCost
  rw [←support_frame]
  change 60*((frame (CoefficientRequest.word ⟨r.stackWidth+1,data.coefficient⟩)).length+1)+
    60*((CoefficientRequest.output ⟨r.stackWidth+1,data.coefficient⟩).length+1)+
    40*((frame ((data.order.map Fin.val).flatMap natWord)).length+1)+
    10*(frame (listWord natWord (data.order.map Fin.val))).length+4≤
      200*((frame (listWord natWord (data.order.map Fin.val))).length+
        (frame (CoefficientRequest.word ⟨r.stackWidth+1,data.coefficient⟩)).length+
        (CoefficientRequest.output ⟨r.stackWidth+1,data.coefficient⟩).length+1)
  omega

/-- `prop:time`, paper/paper.tex: the complete
actual post-reverse clock fits the fixed linear finish magnitude,
without any earlier output or tuple-history length. -/
theorem finishCost_le (r : TermCutRequest)
    (data : MonomialData (17*(Builder.allGates r.header.call).length))
    (t : Finset (Fin (17*(Builder.allGates r.header.call).length))×ℤ) (ht : t∈r.terms) :
    stackPhaseCost (r.stackRequest t ht)+1+(kernelCachesCost r data+1+
      resetCost (r.stackRequest t ht))≤100000000*monomialFinishMagnitude r data t ht := by
  have hc:=kernelCachesCost_le r data
  have hr : resetCost (r.stackRequest t ht)≤300*stackInputMagnitude (r.stackRequest t ht) := by
    unfold resetCost stackInputMagnitude
    omega
  unfold stackPhaseCost callRecordsCost monomialFinishMagnitude
  dsimp only
  omega

/-- `prop:time`, paper/paper.tex: the actual
Stack input, output and finite reset counters fit the frozen capacity;
prior output bytes occur only in the append capacity, never its clock. -/
theorem finish_capacity (r : TermCutRequest)
    (data : MonomialData (17*(Builder.allGates r.header.call).length))
    (t : Finset (Fin (17*(Builder.allGates r.header.call).length))×ℤ) (ht : t∈r.terms)
    (cap : ℕ) (hcap : 100000000*(monomialFinishMagnitude r data t ht+data.output.length+1)≤cap) :
    400*stackInputMagnitude (r.stackRequest t ht)≤cap ∧
    2*(r.stackRequest t ht).word.length+2+(2*(r.stackRequest t ht).budget+2)≤cap ∧
    data.output.length+(r.stackRequest t ht).output.length+1≤cap ∧
    ((data.reverseData r data.order.length).caches 1).length≤cap ∧
    ((data.reverseData r data.order.length).caches 2).length≤cap ∧
    ((data.reverseData r data.order.length).caches 0).length≤cap ∧
    (r.stackRequest t ht).m*((r.stackRequest t ht).s+1)+
      (r.stackRequest t ht).tuples.length+(r.stackRequest t ht).m≤cap ∧
    ((fieldRecords ((r.stackRequest t ht).W+1)
      ((r.stackRequest t ht).tuples.map List.flatten)).flatMap frame).length+1≤cap := by
  have ho:=stack_output_length (r.stackRequest t ht)
  have hi : (r.stackRequest t ht).m*((r.stackRequest t ht).s+1)+
      (r.stackRequest t ht).tuples.length+(r.stackRequest t ht).m+
      ((fieldRecords ((r.stackRequest t ht).W+1)
        ((r.stackRequest t ht).tuples.map List.flatten)).flatMap frame).length+1≤
      stackInputMagnitude (r.stackRequest t ht) := by
    unfold stackInputMagnitude
    omega
  unfold monomialFinishMagnitude at hcap
  dsimp only at hcap
  omega

end NearQuarticWires.StageTupleMonomialFinish
