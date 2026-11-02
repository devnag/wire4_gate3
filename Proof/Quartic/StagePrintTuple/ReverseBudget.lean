import Proof.Quartic.StagePrintTuple.KernelReverseProgram
import Proof.Quartic.StagePrintTuple.ReverseState

set_option autoImplicit false

namespace NearQuarticWires.StageTuple

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.WireExponent3_5.FinalPass.Tm

/-- `prop:time`, paper/paper.tex: one reverse
iteration's capacity is a sum of actual small input, reply, call and
tuple arithmetic bounds. It is an analysis bound, not a runtime field. -/
def reverseStepCapacity (B : StageNativeKids.NativeKidsRequest→ℕ)
    (r : TermCutRequest)
    (data : MonomialData (17*(Builder.allGates r.header.call).length))
    (done : ℕ) (hd : done<data.order.length) : ℕ :=
  let i := data.order[(reverseSupportIndex data.order done hd).val]
  let req := StageNativeKids.NativeKidsRequest.ofTerm r i
  let tr := r.toRowContext.tupleStepRequest (r.stackWidth+1) (by omega)
    i (processedSupport data.order done)
  let q := finiteSupportRequest data.order (reverseSupportIndex data.order done hd)
  1000*supportInputMagnitude q+
    (2*q.word.length+2+q.budget)+((frame q.output).length+1)+
    10000*nativePhaseMagnitude B req+
    (400*((fieldRecords tr.L tr.children).flatMap frame).length+
      400*((fieldRecords tr.L tr.tuples).flatMap frame).length+
      400*(tr.N+tr.M+tr.children.length+tr.tuples.length+10))+
    (2*tr.word.length+2+(2*tr.budget+2))+(((tupleRecords tr).flatMap frame).length+1)+
    tr.children.length*tr.tuples.length+2*tr.children.length+tr.tuples.length+
    (done+1)*(r.rowDimension+1)+
    (frame (nativePhasePayload req)).length+(nativePhasePayload req).length+(frame q.output).length

/-- `prop:time`, paper/paper.tex: an iteration
pays each actual stage and all four sequence transitions, retaining the
native pool and partial tuple census as separate additive stages. -/
def reverseStepCost (B : StageNativeKids.NativeKidsRequest→ℕ)
    (r : TermCutRequest)
    (data : MonomialData (17*(Builder.allGates r.header.call).length))
    (done : ℕ) (hd : done<data.order.length) : ℕ :=
  let i := data.order[(reverseSupportIndex data.order done hd).val]
  let req := StageNativeKids.NativeKidsRequest.ofTerm r i
  let tr := r.toRowContext.tupleStepRequest (r.stackWidth+1) (by omega)
    i (processedSupport data.order done)
  let q := finiteSupportRequest data.order (reverseSupportIndex data.order done hd)
  supportPhaseCost q+1+(1000000*nativePhaseMagnitude B req+1+
    (cartesianStepCost tr+1+
      (100*(tr.children.length*tr.tuples.length+tr.children.length+tr.tuples.length+
        (r.rowDimension+1)+1)+1+
        nativeCleanupCost q.output (natWord tr.children.length) (fieldRecords tr.L tr.children))))

end NearQuarticWires.StageTuple
