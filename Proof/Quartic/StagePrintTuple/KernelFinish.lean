import Proof.Quartic.StagePrintTuple.KernelCartesian
import Proof.Quartic.StagePrintTuple.NativeCleanup

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageTuple

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicGates.Close.TabMachine NearCubicGates.Close.WordPrograms NearCubicGates.Close.CheckedPCPP
open NearQuarticWires.Control

/-- `lem:print` and `prop:time`, paper/paper.tex: after the actual Cartesian call, genuine register
arithmetic updates the tuple product and row stride, then measured
finite erasure restores all native and selected-atom caches. -/
theorem kernelFinish_run (r : TermCutRequest)
    (data : MonomialData (17*(Builder.allGates r.header.call).length))
    (span done cap : ℕ) (hd : done<data.order.length)
    (hproduct :
      (r.toRowContext.nativeKids data.order[(reverseSupportIndex data.order done hd).val]).length*
      (tupleFields r.toRowContext.nativeKids (processedSupport data.order done)).length ≤ cap)
    (hdouble : 2*(r.toRowContext.nativeKids
      data.order[(reverseSupportIndex data.order done hd).val]).length ≤ cap)
    (hold : (tupleFields r.toRowContext.nativeKids (processedSupport data.order done)).length ≤ cap)
    (hstride : (done+1)*(r.rowDimension+1) ≤ cap)
    (hframe :
      (frame (nativePhasePayload (StageNativeKids.NativeKidsRequest.ofTerm r
        data.order[(reverseSupportIndex data.order done hd).val]))).length ≤ cap)
    (hraw :
      (nativePhasePayload (StageNativeKids.NativeKidsRequest.ofTerm r
        data.order[(reverseSupportIndex data.order done hd).val])).length ≤ cap)
    (hatom : (frame (finiteSupportRequest data.order
      (reverseSupportIndex data.order done hd)).output).length ≤ cap) :
    let i := data.order[(reverseSupportIndex data.order done hd).val]
    let req := StageNativeKids.NativeKidsRequest.ofTerm r i
    let tr := r.toRowContext.tupleStepRequest (r.stackWidth+1) (by omega)
      i (processedSupport data.order done)
    let q := finiteSupportRequest data.order (reverseSupportIndex data.order done hd)
    let σ0 := ((data.reverseState r span done).setv 15 (data.order.length-(done+1))).sets
      (kernelLocal span 17) (frame q.output)
    let σ1 := nativePhaseState span req σ0
    let σ := closedHistory σ1 (kernelLocal span 20) 0 (σ1.st (kernelLocal span 20))
      ((tupleRecords tr).flatMap frame)
    let σ' := ((σ.setv 14 (tr.children.length*tr.tuples.length)).setv 13 0).setv
      12 (done*(r.rowDimension+1)+(r.rowDimension+1))
    ∃τ,WXExec cap (.seq (tupleCounterProgram kernelCounterRegisters) (nativeCleanupProgram span)) σ τ
      (100*(tr.children.length*tr.tuples.length+tr.children.length+tr.tuples.length+
        (r.rowDimension+1)+1)+1+
        nativeCleanupCost q.output (natWord tr.children.length) (fieldRecords tr.L tr.children)) ∧
      SimW (nativeCleanupState span σ') τ := by
  let i := data.order[(reverseSupportIndex data.order done hd).val]
  let req := StageNativeKids.NativeKidsRequest.ofTerm r i
  let tr := r.toRowContext.tupleStepRequest (r.stackWidth+1) (by omega)
    i (processedSupport data.order done)
  let q := finiteSupportRequest data.order (reverseSupportIndex data.order done hd)
  let σ0 := ((data.reverseState r span done).setv 15 (data.order.length-(done+1))).sets
    (kernelLocal span 17) (frame q.output)
  let σ1 := nativePhaseState span req σ0
  let σ := closedHistory σ1 (kernelLocal span 20) 0 (σ1.st (kernelLocal span 20))
    ((tupleRecords tr).flatMap frame)
  have e := tupleCounterProgram_spec cap kernelCounterRegisters tr.children.length tr.tuples.length
    (done*(r.rowDimension+1)) (r.rowDimension+1) σ
    (by simp [σ,σ1,σ0,nativePhaseState,closedHistory,kernelCounterRegisters,req,
      StageNativeKids.NativeKidsRequest.ofTerm,tr,RowContext.tupleStepRequest])
    (by simp [σ,σ1,σ0,nativePhaseState,closedHistory,kernelCounterRegisters,tr,
      RowContext.tupleStepRequest,MonomialData.reverseState,MonomialData.reverseData,KernelData.state])
    (by simp [σ,σ1,σ0,nativePhaseState,closedHistory,kernelCounterRegisters,
      MonomialData.reverseState,MonomialData.reverseData,KernelData.state])
    (by simp [σ,σ1,σ0,nativePhaseState,closedHistory,kernelCounterRegisters,
      MonomialData.reverseState,MonomialData.reverseData,KernelData.state])
    (by simp [σ,σ1,σ0,nativePhaseState,closedHistory,kernelCounterRegisters,
      MonomialData.reverseState,MonomialData.reverseData,KernelData.state])
    (by simp [σ,σ1,σ0,nativePhaseState,closedHistory,kernelCounterRegisters,
      MonomialData.reverseState,MonomialData.reverseData,KernelData.state])
    (by simp [σ,σ1,σ0,nativePhaseState,closedHistory,kernelCounterRegisters,
      MonomialData.reverseState,MonomialData.reverseData,KernelData.state])
    hproduct hdouble hold (by simpa only [Nat.add_mul,Nat.one_mul] using hstride)
  let σ' := ((σ.setv 14 (tr.children.length*tr.tuples.length)).setv 13 0).setv
    12 (done*(r.rowDimension+1)+(r.rowDimension+1))
  have e' : WXExec cap (tupleCounterProgram kernelCounterRegisters) σ σ'
      (100*(tr.children.length*tr.tuples.length+tr.children.length+tr.tuples.length+
        (r.rowDimension+1)+1)) := by
    simpa [σ',kernelCounterRegisters] using e
  obtain ⟨b,eb,hb⟩ := nativeCleanupProgram_spec span cap q.output (natWord tr.children.length)
    (fieldRecords tr.L tr.children) (fieldRecords_nonempty tr.L tr.width_pos _) σ'
    (by simp [σ',σ,σ1,σ0,nativePhaseState,closedHistory,kernelLocal])
    (by simp [σ',σ,σ1,σ0,nativePhaseState,closedHistory,kernelLocal,
      MonomialData.reverseState,MonomialData.reverseData,KernelData.state])
    (by simp [σ',σ,σ1,nativePhaseState,nativePhasePayload,closedHistory,kernelLocal,req,
      StageNativeKids.NativeKidsRequest.ofTerm,tr,RowContext.tupleStepRequest,fieldsRecs_eq_records])
    (by simp [σ',σ,σ1,nativePhaseState,nativePhasePayload,closedHistory,kernelLocal,req,
      StageNativeKids.NativeKidsRequest.ofTerm,tr,RowContext.tupleStepRequest,fieldsRecs_eq_records])
    (by simp [σ',σ,σ1,nativePhaseState,nativePhasePayload,closedHistory,kernelLocal,req,
      StageNativeKids.NativeKidsRequest.ofTerm,tr,RowContext.tupleStepRequest,fieldsRecs_eq_records])
    (by simp [σ',σ,σ1,nativePhaseState,closedHistory,kernelLocal,req,
      StageNativeKids.NativeKidsRequest.ofTerm,tr,RowContext.tupleStepRequest])
    (by simp [σ',σ,σ1,σ0,nativePhaseState,closedHistory,kernelLocal,
      MonomialData.reverseState,MonomialData.reverseData,KernelData.state])
    (by simp [σ',σ,σ1,σ0,nativePhaseState,closedHistory,kernelLocal,
      MonomialData.reverseState,MonomialData.reverseData,KernelData.state])
    (by simp [σ',σ,closedHistory])
    (by simp [σ',σ,σ1,σ0,nativePhaseState,closedHistory,
      MonomialData.reverseState,MonomialData.reverseData,KernelData.state])
    (by simp [σ',σ,σ1,nativePhaseState,nativePhasePayload,closedHistory,req,
      StageNativeKids.NativeKidsRequest.ofTerm,tr,RowContext.tupleStepRequest,fieldsRecs_eq_records])
    (by simp [σ',σ,σ1,nativePhaseState,nativePhasePayload,closedHistory,req,
      StageNativeKids.NativeKidsRequest.ofTerm,tr,RowContext.tupleStepRequest,fieldsRecs_eq_records])
    (by simpa only [tr,i,RowContext.tupleStepRequest,nativePhasePayload,
      StageNativeKids.NativeKidsRequest.ofTerm,fieldsRecs_eq_records] using hframe)
    (by simpa only [tr,i,RowContext.tupleStepRequest,nativePhasePayload,
      StageNativeKids.NativeKidsRequest.ofTerm,fieldsRecs_eq_records] using hraw) hatom
  exact ⟨b,e'.seq eb,hb⟩

end NearQuarticWires.StageTuple
