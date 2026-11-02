import Proof.Quartic.StagePrintTuple.KernelNative
import Proof.Quartic.StagePrintTuple.NativeBlank

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageTuple

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicGates.Close.TabMachine NearCubicGates.Close.WordPrograms
open NearQuarticWires.Control

/-- `lem:print`, paper/paper.tex: the actual
Cartesian call receives the genuine current native pool and processed
suffix tuple segment directly from the reverse-loop tapes. -/
theorem kernelCartesian_run (r : TermCutRequest)
    (data : MonomialData (17*(Builder.allGates r.header.call).length))
    (span done cap : ℕ) (hd : done<data.order.length)
    (hp : tupleRecordPrinter.program.tapeCount ≤ span)
    (hinput :
      let i := data.order[(reverseSupportIndex data.order done hd).val]
      let tr := r.toRowContext.tupleStepRequest (r.stackWidth+1) (by omega)
        i (processedSupport data.order done)
      400*((fieldRecords tr.L tr.children).flatMap frame).length+
      400*((fieldRecords tr.L tr.tuples).flatMap frame).length+
      400*(tr.N+tr.M+tr.children.length+tr.tuples.length+10) ≤ cap)
    (hcall :
      let i := data.order[(reverseSupportIndex data.order done hd).val]
      let tr := r.toRowContext.tupleStepRequest (r.stackWidth+1) (by omega)
        i (processedSupport data.order done)
      2*tr.word.length+2+(2*tr.budget+2) ≤ cap)
    (houtput :
      let i := data.order[(reverseSupportIndex data.order done hd).val]
      let tr := r.toRowContext.tupleStepRequest (r.stackWidth+1) (by omega)
        i (processedSupport data.order done)
      ((tupleRecords tr).flatMap frame).length+1 ≤ cap) :
    let i := data.order[(reverseSupportIndex data.order done hd).val]
    let req := StageNativeKids.NativeKidsRequest.ofTerm r i
    let tr := r.toRowContext.tupleStepRequest (r.stackWidth+1) (by omega)
      i (processedSupport data.order done)
    let σ0 := ((data.reverseState r span done).setv 15 (data.order.length-(done+1))).sets
      (kernelLocal span 17) (frame (finiteSupportRequest data.order
        (reverseSupportIndex data.order done hd)).output)
    let σ := nativePhaseState span req σ0
    ∃τ,WXExec cap (cartesianStepProgram
      (kernelPacketMap span kernelCartesianSources tupleRecordPrinter.program hp)
      kernelCartesianRegisters (kernelSite span tupleRecordPrinter.program hp)) σ τ
        (cartesianStepCost tr) ∧
      SimW (closedHistory σ (kernelLocal span 20) 0 (σ.st (kernelLocal span 20))
        ((tupleRecords tr).flatMap frame)) τ := by
  let i := data.order[(reverseSupportIndex data.order done hd).val]
  let req := StageNativeKids.NativeKidsRequest.ofTerm r i
  let tr := r.toRowContext.tupleStepRequest (r.stackWidth+1) (by omega)
    i (processedSupport data.order done)
  let σ0 := ((data.reverseState r span done).setv 15 (data.order.length-(done+1))).sets
    (kernelLocal span 17) (frame (finiteSupportRequest data.order
      (reverseSupportIndex data.order done hd)).output)
  let σ := nativePhaseState span req σ0
  let P := kernelPacketMap span kernelCartesianSources tupleRecordPrinter.program hp
  let R := kernelCartesianRegisters
  let s := kernelSite span tupleRecordPrinter.program hp
  let pre := data.historyPrefix++
    tupleHistoryPrefix (r.stackWidth+1) r.toRowContext.nativeKids data.order done
  have hb0 : CallBlank tupleRecordPrinter.program s σ0 :=
    ((data.reverseState_blank r span done _ hp).setv 15 _ (by
      intro j;fin_cases j <;> simp [kernelSite,kernelCallRegisters])).sets _ _
        (kernelSite_out span _ hp 17 (by decide) (by decide))
        (kernelSite_ruler_ne span _ hp 17 (by decide))
  have hb : CallBlank tupleRecordPrinter.program s σ := nativePhaseState_blank span req _ hp σ0 hb0
  apply cartesianStepProgram_spec cap P R s
    (by simpa [P,s] using kernelPacketMap_input span kernelCartesianSources tupleRecordPrinter.program hp)
    tr (natWord (r.toRowContext.nativeKids i).length) pre σ hb
  · exact kernelSite_out span _ hp 20 (by decide) (by decide)
  · exact kernelSite_ruler_ne span _ hp 20 (by decide)
  · simp [R,s,kernelCartesianRegisters,kernelSite,kernelCallRegisters]
  · change σ.st (kernelLocal span 19)=_
    simp [σ,nativePhaseState,nativePhasePayload,req,StageNativeKids.NativeKidsRequest.ofTerm,
      tr,RowContext.tupleStepRequest,fieldsRecs_eq_records,kernelLocal]
  · change σ.st (kernelLocal span 20)=_
    simp [σ,σ0,nativePhaseState,MonomialData.reverseState,MonomialData.reverseData,
      KernelData.state,kernelLocal,tr,RowContext.tupleStepRequest,pre,tupleHistory_eq,
      tupleSegment,fieldsRecs_eq_records,List.append_assoc]
  · change σ.sh (kernelLocal span 19)=_
    simp [σ,nativePhaseState,req,StageNativeKids.NativeKidsRequest.ofTerm,kernelLocal]
  · change σ.sh (kernelLocal span 20)=_
    simp [σ,σ0,nativePhaseState,MonomialData.reverseState,MonomialData.reverseData,
      KernelData.state,kernelLocal,pre]
  · intro j
    fin_cases j <;> simp [σ,σ0,nativePhaseState,R,kernelCartesianRegisters,
      MonomialData.reverseState,MonomialData.reverseData,KernelData.state]
  · simp [R,kernelCartesianRegisters,σ,σ0,nativePhaseState,req,
      StageNativeKids.NativeKidsRequest.ofTerm,MonomialData.reverseState,
      MonomialData.reverseData,KernelData.state,tr,RowContext.tupleStepRequest,
      processedSupport_length data.order done hd.le,TermCutRequest.rowDimension]
  · exact hinput
  · exact hcall
  · exact houtput

end NearQuarticWires.StageTuple
