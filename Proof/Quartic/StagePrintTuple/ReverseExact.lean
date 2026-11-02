import Proof.Quartic.StagePrintTuple.NativeTransition
import Proof.Quartic.StagePrintTuple.ReverseTransition
import Proof.Quartic.StagePrintTuple.RecordOutputs

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageTuple

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.TabMachine
open NearCubicGates.Close.Interfaces

/-- `lem:print`, paper/paper.tex: the exact
native reply, actual Cartesian history append, computed tuple product
and finite cleanup together produce the next literal reverse boundary. -/
theorem reverseExact (r : TermCutRequest)
    (data : MonomialData (17*(Builder.allGates r.header.call).length))
    (span done : ℕ) (hd : done<data.order.length) :
    let i := data.order[(reverseSupportIndex data.order done hd).val]
    let req := StageNativeKids.NativeKidsRequest.ofTerm r i
    let tr := r.toRowContext.tupleStepRequest (r.stackWidth+1) (by omega)
      i (processedSupport data.order done)
    let q := finiteSupportRequest data.order (reverseSupportIndex data.order done hd)
    let σ0 := (data.reverseState r span done).setv 15 (data.order.length-(done+1))
    let σ1 := nativePhaseState span req (σ0.sets (kernelLocal span 17) (frame q.output))
    let σ := closedHistory σ1 (kernelLocal span 20) 0 (σ1.st (kernelLocal span 20))
      ((tupleRecords tr).flatMap frame)
    nativeCleanupState span (((σ.setv 14 (tr.children.length*tr.tuples.length)).setv 13 0).setv
      12 (done*(r.rowDimension+1)+(r.rowDimension+1)))=
      data.reverseState r span (done+1) := by
  let i := data.order[(reverseSupportIndex data.order done hd).val]
  let req := StageNativeKids.NativeKidsRequest.ofTerm r i
  let tr := r.toRowContext.tupleStepRequest (r.stackWidth+1) (by omega)
    i (processedSupport data.order done)
  let q := finiteSupportRequest data.order (reverseSupportIndex data.order done hd)
  let σ0 := (data.reverseState r span done).setv 15 (data.order.length-(done+1))
  let σ1 := nativePhaseState span req (σ0.sets (kernelLocal span 17) (frame q.output))
  let segment := (tupleRecords tr).flatMap frame
  have ht : σ0.val 14=tr.tuples.length := by
    simp [σ0,MonomialData.reverseState,MonomialData.reverseData,KernelData.state,
      tr,RowContext.tupleStepRequest]
  have hm : σ0.val 12=done*(r.rowDimension+1) := by
    simp [σ0,MonomialData.reverseState,MonomialData.reverseData,KernelData.state]
  have hh : σ1.st (kernelLocal span 20)=σ0.st (kernelLocal span 20) := by
    simp [σ1,nativePhaseState,kernelLocal]
  have hn := nativeTransition_normalize span req σ0 q.output segment tr.children.length (r.rowDimension+1)
    (by simp [σ0,MonomialData.reverseState,MonomialData.reverseData,KernelData.state,kernelLocal])
    (by simp [σ0,MonomialData.reverseState,MonomialData.reverseData,KernelData.state,kernelLocal])
    (by simp [σ0,MonomialData.reverseState,MonomialData.reverseData,KernelData.state,kernelLocal])
    (by simp [σ0,MonomialData.reverseState,MonomialData.reverseData,KernelData.state,kernelLocal])
    (by simp [σ0,MonomialData.reverseState,MonomialData.reverseData,KernelData.state,kernelLocal])
    (by simp [σ0,MonomialData.reverseState,MonomialData.reverseData,KernelData.state])
    (by simp [σ0,MonomialData.reverseState,MonomialData.reverseData,KernelData.state])
  rw [ht,hm] at hn
  dsimp only
  change nativeCleanupState span
    ((((closedHistory σ1 (kernelLocal span 20) 0 (σ1.st (kernelLocal span 20)) segment).setv
      14 (tr.children.length*tr.tuples.length)).setv 13 0).setv
      12 (done*(r.rowDimension+1)+(r.rowDimension+1)))=_
  rw [hh]
  rw [hn]
  let old := {data.reverseData r done with reverseIndex := data.order.length-(done+1)}
  let L := (frame (listWord natWord (data.order.map Fin.val))).length
  have hbase : σ0=(old.state span r).setv 26 L := by
    apply WState.eq
    · rfl
    · rfl
    · funext j
      fin_cases j <;> simp [σ0,old,L,MonomialData.reverseState,MonomialData.reverseData,KernelData.state]
    · rfl
  have hr : segment=fieldsRecs (r.stackWidth+1)
      (tupleFields r.toRowContext.nativeKids (processedSupport data.order (done+1))) := by
    dsimp only [segment]
    rw [←tuple_output_records tr]
    simp only [tr,RowContext.tupleStepRequest_output]
    rw [←reverseSupportIndex_suffix data.order done hd]
  have he := old.nextCartesian_state segment tr.children.length (r.rowDimension+1) span r
  have hnext : old.nextCartesian segment tr.children.length (r.rowDimension+1)=data.reverseData r (done+1) := by
    rw [hr]
    exact (data.reverseData_succ r done hd).symm
  rw [hnext] at he
  have hval : old.tuples=tr.tuples.length ∧ old.stride=done*(r.rowDimension+1) := by
    simp [old,MonomialData.reverseData,tr,RowContext.tupleStepRequest]
  rw [hval.1,hval.2] at he
  rw [MonomialData.reverseState,he]
  rw [hbase]
  apply WState.eq
  · rfl
  · rfl
  · funext j
    fin_cases j <;> simp [closedHistory,L]
  · rfl

end NearQuarticWires.StageTuple
