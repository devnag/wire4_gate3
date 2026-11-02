import Proof.Quartic.StageCertificateControl.IndexedCallState
import Proof.Quartic.StageCertificateControl.IndexedThreshold

/-!
# Literal exterior words and counters between indexed preprocessing phases

Paper: Step 2 of `sec:algorithm`, paper/paper.tex,
and `prop:time`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCertificateControl

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close NearCubicGates.Close.Interfaces

/-- `prop:time`, paper/paper.tex: the
actual selected-record phase starts from the deterministic exterior of
the completed scheduler call. -/
noncomputable def indexedAfterSelection {B1 B2 : ℕ} (p : Program) (r : IndexedRequest B1 B2) :
    WState (p.tapeCount+11) 32 :=
  indexedSelectedState p r (indexedSchedulerCopyState p r)

/-- `prop:time`, paper/paper.tex: the
actual threshold phase retains the original preparation and selected
metadata while adding the exact binary threshold-header frame. -/
noncomputable def indexedAfterThreshold {B1 B2 : ℕ} (p : Program) (r : IndexedRequest B1 B2) :
    WState (p.tapeCount+11) 32 :=
  indexedThresholdState p r.metadata (indexedAfterSelection p r)

/-- `sec:algorithm` and `prop:time`, paper/paper.tex: every threshold-extraction input, including
empty actual work tapes and zero scratch, follows from the concrete
indexed scheduler and selection state. -/
theorem indexedSelection_threshold_ready {B1 B2 : ℕ} (p : Program) (r : IndexedRequest B1 B2) :
    let σ := indexedAfterSelection p r
    σ.st (indexedExternal p 4)=frame r.metadata.word ∧ σ.sh (indexedExternal p 4)=0 ∧
    σ.st (indexedExternal p 5)=[] ∧ σ.sh (indexedExternal p 5)=0 ∧
    σ.sh (indexedExternal p 3)=(σ.st (indexedExternal p 3)).length ∧
    σ.st (indexedExternal p 6)=[] ∧ σ.sh (indexedExternal p 6)=0 ∧
    σ.val 7=2*r.metadata.word.length ∧
    (∀ i∈([0,1,2,8,9,11,12,13,14,16,17,18] : List (Fin 32)),σ.val i=0) := by
  dsimp only
  and_intros
  all_goals first
    | (intro i hi; simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
       rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl)
    | skip
  all_goals simp [indexedAfterSelection,indexedSelectedState,selectedMetadataEnd,
    metadataRecordEnd,metadataPrefixEnd,indexedSchedulerCopyState,indexedClearedState,
    indexedReadState,startState,appendO,indexedSelectionRegs,indexedExternal]

/-- `sec:algorithm` and `prop:time`, paper/paper.tex: after physical threshold extraction, both
retained frames and their actual heads have the exact required bytes. -/
theorem indexedThreshold_retained_frames {B1 B2 : ℕ} (p : Program) (r : IndexedRequest B1 B2) :
    let σ := indexedAfterThreshold p r
    σ.st (indexedExternal p 6)=frame (RepairRepresentation.natWord r.metadata.threshold) ∧
    σ.sh (indexedExternal p 6)=0 ∧
    σ.st (indexedExternal p 4)=frame r.metadata.word ∧ σ.sh (indexedExternal p 4)=0 := by
  dsimp only
  and_intros
  all_goals simp [indexedAfterThreshold,indexedThresholdState,thresholdFieldsEnd,fixedFieldsEnd,
    appendO,indexedThresholdRegs,indexedExternal,indexedSelection_threshold_ready]
  exact (indexedSelection_threshold_ready p r).1

/-- `prop:time`, paper/paper.tex: the
original indexed source and its true preparation offset survive all
scheduler, record-selection and threshold-extraction instructions. -/
theorem indexedThreshold_source {B1 B2 : ℕ} (p : Program) (r : IndexedRequest B1 B2) :
    (indexedAfterThreshold p r).st (indexedExternal p 0)=frame r.word ∧
    (indexedAfterThreshold p r).sh (indexedExternal p 0)=
      2*(RepairRepresentation.natWord r.index.val).length := by
  constructor
  all_goals simp [indexedAfterThreshold,indexedThresholdState,thresholdFieldsEnd,fixedFieldsEnd,
    indexedAfterSelection,indexedSelectedState,selectedMetadataEnd,metadataRecordEnd,metadataPrefixEnd,
    indexedSchedulerCopyState,indexedClearedState,indexedReadState,startState,appendO,indexedExternal]

/-- `prop:time`, paper/paper.tex: the final
literal output copy has zero counters before its first actual bit. -/
theorem indexedThreshold_output_counters {B1 B2 : ℕ} (p : Program) (r : IndexedRequest B1 B2) :
    (indexedAfterThreshold p r).val 19=0 ∧ (indexedAfterThreshold p r).val 20=0 := by
  constructor
  all_goals simp [indexedAfterThreshold,indexedThresholdState,thresholdFieldsEnd,fixedFieldsEnd,
    indexedAfterSelection,indexedSelectedState,selectedMetadataEnd,metadataRecordEnd,metadataPrefixEnd,
    indexedSchedulerCopyState,indexedClearedState,indexedReadState,startState,appendO,
    indexedThresholdRegs,indexedSelectionRegs]

end NearQuarticWires.StageCertificateControl
