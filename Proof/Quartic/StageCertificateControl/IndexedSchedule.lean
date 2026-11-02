import Proof.Quartic.StageCertificateControl.IndexedCall
import Proof.Quartic.StageCertificateControl.IndexedPostShapes

/-!
# The complete actual indexed scheduler and selection phase

Paper: Step 2 of `sec:algorithm`, paper/paper.tex,
and `prop:time`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCertificateControl

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicGates.Close NearCubicGates.Close.WordPrograms NearCubicGates.Close.Interfaces
open NearCubicGates.Close.CheckedPCPP
open NearQuarticWires.Control

/-- `sec:algorithm` and `prop:time`, paper/paper.tex: the original cold scheduler produces all
literal selection inputs, including empty work streams and the real
index retained outside its physically erased bank. -/
theorem indexedSchedulerCopy_select_ready {B1 B2 : ℕ} (p : Program) (r : IndexedRequest B1 B2) :
    let σ := indexedSchedulerCopyState p r
    σ.st (indexedExternal p 1)=frame r.prepared.output ∧
    σ.sh (indexedExternal p 1)=(frame r.prepared.output).length ∧
    σ.st (indexedExternal p 2)=[] ∧ σ.sh (indexedExternal p 2)=0 ∧
    σ.sh (indexedExternal p 3)=(σ.st (indexedExternal p 3)).length ∧
    σ.st (indexedExternal p 4)=[] ∧ σ.sh (indexedExternal p 4)=0 ∧
    σ.val 10=(frame r.prepared.output).length ∧ σ.val 4=r.index.val ∧
    (∀ i∈([0,1,2,6,7,8,9,11,12,13,14,15] : List (Fin 32)),σ.val i=0) := by
  dsimp only
  and_intros
  all_goals first
    | (intro i hi; simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
       rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl)
    | skip
  all_goals simp [indexedSchedulerCopyState,indexedClearedState,indexedReadState,startState,
    appendO,indexedExternal]

/-- `prop:time`, paper/paper.tex: the
actual cold scheduler execution, copied-frame retention, full erasure,
binary unframing and selected-record traversal have one literal clock. -/
noncomputable def indexedScheduleCost {B1 B2 : ℕ} (r : IndexedRequest B1 B2) : ℕ :=
  StagePrint.callAppendCost r.prepared.word.length (framedScheduleBudget r.prepared)+1+
    indexedSelectCost r

/-- `sec:algorithm` and `prop:time`, paper/paper.tex: a complete physical scheduler call followed
by actual index selection produces the exact retained metadata state.
All cold execution, binary output copies and bank cleanup are paid;
no decoded metadata supplier is assumed. -/
theorem indexedSchedule_exec {B1 B2 : ℕ} (r : IndexedRequest B1 B2) (cap : ℕ)
    (hcall : 2*r.prepared.word.length+2+framedScheduleBudget r.prepared≤cap)
    (hcopy : (frame r.prepared.output).length+1≤cap)
    (hselect : 100*(r.prepared.output.length+r.index.val+1)≤cap) :
    let p := (framedScheduleWordFunction B1 B2).program
    ∃ τ, WXExec cap (indexedScheduleProgram p) (indexedLoadedState p r) τ (indexedScheduleCost r) ∧
      SimW (indexedAfterSelection p r) τ := by
  let p := (framedScheduleWordFunction B1 B2).program
  obtain ⟨τcall,ec,hsc⟩ := indexedScheduler_call r cap hcall hcopy
  obtain ⟨hs,hsh,hr,hrh,hd,hm,hmh,hOP,hindex,hz⟩ := indexedSchedulerCopy_select_ready p r
  have es := indexedSelect_exec p r cap (indexedSchedulerCopyState p r)
    hs hsh hr hrh hd hm hmh hOP hindex hz hselect
  obtain ⟨τend,esActual,hsend⟩ := wxexec_sim es τcall hsc
  exact ⟨τend,ec.seq esActual,hsend⟩

end NearQuarticWires.StageCertificateControl
