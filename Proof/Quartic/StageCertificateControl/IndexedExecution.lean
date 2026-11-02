import Proof.Quartic.StageCertificateControl.IndexedBounds
import Proof.Quartic.StageCertificateControl.IndexedEmit
import Proof.Quartic.StageCertificateControl.IndexedAvoid

/-!
# Complete cold execution of the indexed whole-test preprocessing

Paper: Step 2 of `sec:algorithm`, paper/paper.tex,
and `prop:time`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCertificateControl

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicWires.RepairOrdinary.Streaming (marks marks_length)
open NearCubicGates.Close NearCubicGates.Close.Interfaces NearCubicGates.Close.WordPrograms
open NearCubicGates.Close.CheckedPCPP
open NearQuarticWires.Control

/-- `sec:algorithm` and `prop:time`, paper/paper.tex: from the literal indexed preparation, one
fixed actual program computes the selected five-field request and its
binary threshold header. The real scheduler is executed and erased,
all heads and fields are handled by measured physical instructions,
and every work guard follows from original-source bounds. -/
theorem indexedFront_exec {B1 B2 : ℕ} (r : IndexedRequest B1 B2) :
    let p := (framedScheduleWordFunction B1 B2).program
    ∃ τ, WXExec (indexedFrontSourceSteps r) (indexedFrontProgram p)
      (startState (p.tapeCount+11) 32 r.word) τ (indexedFrontSourceSteps r) ∧
      τ.st (indexedFinal p)=frame r.frontWord := by
  let p := (framedScheduleWordFunction B1 B2).program
  let cap := indexedFrontSourceSteps r
  obtain ⟨hindex,hcopy,hcall,hout,hselect,hthreshold,hemit,hcost⟩ := indexedFront_bounds r
  have el := indexedLoad_exec p r cap hindex hcopy
  obtain ⟨τschedule,es,hss⟩ := indexedSchedule_exec r cap hcall hout hselect
  obtain ⟨hs,hsh,hr,hrh,hd,ht,hth,hmeta,hz⟩ := indexedSelection_threshold_ready p r
  have et := indexedThreshold_exec p r.metadata cap (indexedAfterSelection p r)
    hs hsh hr hrh hd ht hth hmeta hz hthreshold
  obtain ⟨τthreshold,etActual,hst⟩ := wxexec_sim et τschedule hss
  have hav := indexedPrior_avoids_final p
  have hlf := NearQuarticWires.Control.WXExec.avoids el hav.1
  have hsf := NearQuarticWires.Control.WXExec.avoids es hav.2.1
  have htf := NearQuarticWires.Control.WXExec.avoids etActual hav.2.2
  have ho : τthreshold.st (indexedFinal p)=[] := by
    rw [htf.1,hsf.1,hlf.1]
    simp [startState,indexedFinal]
  have hoh : τthreshold.sh (indexedFinal p)=0 := by
    rw [htf.2,hsf.2,hlf.2]
    rfl
  have hframes := indexedThreshold_retained_frames p r
  have hsource := indexedThreshold_source p r
  have hcounters := indexedThreshold_output_counters p r
  have transfer (i : Fin (p.tapeCount+12)) (bits : List Bool)
      (hc : ∀ q,readTapeBit ((indexedAfterThreshold p r).st i)
        ((indexedAfterThreshold p r).sh i+q)=readTapeBit (frame bits) q) :
      ∀ q,readTapeBit (τthreshold.st i) (τthreshold.sh i+q)=readTapeBit (frame bits) q := by
    intro q
    rw [hst.sh]
    exact (hst.st i _).symm.trans (hc q)
  have hH := transfer (indexedExternal p 6) (RepairRepresentation.natWord r.metadata.threshold)
    (by intro q;rw [hframes.1,hframes.2.1];simp only [Nat.zero_add])
  have hM := transfer (indexedExternal p 4) r.metadata.word
    (by intro q;rw [hframes.2.2.1,hframes.2.2.2];simp only [Nat.zero_add])
  have hS := transfer (indexedExternal p 0) r.prepared.word (by
    intro q
    rw [hsource.1,hsource.2]
    have hsplit : frame r.word=marks (RepairRepresentation.natWord r.index.val)++frame r.prepared.word := by
      simp [IndexedRequest.word,Codec.frame_eq_marks,
        NearCubicWires.RepairOrdinary.Streaming.marks_append,List.append_assoc]
    rw [hsplit]
    unfold readTapeBit
    rw [List.getD_append_right _ _ _ _ (by simp [marks_length])]
    simp [marks_length])
  obtain ⟨τ,ee,hresult⟩ := indexedEmit_exec p cap
    (RepairRepresentation.natWord r.metadata.threshold) r.prepared.word r.metadata.word τthreshold
    hH hS hM ho hoh
    (by rw [hst.val];exact hcounters.1) (by rw [hst.val];exact hcounters.2) hemit
  refine ⟨τ,(el.seq (es.seq (etActual.seq ee))).mono hcost,?_⟩
  simpa only [IndexedRequest.frontWord,IndexedRequest.baseWord,List.append_assoc] using hresult

end NearQuarticWires.StageCertificateControl
