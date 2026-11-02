import Proof.Quartic.StageCertificateControl.IndexedSchedule

/-!
# Original-source capacities and clocks for whole-test indexing

Paper: `prop:time`, paper/paper.tex.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCertificateControl

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close
open NearQuarticWires.Control

/-- `prop:time`, paper/paper.tex: one
fixed polynomial original-source scale bounds all physical index and
metadata preprocessing instructions and their unary work registers. -/
noncomputable def indexedFrontSourceSteps {B1 B2 : ℕ} (r : IndexedRequest B1 B2) : ℕ :=
  10000000*(indexedSourceMass r.prepared)^2

/-- `prop:time`, paper/paper.tex: every
index, copy, actual scheduler, record and threshold guard is derived
from original request bytes and proved machine output length. The
complete physical source clock is bounded by that same scale. -/
theorem indexedFront_bounds {B1 B2 : ℕ} (r : IndexedRequest B1 B2) :
    let cap := indexedFrontSourceSteps r
    2^(natBitLength r.index.val+1)≤cap ∧
    4*r.prepared.word.length+4≤cap ∧
    2*r.prepared.word.length+2+framedScheduleBudget r.prepared≤cap ∧
    (frame r.prepared.output).length+1≤cap ∧
    100*(r.prepared.output.length+r.index.val+1)≤cap ∧
    100*(r.metadata.word.length+1)≤cap ∧
    100*((RepairRepresentation.natWord r.metadata.threshold).length+
      r.prepared.word.length+r.metadata.word.length+1)≤cap ∧
    indexedLoadCost r+1+(indexedScheduleCost r+1+
      (3000*(r.metadata.word.length+1)+1+
        100*((RepairRepresentation.natWord r.metadata.threshold).length+
          r.prepared.word.length+r.metadata.word.length+1)))≤cap := by
  let M := indexedSourceMass r.prepared
  have hM : M=r.prepared.word.length+framedScheduleBudget r.prepared+
      (StageCertTests.certificateMetadata r.prepared.selected.1 r.prepared.call.kind).length+10 := rfl
  have hpos : 10≤M := by omega
  have hj := r.index.isLt
  have hb := Control.natBitLength_le_self_succ r.index.val
  have hp := Control.two_pow_natBitLength_le r.index.val
  have hout := Control.output_length_le (framedScheduleWordFunction B1 B2) r.prepared
  change (frame r.prepared.output).length≤framedScheduleBudget r.prepared+1 at hout
  have hframe : (frame r.prepared.output).length=2*r.prepared.output.length+1 := by
    simp [Codec.frame_eq_marks]
  rw [hframe] at hout
  have hm := r.metadata_length_le
  have ht := r.threshold_length_le
  have hfront := r.byte_bounds.2
  simp only [IndexedRequest.frontWord,IndexedRequest.baseWord,List.length_append] at hfront
  have hnext : 2^(natBitLength r.index.val+1)≤4*r.index.val+4 := by
    rw [pow_succ]
    nlinarith
  have hproduct := Nat.mul_le_mul
    (show natBitLength r.index.val+2≤M by omega)
    (show 40*2^natBitLength r.index.val+40≤100*M by nlinarith)
  have hload : indexedLoadCost r≤1000*M^2 := by
    unfold indexedLoadCost
    nlinarith
  have hschedule : indexedScheduleCost r≤100000*M := by
    unfold indexedScheduleCost StagePrint.callAppendCost indexedSelectCost
    nlinarith
  dsimp only
  change _≤10000000*M^2 ∧ _≤10000000*M^2 ∧ _≤10000000*M^2 ∧ _≤10000000*M^2 ∧
    _≤10000000*M^2 ∧ _≤10000000*M^2 ∧ _≤10000000*M^2 ∧ _≤10000000*M^2
  rw [hframe]
  and_intros <;> nlinarith

end NearQuarticWires.StageCertificateControl
