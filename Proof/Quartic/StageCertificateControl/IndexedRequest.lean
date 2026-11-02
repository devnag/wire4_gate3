import Proof.Quartic.StageCertificateControl.FramedSchedule
import Proof.Quartic.StageCertificateControl.MetadataFields
import Proof.Quartic.StageCertificateControl.CountStartCost

/-!
# Original-source requests for indexed whole-test tables

Paper: Step 2 of `sec:algorithm`, paper/paper.tex,
and `prop:time`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCertificateControl

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close NearCubicGates.Close.Interfaces
open StageCertTests

/-- `sec:algorithm`, paper/paper.tex: the physical
indexed input contains only the actual successful preparation and one
bounded schedule index. No decoded metadata or moment table is supplied. -/
structure IndexedRequest (B1 B2 : ℕ) where
  prepared : PreparedScheduleRequest B1 B2
  index : Fin (certificateMetadata prepared.selected.1 prepared.call.kind).length

/-- `sec:algorithm`, paper/paper.tex: the actual
indexed call keeps the original preparation bytes after the index. -/
noncomputable def IndexedRequest.word {B1 B2 : ℕ} (r : IndexedRequest B1 B2) : List Bool :=
  RepairRepresentation.natWord r.index.val++r.prepared.word

/-- `eq:testX`–`eq:testPhi`, paper/paper.tex:
the selected metadata is determined by the original complete scheduler. -/
noncomputable def IndexedRequest.metadata {B1 B2 : ℕ} (r : IndexedRequest B1 B2) : TestMetadata :=
  (certificateMetadata r.prepared.selected.1 r.prepared.call.kind)[r.index.val]

/-- `sec:algorithm`, paper/paper.tex: the whole-test
base input appends the actual five-field record to the unchanged prep. -/
noncomputable def IndexedRequest.baseWord {B1 B2 : ℕ} (r : IndexedRequest B1 B2) : List Bool :=
  r.prepared.word++r.metadata.word

/-- `prop:time`, paper/paper.tex: the
polynomial preprocessing payload retains the actual threshold codec,
preparation, and selected metadata, in their physically copied order. -/
noncomputable def IndexedRequest.frontWord {B1 B2 : ℕ} (r : IndexedRequest B1 B2) : List Bool :=
  RepairRepresentation.natWord r.metadata.threshold++r.baseWord

/-- `prop:time`, paper/paper.tex: the
selected metadata bytes are part of the literal complete schedule. -/
theorem IndexedRequest.metadata_length_le {B1 B2 : ℕ} (r : IndexedRequest B1 B2) :
    r.metadata.word.length≤r.prepared.output.length := by
  have h := congrArg List.length
    (metadataSelected_word (certificateMetadata r.prepared.selected.1 r.prepared.call.kind) r.index)
  simp only [List.length_append,metadataFields_word,metadataScalarFields_word] at h
  change r.metadata.word.length≤_
  change _≤((certificateMetadata r.prepared.selected.1 r.prepared.call.kind).flatMap TestMetadata.word).length
  dsimp only [IndexedRequest.metadata]
  omega

/-- `prop:time`, paper/paper.tex: the
threshold header is bounded by its actual metadata bytes, independently
of the threshold's numeric magnitude. -/
theorem IndexedRequest.threshold_length_le {B1 B2 : ℕ} (r : IndexedRequest B1 B2) :
    (RepairRepresentation.natWord r.metadata.threshold).length≤r.metadata.word.length := by
  have h := congrArg List.length (metadataThreshold_word r.metadata)
  simp only [List.length_append] at h
  omega

/-- `prop:time`, paper/paper.tex: all
preprocessing sizes are controlled by actual original-source bytes,
the actual scheduler budget, and the complete numeric test count. -/
noncomputable def indexedSourceMass {B1 B2 : ℕ} (r : PreparedScheduleRequest B1 B2) : ℕ :=
  r.word.length+framedScheduleBudget r+
    (certificateMetadata r.selected.1 r.call.kind).length+10

/-- `prop:time`, paper/paper.tex: both the
literal indexed input and exact preprocessing output are polynomial-
size byte streams. The threshold is never charged by its numeric value. -/
theorem IndexedRequest.byte_bounds {B1 B2 : ℕ} (r : IndexedRequest B1 B2) :
    r.word.length≤4*indexedSourceMass r.prepared ∧
      r.frontWord.length≤4*indexedSourceMass r.prepared := by
  have hout := Control.output_length_le (framedScheduleWordFunction B1 B2) r.prepared
  change (frame r.prepared.output).length≤framedScheduleBudget r.prepared+1 at hout
  have hm := r.metadata_length_le
  have ht := r.threshold_length_le
  have hi := Control.natWord_length_bound r.index.val
  have hir := r.index.isLt
  simp only [Codec.frame_eq_marks,List.length_append,
    NearCubicWires.RepairOrdinary.Streaming.marks_length,List.length_singleton] at hout
  simp only [IndexedRequest.word,IndexedRequest.frontWord,IndexedRequest.baseWord,List.length_append]
  unfold indexedSourceMass
  omega

/-- `prop:time`, paper/paper.tex: the entire
index and metadata preprocessing scale is polynomial in the original
call word on every actual selected preparation and every witness. -/
theorem indexedSourceMass_polynomial (B1 B2 : ℕ) :
    PreparedPolynomial (B1 := B1) (B2 := B2) indexedSourceMass := by
  have hc : PreparedPolynomial (B1 := B1) (B2 := B2) (fun r =>
      (certificateMetadata r.selected.1 r.call.kind).length) := by
    obtain ⟨K,e,hK⟩ := countHeaderValuePolyCost B1 B2
    refine ⟨K,e,fun r => ?_⟩
    simpa only [countHeaderValue,r.dispatched] using hK r.call r.witness
  exact ((PreparedPolynomial.inputLength.add (framedScheduleBudget_polynomial B1 B2)).add hc).add
    (PreparedPolynomial.const 10)

end NearQuarticWires.StageCertificateControl
