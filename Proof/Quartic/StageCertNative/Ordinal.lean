import Proof.Quartic.StageCertificateControl.IndexedRequest
import Proof.Quartic.StageCertTests.ScheduleSemantics
import Proof.Quartic.StageCert.MomentTermSum

set_option autoImplicit false

namespace NearQuarticWires.StageCertNative
open NearCubicWires NearCubicWires.RepairRepresentation
open StageCertificateControl StageCertTests StageCert.Tokens

/-- `sec:algorithm`, paper/paper.tex: an actual
whole-test index selects the same ordinal as the original physical
metadata schedule, including all sign filters and both circuit banks. -/
noncomputable def actualOrdinal {B1 B2 : ℕ} (r : IndexedRequest B1 B2) :
    TestOrdinal (r.prepared.selected.1.J-1) :=
  (ordinalTestPlan (r.prepared.selected.1.J-1) (Builder.circuitSet r.prepared.call))[
    r.index.val]'(by
      have hs := Cells.prepare_spec _ r.prepared.selected.1 r.prepared.selected.2
      have h := certificateMetadata_eq_ordinalTestPlan r.prepared.call r.prepared.selected.1 hs.J_pos
      have hh := congrArg List.length h
      simp only [List.length_map] at hh
      exact r.index.isLt.trans_eq hh)

/-- `eq:testX`–`eq:testPhi` and `sec:algorithm`, paper/paper.tex: no decoded test or threshold is
supplied to BASE; the literal selected five fields are exact. -/
theorem actualOrdinal_metadata {B1 B2 : ℕ} (r : IndexedRequest B1 B2) :
    (actualOrdinal r).metadata r.prepared.selected.1=r.metadata := by
  have hs := Cells.prepare_spec _ r.prepared.selected.1 r.prepared.selected.2
  have h := certificateMetadata_eq_ordinalTestPlan r.prepared.call r.prepared.selected.1 hs.J_pos
  have he := congrArg (fun l : List TestMetadata=>l.getD r.index.val ⟨0,0,0,0,0⟩) h
  have hi : r.index.val<((ordinalTestPlan (r.prepared.selected.1.J-1)
      (Builder.circuitSet r.prepared.call)).map (TestOrdinal.metadata r.prepared.selected.1)).length := by
    rw [←h]
    exact r.index.isLt
  rw [List.getD_eq_getElem _ _ r.index.isLt,List.getD_eq_getElem _ _ hi,List.getElem_map] at he
  exact he.symm

/-- `lem:print` and `prop:time`, paper/paper.tex: the actual selected whole test has precisely N²
population terms or N⁸ moment terms, not an unconditional N⁸ loop. -/
noncomputable def termCount {B1 B2 : ℕ} (r : IndexedRequest B1 B2) : ℕ :=
  momentTermCount r.prepared.selected.1.N (actualOrdinal r)

/-- `lem:print`, paper/paper.tex: every term
request contains only the original actual source and low-first index;
all masks, signed Formula syntax and native rows remain computed. -/
noncomputable def actualMoment {B1 B2 : ℕ} (r : IndexedRequest B1 B2)
    (index : Fin (termCount r)) : MomentRequest B1 B2 where
  call := r.prepared.call
  selected := r.prepared.selected
  dispatched := r.prepared.dispatched
  witness := r.prepared.witness
  test := actualOrdinal r
  index := index

/-- `lem:print`, paper/paper.tex: the frozen
actual per-term source appends its index after the unchanged BASE
word, without adding a semantic supplier or new encoded field. -/
theorem actualMoment_word {B1 B2 : ℕ} (r : IndexedRequest B1 B2)
    (index : Fin (termCount r)) :
    (actualMoment r index).word=r.baseWord++natWord index.val := by
  unfold MomentRequest.word actualMoment IndexedRequest.baseWord StageCertTests.PreparedScheduleRequest.word
  rw [actualOrdinal_metadata]

end NearQuarticWires.StageCertNative
