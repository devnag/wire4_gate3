import Proof.Quartic.StageCertNative.CachedSource
import Proof.Quartic.StageCertNative.EntryRequest

set_option autoImplicit false

namespace NearQuarticWires.StageCertNative
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open StageCertificateControl StageCert.Tokens

/-- `lem:print`, paper/paper.tex: an actual
loop term has one original whole-test request and its finite low-first
ordinal. The common context and count were computed once beforehand. -/
structure TermJob (B1 B2 : ℕ) where
  base : IndexedRequest B1 B2
  index : Fin (termCount base)

noncomputable def TermJob.moment {B1 B2 : ℕ} (r : TermJob B1 B2) : MomentRequest B1 B2 :=
  actualMoment r.base r.index

/-- `lem:print`, paper/paper.tex: the ordinary
pool loop writes only its binary index before the actually retained
whole-test source; no Formula, pool or decoded context is supplied. -/
noncomputable def TermJob.word {B1 B2 : ℕ} (r : TermJob B1 B2) : List Bool :=
  natWord r.index.val++cachedSourceWord r.base

/-- `lem:print`, paper/paper.tex: this is the
original literal preparation and five test fields, preceded only by
the actual index and once-computed binary count. -/
theorem actualMoment_indexedWord {B1 B2 : ℕ} (r : IndexedRequest B1 B2)
    (i : Fin (termCount r)) :
    indexedMomentWord (actualMoment r i)=natWord i.val++r.baseWord := by
  unfold indexedMomentWord indexedMomentValues actualMoment IndexedRequest.baseWord
    StageCertTests.PreparedScheduleRequest.word
  rw [actualOrdinal_metadata]
  simp only [StageCertTests.TestMetadata.word,List.flatMap_cons,List.flatMap_nil,
    List.append_nil,List.append_assoc]

end NearQuarticWires.StageCertNative
