import Proof.Quartic.StageCertNative.HeaderSource
import Proof.Quartic.StageCertNative.WeakMeaning
import Proof.Quartic.StageCertNative.OutputTarget

set_option autoImplicit false

namespace NearQuarticWires.StageCertNative
open NearCubicWires NearCubicWires.RepairOrdinary
open StageCertificateControl

/-- `lem:print`, paper/paper.tex: the one
whole-test native call uses the original canonical star and literal
concatenated signed matrix, including all padded columns. -/
noncomputable def nativeHeaderRequest {B1 B2 : ℕ} (r : IndexedRequest B1 B2) :
    StagePrint.Downstream.NativeHeaderRequest where
  parameters:=(zeroMoment r).rules.starParams
  table:=actualTable r
  dimension_eq:=rfl
  width_eq:=rfl
  columns_eq:=fun _=>rfl

/-- `lem:print`, paper/paper.tex: the physical
header source contains precisely the five source-derived scalars and
the once-concatenated whole-test weak-cut body, with no table input. -/
theorem nativeHeaderRequest_word {B1 B2 : ℕ} (r : IndexedRequest B1 B2) :
    (nativeHeaderRequest r).word=nativeFieldsWord r++wholeWeakWord r := by
  have hs : (nativeHeaderRequest r).stream=wholeWeakWord r :=
    (wholeWeakWord_eq_nativeStream r).symm
  unfold StagePrint.Downstream.NativeHeaderRequest.word
  rw [hs]
  change [r.prepared.call.n,r.prepared.selected.1.r,(zeroMoment r).rules.starParams.b,
      (zeroMoment r).rules.starParams.s,commonWidth r+1].flatMap RepairRepresentation.natWord++wholeWeakWord r=_
  rw [(zeroMoment r).rules.star_b,(zeroMoment r).rules.star_s]
  simp only [nativeFieldsWord,StagePrint.Context.geometryWord,List.flatMap_cons,List.flatMap_nil,
    List.append_nil,List.append_assoc]
  rfl

/-- `lem:print`, paper/paper.tex: the shared
output helper's payload is the exact unchanged actual BASE payload,
with no threshold or additional interpretation. -/
theorem nativeHeaderRequest_output {B1 B2 : ℕ} (r : IndexedRequest B1 B2) :
    Output.output (nativeHeaderRequest r)=
      frame (RepairRepresentation.natWord ((actualTable r).q+1)++(actualTable r).output) := rfl

end NearQuarticWires.StageCertNative
