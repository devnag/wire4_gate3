import Proof.Quartic.StageCertNative.HeaderProjection
import Proof.Quartic.StageCertNative.NaturalSuccessor

set_option autoImplicit false

namespace NearQuarticWires.StageCertNative
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open StageCertificateControl

noncomputable def firstJob {B1 B2 : ℕ} (r : IndexedRequest B1 B2) : TermJob B1 B2 :=
  ⟨r,⟨0,termCount_pos r⟩⟩

noncomputable def firstJobSourceBudget {B1 B2 : ℕ} (r : IndexedRequest B1 B2) : ℕ :=
  2*StageRecovery.FramedPair.cost (input:=IndexedRequest.baseWord)
    (left:=fun _ : IndexedRequest B1 B2=>natWord 0) (right:=cachedSourceWord)
    (lb:=zeroOrdinalBudget) (rb:=cachedSourceBudget) r+2

/-- `lem:print`, paper/paper.tex: the first
actual term request is derived from BASE by physically emitting its
literal zero index before the actual cached context and count. -/
noncomputable def firstJobSourceWordFunction (B1 B2 : ℕ) :
    WordFunction (IndexedRequest B1 B2) IndexedRequest.baseWord
      (fun r=>frame (firstJob r).word) firstJobSourceBudget :=
  StageRecovery.FramedPair.wordFunction (zeroOrdinalWordFunction B1 B2)
    (cachedSourceWordFunction B1 B2)

noncomputable def baseStackBudget {B1 B2 : ℕ} (r : IndexedRequest B1 B2) : ℕ :=
  4*firstJobSourceBudget r+4*jobStackBudget (firstJob r)+12

/-- `lem:print`, paper/paper.tex: one computed
first-term packing width is the common whole-test width, so the
native header does not enumerate or inspect all later equality cuts. -/
noncomputable def baseStackWordFunction (B1 B2 : ℕ) :
    WordFunction (IndexedRequest B1 B2) IndexedRequest.baseWord
      (fun r=>frame (natWord (commonWidth r))) baseStackBudget := by
  let f:=Program.WordFunction.pipe (firstJobSourceWordFunction B1 B2)
    (restrictWordFunction (jobStackWordFunction B1 B2)
      (fun r : IndexedRequest B1 B2=>firstJob r))
  refine ⟨f.program,?_⟩
  intro r
  have hw : (termRequest (firstJob r).base (firstJob r).index).stackWidth=commonWidth r := rfl
  simpa only [baseStackBudget,hw] using f.realizes r

noncomputable def basePackedFieldBudget {B1 B2 : ℕ} (r : IndexedRequest B1 B2) : ℕ :=
  4*baseStackBudget r+4*successorBudget (commonWidth r)+12

noncomputable def basePackedFieldWordFunction (B1 B2 : ℕ) :
    WordFunction (IndexedRequest B1 B2) IndexedRequest.baseWord
      (fun r=>frame (natWord (commonWidth r+1))) basePackedFieldBudget :=
  Program.WordFunction.pipe (baseStackWordFunction B1 B2)
    (restrictWordFunction successorWordFunction commonWidth)

noncomputable def nativeFieldsWord {B1 B2 : ℕ} (r : IndexedRequest B1 B2) : List Bool :=
  StagePrint.Context.geometryWord r.prepared++natWord (commonWidth r+1)

noncomputable def nativeFieldsBudget {B1 B2 : ℕ} (r : IndexedRequest B1 B2) : ℕ :=
  2*StageRecovery.FramedPair.cost (input:=IndexedRequest.baseWord)
    (left:=fun r : IndexedRequest B1 B2=>StagePrint.Context.geometryWord r.prepared)
    (right:=fun r : IndexedRequest B1 B2=>natWord (commonWidth r+1))
    (lb:=baseGeometryBudget) (rb:=basePackedFieldBudget) r+2

/-- `lem:print` and `prop:time`, paper/paper.tex: the five actual native-header scalars are computed
from literal original preparation and selected exact expansion;
no geometry, stacking width or native request is supplied. -/
noncomputable def nativeFieldsWordFunction (B1 B2 : ℕ) :
    WordFunction (IndexedRequest B1 B2) IndexedRequest.baseWord
      (fun r=>frame (nativeFieldsWord r)) nativeFieldsBudget :=
  StageRecovery.FramedPair.wordFunction (baseGeometryWordFunction B1 B2)
    (basePackedFieldWordFunction B1 B2)

end NearQuarticWires.StageCertNative
