import Proof.Quartic.StageCertNative.FieldProjection
import Proof.Quartic.StageCertNative.EntryFormatJoin

set_option autoImplicit false

namespace NearQuarticWires.StageCertNative
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats
open StageCertificateControl

/-- `lem:print`, paper/paper.tex: the four
original star scalars are a literal framed field of the once-computed
context, not an additional decoded geometry input. -/
def geometryProjection {B1 B2 : ℕ} (r : StageCertTests.PreparedScheduleRequest B1 B2) :
    FieldProjectionRequest 3 where
  fields:=[frame (callWord r.call),frame ((StagePrint.Header.baseHeaderValues
    (StagePrint.Context.header r)).flatMap natWord),StagePrint.Context.countsWord r]
  target:=StagePrint.Context.geometryWord r
  tail:=List.replicate 7 false
  prefix_length:=rfl

theorem geometryProjection_word {B1 B2 : ℕ} (r : StageCertTests.PreparedScheduleRequest B1 B2) :
    (geometryProjection r).word=StagePrint.Context.word r := by
  simp only [geometryProjection,FieldProjectionRequest.word,StagePrint.Context.word,
    Top.loadRec,List.flatMap_cons,List.flatMap_nil,List.append_nil,frame,
    List.replicate_succ,List.replicate_zero,List.append_assoc]
  rfl

theorem geometryProjection_target {B1 B2 : ℕ} (r : StageCertTests.PreparedScheduleRequest B1 B2) :
    (geometryProjection r).target=StagePrint.Context.geometryWord r := rfl

noncomputable def geometryProjectionBudget {B1 B2 : ℕ}
    (r : StageCertTests.PreparedScheduleRequest B1 B2) : ℕ :=
  fieldProjectionBudget (geometryProjection r)

noncomputable def geometryProjectionWordFunction (B1 B2 : ℕ) :
    WordFunction (StageCertTests.PreparedScheduleRequest B1 B2) StagePrint.Context.word
      (fun r=>frame (StagePrint.Context.geometryWord r)) geometryProjectionBudget := by
  let f:=restrictWordFunction (fieldProjectionWordFunction 3)
    (fun r : StageCertTests.PreparedScheduleRequest B1 B2=>geometryProjection r)
  refine ⟨f.program,?_⟩
  intro r
  simpa only [geometryProjection_word,geometryProjectionBudget,geometryProjection_target] using f.realizes r

noncomputable def baseGeometryBudget {B1 B2 : ℕ} (r : IndexedRequest B1 B2) : ℕ :=
  4*baseContextBudget r+4*geometryProjectionBudget r.prepared+12

/-- `imp:partition` and `lem:print`, paper/paper.tex: original BASE alone yields the real original star
header through actual context acquisition and finite field projection. -/
noncomputable def baseGeometryWordFunction (B1 B2 : ℕ) :
    WordFunction (IndexedRequest B1 B2) IndexedRequest.baseWord
      (fun r=>frame (StagePrint.Context.geometryWord r.prepared)) baseGeometryBudget := by
  let f:=Program.WordFunction.pipe (baseContextWordFunction B1 B2)
    (restrictWordFunction (geometryProjectionWordFunction B1 B2)
      (fun r : IndexedRequest B1 B2=>r.prepared))
  refine ⟨f.program,?_⟩
  intro r
  simpa only [baseGeometryBudget] using f.realizes r

/-- `lem:print`, paper/paper.tex: the actual
computed stacking width is physically read from the existing Tuple
input; no numeric field width is supplied to the original source. -/
def stackProjection (r : StageTuple.TermCutRequest) : FieldProjectionRequest 4 where
  fields:=[frame (callWord r.header.call),
    frame ((StagePrint.Header.baseHeaderValues r.header).flatMap natWord),r.contextWord,
    termsWord r.terms]
  target:=natWord r.stackWidth
  tail:=frame (natWord r.degree)++List.replicate 5 false
  prefix_length:=rfl

theorem stackProjection_word (r : StageTuple.TermCutRequest) :
    (stackProjection r).word=r.word := by
  simp only [stackProjection,FieldProjectionRequest.word,StageTuple.TermCutRequest.word,
    Top.loadRec,List.flatMap_cons,List.flatMap_nil,List.append_nil,frame,
    List.replicate_succ,List.replicate_zero,List.append_assoc]
  rfl

theorem stackProjection_target (r : StageTuple.TermCutRequest) :
    (stackProjection r).target=natWord r.stackWidth := rfl

noncomputable def stackProjectionBudget (r : StageTuple.TermCutRequest) : ℕ :=
  fieldProjectionBudget (stackProjection r)

noncomputable def stackProjectionWordFunction :
    WordFunction StageTuple.TermCutRequest StageTuple.TermCutRequest.word
      (fun r=>frame (natWord r.stackWidth)) stackProjectionBudget := by
  let f:=restrictWordFunction (fieldProjectionWordFunction 4) stackProjection
  refine ⟨f.program,?_⟩
  intro r
  simpa only [stackProjection_word,stackProjectionBudget,stackProjection_target] using f.realizes r

noncomputable def jobStackBudget {B1 B2 : ℕ} (r : TermJob B1 B2) : ℕ :=
  4*termRequestSourceBudget r+4*stackProjectionBudget (termRequest r.base r.index)+12

noncomputable def jobStackWordFunction (B1 B2 : ℕ) :
    WordFunction (TermJob B1 B2) TermJob.word
      (fun r=>frame (natWord (termRequest r.base r.index).stackWidth)) jobStackBudget := by
  let f:=Program.WordFunction.pipe (termRequestSourceWordFunction B1 B2)
    (restrictWordFunction stackProjectionWordFunction (fun r : TermJob B1 B2=>termRequest r.base r.index))
  refine ⟨f.program,?_⟩
  intro r
  simpa only [jobStackBudget] using f.realizes r

end NearQuarticWires.StageCertNative
