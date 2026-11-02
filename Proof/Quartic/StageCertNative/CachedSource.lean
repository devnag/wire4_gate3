import Proof.Quartic.StageCertNative.PrepCopy
import Proof.Quartic.StageCertNative.CountMachine
import Proof.Quartic.StageRecovery.FramedPair

set_option autoImplicit false

namespace NearQuarticWires.StageCertNative
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open StageCertificateControl

/-- `lem:print`, paper/paper.tex: the original
BASE source and once-computed eleven-field context form one retained
source for all actual terms of the same whole test. -/
noncomputable def retainedContextBudget {B1 B2 : ℕ} (r : IndexedRequest B1 B2) : ℕ :=
  2*StageGamma.retainedCost (input:=IndexedRequest.baseWord)
    (cache:=fun r : IndexedRequest B1 B2=>StagePrint.Context.word r.prepared)
    (budget:=baseContextBudget) r+2

noncomputable def retainedContextWordFunction (B1 B2 : ℕ) :
    WordFunction (IndexedRequest B1 B2) IndexedRequest.baseWord
      (fun r=>frame (r.baseWord++StagePrint.Context.word r.prepared)) retainedContextBudget :=
  StageGamma.retainedWordFunction (baseContextWordFunction B1 B2)

/-- `lem:print` and `prop:time`, paper/paper.tex: the actual binary term count is computed once and
retained beside the literal BASE and shared context; none is an input
oracle or a newly supplied preparation field. -/
noncomputable def cachedSourceWord {B1 B2 : ℕ} (r : IndexedRequest B1 B2) : List Bool :=
  natWord (termCount r)++r.baseWord++StagePrint.Context.word r.prepared

noncomputable def cachedSourceBudget {B1 B2 : ℕ} (r : IndexedRequest B1 B2) : ℕ :=
  2*StageRecovery.FramedPair.cost (input:=IndexedRequest.baseWord)
    (left:=fun r : IndexedRequest B1 B2=>natWord (termCount r))
    (right:=fun r : IndexedRequest B1 B2=>r.baseWord++StagePrint.Context.word r.prepared)
    (lb:=countBudget) (rb:=retainedContextBudget) r+2

/-- `lem:print` and `prop:time`, paper/paper.tex: one fixed physical machine builds the actual shared
counted context before the whole-term loop starts, including all
original source copies, both binary calculations and stream cleanup. -/
noncomputable def cachedSourceWordFunction (B1 B2 : ℕ) :
    WordFunction (IndexedRequest B1 B2) IndexedRequest.baseWord
      (fun r=>frame (cachedSourceWord r)) cachedSourceBudget :=
by
  let f:=StageRecovery.FramedPair.wordFunction (countWordFunction B1 B2)
    (retainedContextWordFunction B1 B2)
  refine ⟨f.program,?_⟩
  intro r
  simpa only [cachedSourceWord,cachedSourceBudget,List.append_assoc] using f.realizes r

end NearQuarticWires.StageCertNative
