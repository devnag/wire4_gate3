import Proof.Quartic.StagePrintTuple.Machine
import Proof.Quartic.StageTupleTermPrice.Final
import Proof.Quartic.StageTupleSetupCold.Final
import Proof.Quartic.StageTupleOuter.Core
import Proof.Quartic.StageTupleOuter.Sharp

set_option autoImplicit false

namespace NearQuarticWires.StageTuple

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Interfaces.Formats

/-- `lem:print` and `prop:time`, paper/paper.tex: the concrete original-source monomial printer binds
the actual native child-pool machine, its same proved source budget,
all genuine finite subroutines and the proved individual sharp clock.
It requires no extra algorithm, source, row, count or price premise. -/
noncomputable def termStageMachine :
    TermStageMachine StageNativeKids.nativeKidsWordFunction StageNativeKids.nativeStagePrice :=
  termStageMachineOfBound StageTupleTermPrice.termStageCostBound

/-- `lem:print` and `prop:time`, paper/paper.tex: the canonical cold tuple clock uses the actual
source preparation and the actual complete monomial implementation. -/
noncomputable def TermCutRequest.budget (r : TermCutRequest) : ℕ :=
  StageTupleOuter.termCutBudget termStageMachine StageTupleSetupCold.setupBudget r

/-- `lem:print`, paper/paper.tex: the complete
cold printer reads the unchanged original source request and emits
exactly its framed signed equality-cut stream using the actual fixed
preparation, original-child monomial and outer controller machines. -/
noncomputable def termCutWordFunction :
    WordFunction TermCutRequest TermCutRequest.word (fun r=>frame r.output) TermCutRequest.budget :=
  StageTupleOuter.termCutWordFunction termStageMachine StageTupleSetupCold.tupleSetupWordFunction

/-- `lem:print` and `prop:time`, paper/paper.tex: the actual cold printer has the unchanged sharp
degree-2D child census, with entire Terms bytes entering only additively
beside a polynomial in the separate structural magnitude. -/
theorem budget_sharp :
    ∃ C E : ℕ,1 ≤ C ∧ 1 ≤ E ∧ ∀ (r : TermCutRequest) (mc : ℕ),1 ≤ mc →
      (∀i,(r.toRowContext.nativeKids i).length ≤ mc) →
        r.budget ≤ C*(r.censusMagnitude mc)^E*
          ((1+17*(Builder.allGates r.header.call).length*mc)^(2*r.degree)+
            (termsWord r.terms).length+1) :=
  StageTupleOuter.budget_sharp termStageMachine StageTupleSetupCold.setupBudget_linear_source

end NearQuarticWires.StageTuple
