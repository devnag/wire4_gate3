import Proof.Quartic.StageTupleSetup.WidthCost
import Proof.Quartic.StageTupleSetup.LoadCost
import Proof.Quartic.StageTupleSetup.CoefficientInput
import Proof.Quartic.StageNativeRowCount.Cost

/-!
# The complete one-time cold setup clock

Paper: `lem:print` and `prop:time`,
paper/paper.tex.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageTupleSetupCold

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Interfaces
open StageTuple

/-- `lem:print`, paper/paper.tex: the
small row-count request contains the actual original finite header. -/
def rowRequest (r : TermCutRequest) : StageNativeRowCount.Request := ⟨r.header⟩

/-- `prop:time`, paper/paper.tex: the
twelve physical stages include source acquisition, six framing
passes, four one-shot ordinary helper calls and the complete prepared
formatter. Eleven sequencing instructions are charged explicitly.
Only source acquisition and the final formatter inspect Terms bytes. -/
def sourceStepsWith (bw : ℕ→ℕ) (br : StageNativeRowCount.Request→ℕ)
    (bc : CoefficientRequest→ℕ) (r : TermCutRequest) : ℕ :=
  r.sourceLoadCost+
  1000*((natWord r.stackWidth).length+1)+(2*bw r.stackWidth+2)+
  1000*(r.contextWord.length+1)+1000*((natWord r.degree).length+1)+
  1000*((frame ((StagePrint.Header.baseHeaderValues r.header).flatMap natWord)).length+1)+
  (2*br (rowRequest r)+2)+
  1000*((natWord (r.stackWidth+1)++intWord 0).length+1)+
  (2*bc (CoefficientRequest.mk (r.stackWidth+1) 0)+2)+
  1000*((natWord (r.stackWidth+1)++intWord 1).length+1)+
  (2*bc (CoefficientRequest.mk (r.stackWidth+1) 1)+2)+
  100000*(r.word.length+r.setupStructuralMagnitude)+11

/-- `prop:time`, paper/paper.tex: the
actual width, row-count and two coefficient machines determine the
complete source execution bound, without a supplied clock or cache. -/
noncomputable def sourceSteps (r : TermCutRequest) : ℕ :=
  sourceStepsWith StageTupleSetup.widthBudget StageNativeRowCount.Request.budget
    CoefficientRequest.budget r

/-- `prop:time`, paper/paper.tex: the
same public cold setup budget includes the actual source execution
and the final ordinary global head reset. -/
noncomputable def setupBudget (r : TermCutRequest) : ℕ :=2*sourceSteps r+2

end NearQuarticWires.StageTupleSetupCold
