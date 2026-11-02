import Proof.Quartic.StagePrintContext.SourceCost
import Proof.Quartic.StageFormulaMetadata.Cost
import Proof.Quartic.StageCertTests.PreparedPolynomial

set_option autoImplicit false

namespace NearQuarticWires.StagePrintContext

open NearCubicWires
open NearCubicGates.Close.Cells
open StageCertTests StageFormulaMetadata

/-- `prop:time`, paper/paper.tex: measured
allocation, actual binary compilation, output movement and every final
head return have a fixed polynomial bound in the real finite source. -/
theorem contextBudget_bound {B1 B2 : ℕ} (r : PreparedScheduleRequest B1 B2) :
    contextBudget r≤10^25*(r.word.length+1)^8 := by
  have hsource:=contextSteps_bound r
  have hmono:=finiteBudget_mono StageRecovery.packetCallee VV MM r.word (contextSteps r)
    (100000000*(r.word.length+1)^3) hsource
  unfold contextBudget
  refine hmono.trans ?_
  dsimp only [finiteBudget,finiteInitializeCost,finiteSetupACost,finiteWidth,costB,costC]
  rw [show TSK StageRecovery.packetCallee=3 from rfl]
  norm_num [VV,MM]
  ring_nf
  omega

/-- `lem:print` and `prop:time`, paper/paper.tex: the actual cold context producer has polynomial
ordinary running time in its original call word, uniformly over all
proposed witness words and both downstream moment modes. -/
theorem contextProducer_polynomial (B1 B2 : ℕ) :
    PreparedPolynomial ((contextProducer B1 B2).1) := by
  have hm : PreparedPolynomial (B1:=B1) (B2:=B2) (fun r=>
      10^25*(r.word.length+1)^8) :=
    (PreparedPolynomial.const (10^25)).mul
      ((PreparedPolynomial.inputLength.add (PreparedPolynomial.const 1)).pow 8)
  exact hm.mono fun r=>contextBudget_bound r

end NearQuarticWires.StagePrintContext
