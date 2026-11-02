import Proof.Quartic.StagePrintFinal.Producers
import Proof.Quartic.StageCarrierEnvelope.Cost

/-!
# The actual original-source carrier envelope in the complete printer

Paper: `lem:print` and `prop:time`,
paper/paper.tex.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrintFinal

open NearCubicWires NearCubicWires.RepairOrdinary
open StagePrint

/-- `prop:time`, paper/paper.tex: the
actual carrier-only envelope program retains its own linear source
clock, with polynomial overhead in original arity and no repeated
raw-index acquisition cost. -/
theorem actualEnvelope_bound (B1 B2 : ℕ) :
    StageGreedyCollector.ContextBudgetBound
      (StageCarrierEnvelope.carrierEnvelopeProducer B1 B2).1 := by
  obtain ⟨K,e,hK⟩:=StageCarrierEnvelope.carrierEnvelopeProducer_budget B1 B2
  refine ⟨K,e,fun r=>?_⟩
  exact (hK r).trans_eq (by ring)

/-- `lem:print`, paper/paper.tex: the
original source, actual carrier-envelope program, both actual cold
middle maps, actual native header and actual native recovery are
fixed. Only the whole-cut collector remains an explicit component. -/
noncomputable def componentsOfCollector {B1 B2 : ℕ}
    (C : GreedyCollector.Producer B1 B2) : Components B1 B2 :=
  componentsOfProducers (StageCarrierEnvelope.carrierEnvelopeProducer B1 B2) C

/-- `lem:print`, `lem:residue` and `prop:time`,
paper/paper.tex:
the actual source-to-recovery printer and its same selected budget
are instantiated with the concrete source-only envelope. The sole
remaining explicit program is the whole-cut collector, with its own
original-column bound. -/
noncomputable def fieldOfCollector
    (h : Bindings.Williams14.Williams14_Corollary4_4) {B1 B2 : ℕ}
    (C : GreedyCollector.Producer B1 B2) (hc : ColumnBound C.1) :
    Program.PrintField B1 B2 :=
  fieldOfProducers h (StageCarrierEnvelope.carrierEnvelopeProducer B1 B2) C
    (actualEnvelope_bound B1 B2) hc

end NearQuarticWires.StagePrintFinal
