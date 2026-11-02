import Proof.Quartic.StagePrintFinal.Selected
import Proof.Quartic.StageNativeMiddleMap.Machine

/-!
# Concrete metadata-preserving maps of the whole printer

Paper: `lem:print` and `prop:time`,
paper/paper.tex.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrintFinal

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Interfaces
open StagePrint

/-- `lem:print`, paper/paper.tex: both
metadata-preserving maps are the actual cold ordinary program. The
collector is called once in the first map and the actual native
header is called once in the second, with their unchanged budgets. -/
noncomputable def componentsOfProducers {B1 B2 : ℕ}
    (E : CarrierEnvelope.Producer B1 B2) (C : GreedyCollector.Producer B1 B2) :
    Components B1 B2 where
  envelope:=E
  collector:=C
  collectedMap:=StageNativeMiddleMap.middleMapper C.2 modulus targetCount
  headerMap:=StageNativeMiddleMap.middleMapper (headerWordFunction B1 B2) modulus targetCount

/-- `lem:print` and `prop:time`, paper/paper.tex: an actual linear carrier envelope
and actual whole-cut collector instantiate the complete printer.
Every mapper, compiler, native header and recovery program is the
concrete one, and the final fields retain their composed budget. -/
noncomputable def fieldOfProducers
    (h : Bindings.Williams14.Williams14_Corollary4_4) {B1 B2 : ℕ}
    (E : CarrierEnvelope.Producer B1 B2) (C : GreedyCollector.Producer B1 B2)
    (he : StageGreedyCollector.ContextBudgetBound E.1) (hc : ColumnBound C.1) :
    Program.PrintField B1 B2 :=
  fieldOfComponents h (componentsOfProducers E C) (ColumnBound.of_carrier he) hc

end NearQuarticWires.StagePrintFinal
