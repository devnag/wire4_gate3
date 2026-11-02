import Proof.Quartic.StagePrintFinal.Components

/-!
# The exact complete printer clock

Paper: `prop:time`, paper/paper.tex.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrintFinal

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Interfaces
open StagePrint

/-- `prop:time`, paper/paper.tex: the
actual compiler reads the original raw indices once; its complete
clock has one additive raw-index polynomial. -/
theorem compiledTermsBudget_bound (B1 B2 : ℕ) :
    PrintBound ((StageCompiledTerms.compiledTermsProducer B1 B2).1) :=
  StageCompiledTerms.producerBudget_selected B1 B2

/-- `prop:time`, paper/paper.tex: the
first actual map pays only the carrier-envelope output bytes and the
whole collector clock, independently of raw index acquisition. -/
theorem collectedMap_bound {B1 B2 : ℕ} (S : Components B1 B2)
    (he : ColumnBound S.envelope.1) (hc : ColumnBound S.collector.1) :
    ColumnBound S.collectedMap.budget :=
  ColumnBound.middle S.collector.2 modulus targetCount S.collectedMap
    (ColumnBound.output_payload S.envelope.2 he) hc

/-- `prop:time`, paper/paper.tex: the
second map pays the preceding real map's output and the actual
native-header clock. No native table is supplied as an extra input. -/
theorem headerMap_bound
    (h : Bindings.Williams14.Williams14_Corollary4_4) {B1 B2 : ℕ}
    (S : Components B1 B2) (he : ColumnBound S.envelope.1)
    (hc : ColumnBound S.collector.1) : ColumnBound S.headerMap.budget := by
  have hh : ColumnBound (headerBudget (B1:=B1) (B2:=B2)) :=
    headerBudget_selected h B1 B2
  exact ColumnBound.middle (headerWordFunction B1 B2) modulus targetCount S.headerMap
    (ColumnBound.output_payload S.collectedMap.machine (collectedMap_bound S he hc)) hh

/-- `prop:time`, paper/paper.tex: all
stages after the original source compiler have column-polynomial
cost, including their literal ordinary-composition multipliers. -/
theorem downstream_bound
    (h : Bindings.Williams14.Williams14_Corollary4_4) {B1 B2 : ℕ}
    (S : Components B1 B2) (he : ColumnBound S.envelope.1)
    (hc : ColumnBound S.collector.1) :
    ColumnBound (fun r=>256*S.envelope.1 r+64*S.collectedMap.budget r+
      16*S.headerMap.budget r+4*(native r).recoveryBudget h+1020) := by
  have hr : ColumnBound (fun r : Greedy.PrintRequest B1 B2=>(native r).recoveryBudget h) :=
    recoveryBudget_selected h B1 B2
  exact ((((he.scale 256).add ((collectedMap_bound S he hc).scale 64)).add
    ((headerMap_bound h S he hc).scale 16)).add (hr.scale 4)).add
      (ColumnBound.const B1 B2 1020)

/-- `prop:time`, paper/paper.tex: the
same budget attached to the actual five-stage machine satisfies the
selected column cost plus one additive polynomial in raw index bits. -/
theorem budget_bound
    (h : Bindings.Williams14.Williams14_Corollary4_4) {B1 B2 : ℕ}
    (S : Components B1 B2) (he : ColumnBound S.envelope.1)
    (hc : ColumnBound S.collector.1) : PrintBound (budget h S) := by
  apply PrintBound.mono (((compiledTermsBudget_bound B1 B2).scale 256).add
    (downstream_bound h S he hc).to_print)
  intro r
  unfold budget
  rw [composeBudget_eq]
  omega

/-- `lem:print` and `prop:time`, paper/paper.tex: the actual complete printer and
its own selected cost supply precisely the final subroutine fields.
The envelope and collector remain explicit here so that the concrete
producer instantiation uses the same programs and clocks. -/
noncomputable def fieldOfComponents
    (h : Bindings.Williams14.Williams14_Corollary4_4) {B1 B2 : ℕ}
    (S : Components B1 B2) (he : ColumnBound S.envelope.1)
    (hc : ColumnBound S.collector.1) : Program.PrintField B1 B2 where
  printBudget:=budget h S
  print:=wordFunction h S
  Kp:=Classical.choose (budget_bound h S he hc)
  ep:=Classical.choose (Classical.choose_spec (budget_bound h S he hc))
  printCost:=Classical.choose_spec (Classical.choose_spec (budget_bound h S he hc))

end NearQuarticWires.StagePrintFinal
