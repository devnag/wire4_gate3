import Proof.Quartic.StageTupleSetupCost.Clock

set_option autoImplicit false

namespace NearQuarticWires.StageTupleSetupCost

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Interfaces
open StageTuple

/-- `prop:time`, paper/paper.tex: one fixed
constant pays actual arithmetic compilers, framing and the global reset. -/
noncomputable def setupCostConstant : ℕ := 10^7*costFactor

/-- `lem:print` and `prop:time`, paper/paper.tex: the exact cold setup budget has additive
linear cost in complete source bytes and a separate structural polynomial.
The structural magnitude excludes Terms, Terms length and arithmetic hints. -/
theorem setupBudget_linear_source :
    StageTuple.TupleSetupCost StageTupleSetupCold.setupBudget := by
  refine ⟨setupCostConstant,9,?_⟩
  intro r
  have hs:=structural_bounds r
  have hp:=structural_powers r
  have hb:=helper_budgets r
  have hbytes:=small_bytes r
  have hA:=costFactor_bounds.1
  have hP : 1≤r.setupStructuralMagnitude^9 := Nat.one_le_pow _ _ (by have h:=hs.ten;omega)
  have hSP : r.setupStructuralMagnitude≤costFactor*r.setupStructuralMagnitude^9 :=
    hp.1.trans (Nat.le_mul_of_pos_left _ hA)
  have hAP : 1≤costFactor*r.setupStructuralMagnitude^9 := Nat.mul_pos hA hP
  have hnw : (natWord r.stackWidth).length≤4*r.setupStructuralMagnitude := by
    have h:=hbytes.1;omega
  have hctx : r.contextWord.length≤4*r.setupStructuralMagnitude := by
    have h:=hs.context;omega
  have hdeg : (natWord r.degree).length≤4*r.setupStructuralMagnitude := by
    have h:=hs.degree;omega
  have hhdr : (frame ((StagePrint.Header.baseHeaderValues r.header).flatMap natWord)).length≤
      4*r.setupStructuralMagnitude := by
    rw [NearCubicWires.RepairOrdinary.frame_length]
    have h:=hs.header
    have ht:=hs.ten
    omega
  have hc : StageTupleSetupCold.sourceSteps r≤
      100006*r.word.length+200000*(costFactor*r.setupStructuralMagnitude^9) := by
    unfold StageTupleSetupCold.sourceSteps StageTupleSetupCold.sourceStepsWith
    rw [StageTupleSetup.sourceLoadCost_linear]
    exact scalar_clock r.word.length r.setupStructuralMagnitude
      (costFactor*r.setupStructuralMagnitude^9)
      (natWord r.stackWidth).length r.contextWord.length (natWord r.degree).length
      (frame ((StagePrint.Header.baseHeaderValues r.header).flatMap natWord)).length
      (natWord (r.stackWidth+1)++intWord (0 : ℤ)).length
      (natWord (r.stackWidth+1)++intWord (1 : ℤ)).length
      (StageTupleSetup.widthBudget r.stackWidth)
      (StageTupleSetupCold.rowRequest r).budget
      (CoefficientRequest.mk (r.stackWidth+1) 0).budget
      (CoefficientRequest.mk (r.stackWidth+1) 1).budget
      hSP hAP hnw hctx hdeg hhdr hbytes.2.2.1 hbytes.2.2.2
      hb.1 hb.2.1 hb.2.2.1 hb.2.2.2
  exact scalar_reset r.word.length (r.setupStructuralMagnitude^9) costFactor
    (StageTupleSetupCold.sourceSteps r) hA hP hc

end NearQuarticWires.StageTupleSetupCost
