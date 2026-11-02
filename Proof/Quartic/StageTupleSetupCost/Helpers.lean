import Proof.Quartic.StageTupleSetupCost.Structural

set_option autoImplicit false

namespace NearQuarticWires.StageTupleSetupCost

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Interfaces
open StageTuple

/-- `prop:time`, paper/paper.tex: one fixed
constant dominates the actual width, row and fixed-coefficient compilers. -/
noncomputable def costFactor : ℕ :=
  512*(StageTupleSetup.widthCostConstant+StageNativeRowCount.costConstant+10^20+1)

theorem costFactor_bounds : 1≤costFactor ∧
    StageTupleSetup.widthCostConstant≤costFactor ∧
    64*StageNativeRowCount.costConstant≤costFactor ∧
    512*10^20≤costFactor := by
  unfold costFactor
  omega

/-- `prop:time`, paper/paper.tex: the
small actual helper calls depend only on the separate structural scale. -/
theorem helper_budgets (r : TermCutRequest) :
    StageTupleSetup.widthBudget r.stackWidth≤costFactor*r.setupStructuralMagnitude^9 ∧
    (StageTupleSetupCold.rowRequest r).budget≤costFactor*r.setupStructuralMagnitude^9 ∧
    (CoefficientRequest.mk (r.stackWidth+1) 0).budget≤costFactor*r.setupStructuralMagnitude^9 ∧
    (CoefficientRequest.mk (r.stackWidth+1) 1).budget≤costFactor*r.setupStructuralMagnitude^9 := by
  have hs:=structural_bounds r
  have hp:=structural_powers r
  have hc:=costFactor_bounds
  have hw:=StageTupleSetup.widthBudget_polynomial r.stackWidth
  have hwp:=Nat.pow_le_pow_left hs.width 3
  have hwidth : StageTupleSetup.widthBudget r.stackWidth≤costFactor*r.setupStructuralMagnitude^9 :=
    hw.trans ((Nat.mul_le_mul_left _ (hwp.trans hp.2.1)).trans
      (Nat.mul_le_mul_right _ hc.2.1))
  have hrscale : (StageTupleSetupCold.rowRequest r).header.call.n+
      (StageTupleSetupCold.rowRequest r).word.length+1≤2*r.setupStructuralMagnitude := by
    simp only [StageTupleSetupCold.rowRequest,StageNativeRowCount.Request.word,
      StageNativeRowCount.Request.payload,NearCubicWires.RepairOrdinary.frame_length]
    have hh:=hs.header
    unfold TermCutRequest.setupStructuralMagnitude
    omega
  have hr:=StageNativeRowCount.Request.budget_polynomial (StageTupleSetupCold.rowRequest r)
  have hrp:=Nat.mul_le_mul_left StageNativeRowCount.costConstant
    (Nat.pow_le_pow_left hrscale 6)
  have hrid (S K : ℕ) : K*(2*S)^6=64*K*S^6 := by ring
  rw [hrid] at hrp
  have hrow : (StageTupleSetupCold.rowRequest r).budget≤costFactor*r.setupStructuralMagnitude^9 :=
    (hr.trans hrp).trans ((Nat.mul_le_mul_left _ hp.2.2).trans
      (Nat.mul_le_mul_right _ hc.2.2.1))
  have hcoeff (z : ℤ) (hz : (intWord z).length=6) :
      (CoefficientRequest.mk (r.stackWidth+1) z).budget≤costFactor*r.setupStructuralMagnitude^9 := by
    have hscale : (r.stackWidth+1)+(intWord z).length+1≤2*r.setupStructuralMagnitude := by
      rw [hz]
      have hh:=hs.width
      have ht:=hs.ten
      omega
    have h:=StageTupleSetup.coefficientBudget_polynomial
      (CoefficientRequest.mk (r.stackWidth+1) z)
    change _≤10^20*((r.stackWidth+1)+(intWord z).length+1)^9 at h
    have hp:=Nat.mul_le_mul_left (10^20) (Nat.pow_le_pow_left hscale 9)
    have hid (S : ℕ) : 10^20*(2*S)^9=(512*10^20)*S^9 := by ring
    rw [hid] at hp
    exact (h.trans hp).trans (Nat.mul_le_mul_right _ hc.2.2.2)
  exact ⟨hwidth,hrow,hcoeff 0 fixed_integer_bytes.1,hcoeff 1 fixed_integer_bytes.2⟩

end NearQuarticWires.StageTupleSetupCost
