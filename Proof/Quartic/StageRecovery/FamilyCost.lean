import Proof.Quartic.StageRecovery.FamilyMachine

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageRecovery

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicGates.Close.Expand

/-- `prop:time`, paper/paper.tex: loading all original
support-family setup fields has a linear binary-word clock. -/
theorem FamilyRequest.loadCost_le (r : FamilyRequest) :
    r.loadCost ≤ 10000 * (r.arity + r.degree + 9) := by
  simp [FamilyRequest.loadCost, FamilyRequest.fields, Top.loadCost, Top.loadRec,
    Top.loadChainCost, frame_length, SignedSortKey.binary_length, FamilyRequest.width]
  omega

/-- `prop:time`, paper/paper.tex: every actual support
generation, level transition, copy, rewind and closure costs only one
linear family-count factor and a fixed polynomial in the finite dimensions. -/
theorem FamilyRequest.budget_le (r : FamilyRequest) :
    r.budget ≤ 10 ^ 9 * ((fam r.arity r.degree).length + 1) * (r.arity + r.degree + 9) ^ 4 := by
  let H := r.arity + r.degree + 9
  let N := (fam r.arity r.degree).length + 1
  have hH : 1 ≤ H := by dsimp [H]; omega
  have hN : 1 ≤ N := by dsimp [N]; omega
  have hw : r.width ≤ H := by dsimp [H, FamilyRequest.width]; omega
  have hv : r.arity ≤ H := by dsimp [H]; omega
  have hd : r.degree ≤ H := by dsimp [H]; omega
  have hn : (fam r.arity r.degree).length ≤ N := by dsimp [N]; omega
  have hload : r.loadCost ≤ 10000 * H := r.loadCost_le
  have hphase : famPhaseCost r.width r.arity r.degree (fam r.arity r.degree).length ≤
      famPhaseCost H H H N := by
    unfold famPhaseCost famInitCost famLoopCost famBodyCost vStepCost famTailCost
    gcongr
  have hsteps : r.steps ≤ 10000 * H + 1 + (16 * H + 14 + 1 + (16 * H + 14 + 1 +
      (famPhaseCost H H H N + 1 +
        (N * (40 * H + 11 + (50 * H + 30)) + 3 + 1 + (5 * (N * (2 * H + 1)) + 3))))) := by
    unfold FamilyRequest.steps
    rw [famRecs_length]
    gcongr
  have hH2 : H ≤ H ^ 2 := by nlinarith
  have hH3 : H ^ 2 ≤ H ^ 3 := by nlinarith
  have hH4 : H ^ 3 ≤ H ^ 4 := by nlinarith
  have hN1 := Nat.mul_le_mul_left N (hH2.trans (hH3.trans hH4))
  have hN2 := Nat.mul_le_mul_left N (hH3.trans hH4)
  have hN3 := Nat.mul_le_mul_left N hH4
  have hHN := Nat.mul_le_mul_right (H ^ 4) hN
  change 2 * r.steps + 2 ≤ 10 ^ 9 * N * H ^ 4
  unfold famPhaseCost famInitCost famLoopCost famBodyCost vStepCost famTailCost at hsteps
  nlinarith

end NearQuarticWires.StageRecovery
