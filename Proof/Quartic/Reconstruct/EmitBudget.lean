import Proof.Quartic.Reconstruct.EmitPack
import Proof.Quartic.StageMain.CompilerRuntime

/-!
# The budget of the emission stage

Paper: `prop:time`, paper/paper.tex.

With `U = a₁ 2^{c₁} (n+1)^{c₁}`, which bounds the width and the envelope of a child (`width_le_U`,
`envelope_le_U`), one item costs at most `10^9 U^6` steps (`itemCostQ_le`), the whole run at most
`2·10^9 U^6 (m + n_col + 1)` (`emitRunCost_le`), and the gathered word has at most `10^5·2 U^5 (|γ| + m + 1)` bits
(`gatheredWord_length_le`). The compiled budget is then at most `emitK B₁ (n+1)^{emitE B₁}` times the cost
`systemsCost` of the stage (`emitBudget_le`).
-/

set_option autoImplicit false

namespace NearQuarticWires.Reconstruct

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.Cells
open NearCubicGates.Close.Interfaces (listWord bitWord)
open NearQuarticWires.Greedy NearQuarticWires.Program

variable {B1 B2 : ℕ}

/-- The scale `U = a₁ 2^{c₁} (n+1)^{c₁}` of a child. -/
noncomputable def scaleU (B1 : ℕ) (q : ChildRequest B1 B2) : ℕ :=
  (emitSizes B1).a1 * 2 ^ (emitSizes B1).c1 * (q.call.n + 1) ^ (emitSizes B1).c1

theorem a1_ge (B1 : ℕ) : 100026 ≤ (emitSizes B1).a1 := by
  unfold emitSizes
  simp only
  have : 1 ≤ (Cells.ParameterArithmetic.preparationCoefficient B1 + 1) ^ 5 := Nat.one_le_pow _ _ (by omega)
  omega

theorem scaleU_facts (q : ChildRequest B1 B2) :
    (emitSizes B1).a1 ≤ scaleU B1 q ∧ (emitSizes B1).c1 ≤ scaleU B1 q ∧ q.call.n + 1 ≤ scaleU B1 q ∧
      128 ≤ scaleU B1 q := by
  have ha := a1_ge B1
  have h2 : 1 ≤ 2 ^ (emitSizes B1).c1 := Nat.one_le_two_pow
  have hc : (emitSizes B1).c1 < 2 ^ (emitSizes B1).c1 := Nat.lt_two_pow_self
  have hc1 : 1 ≤ (emitSizes B1).c1 := by unfold emitSizes; simp only; omega
  have hP : q.call.n + 1 ≤ (q.call.n + 1) ^ (emitSizes B1).c1 := by
    calc q.call.n + 1 = (q.call.n + 1) ^ 1 := (pow_one _).symm
      _ ≤ _ := Nat.pow_le_pow_right (by omega) hc1
  have hP1 : 1 ≤ (q.call.n + 1) ^ (emitSizes B1).c1 := Nat.one_le_pow _ _ (by omega)
  unfold scaleU
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc (emitSizes B1).a1 = (emitSizes B1).a1 * 1 * 1 := by ring
      _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul le_rfl h2) hP1
  · calc (emitSizes B1).c1 ≤ 1 * 2 ^ (emitSizes B1).c1 * 1 := by omega
      _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul (by omega) le_rfl) hP1
  · calc q.call.n + 1 ≤ 1 * 1 * (q.call.n + 1) ^ (emitSizes B1).c1 := by omega
      _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul (by omega) h2) le_rfl
  · calc 128 ≤ (emitSizes B1).a1 * 1 * 1 := by omega
      _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul le_rfl h2) hP1

/-- The width of the run is at most `U`. -/
theorem width_le_U (q : ChildRequest B1 B2) : (emitSizes B1).W (leadOnes (gatheredWord q)) ≤ scaleU B1 q := by
  unfold Sz.W scaleU
  rw [leadOnes_gatheredWord, pow_mul']
  have h := NearCubicGates.Close.CounterMachine.PrefixProg.pow_nbl_le q.call.n
  calc (2 ^ natBitLength q.call.n) ^ (emitSizes B1).c1 * (emitSizes B1).a1
      ≤ (2 * (q.call.n + 1)) ^ (emitSizes B1).c1 * (emitSizes B1).a1 :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_left h _)
    _ = _ := by rw [mul_pow]; ring

/-- The envelope of a child is below `U`. -/
theorem envelope_le_U (q : ChildRequest B1 B2) : envelope q + 1 ≤ scaleU B1 q := by
  have hV := envelope_succ_le q
  set c := Cells.ParameterArithmetic.preparationCoefficient B1
  have h1 : c + 1 ≤ (emitSizes B1).a1 := by
    show c + 1 ≤ 100026 * (c + 1) ^ 5
    have : c + 1 ≤ (c + 1) ^ 5 := Nat.le_self_pow (by norm_num) _
    omega
  have h2 : (q.call.n + 1) ^ (B1 + 12) ≤ (q.call.n + 1) ^ (emitSizes B1).c1 :=
    Nat.pow_le_pow_right (by omega) (by unfold emitSizes; simp only; omega)
  have h3 : 1 ≤ 2 ^ (emitSizes B1).c1 := Nat.one_le_two_pow
  unfold scaleU
  calc envelope q + 1 ≤ (c + 1) * (q.call.n + 1) ^ (B1 + 12) := hV
    _ ≤ (emitSizes B1).a1 * 2 ^ (emitSizes B1).c1 * (q.call.n + 1) ^ (emitSizes B1).c1 := by
      calc (c + 1) * (q.call.n + 1) ^ (B1 + 12) = (c + 1) * 1 * (q.call.n + 1) ^ (B1 + 12) := by ring
        _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul h1 h3) h2

theorem natBitLength_le_succ' (x : ℕ) : natBitLength x ≤ x + 1 :=
  natBitLength_le_of_lt_two_pow (Nat.lt_two_pow_self.trans (Nat.pow_lt_pow_right (by norm_num) (by omega)))
    (by omega)

/-- **One item costs at most `10^9 U^6` steps.** -/
theorem itemCost_le (J W V U : ℕ) (hU : 1 ≤ U) (hJ : J ≤ U) (hW : W ≤ U) (hV : V ≤ U) :
    itemAxesCost J W + itemEmitCost W (W - 2) (16 * V + 1) (16 * V + 1) (100000 * V ^ 5) + 1 ≤
      1000000000 * U ^ 6 := by
  have e1 : ∀ x, emitNatDCost 2 x = 36 * x + 108 := fun x => by unfold emitNatDCost; norm_num; ring
  have p1 : U ≤ U ^ 2 := by nlinarith
  have p2 : U ^ 2 ≤ U ^ 3 := Nat.pow_le_pow_right hU (by norm_num)
  have p3 : U ^ 3 ≤ U ^ 6 := Nat.pow_le_pow_right hU (by norm_num)
  have p5 : U ^ 5 ≤ U ^ 6 := Nat.pow_le_pow_right hU (by norm_num)
  have hL : 16 * V + 1 ≤ 17 * U := by omega
  have hR : 5 * (100000 * V ^ 5) + 1 ≤ 500001 * U ^ 5 := by
    have : V ^ 5 ≤ U ^ 5 := Nat.pow_le_pow_left hV 5
    have : 1 ≤ U ^ 5 := Nat.one_le_pow _ _ (by omega)
    omega
  -- the parts
  have hA : itemAxesCost J W ≤ 1036 * U ^ 2 := by
    unfold itemAxesCost
    have := Nat.mul_le_mul (show 2 * J + 2 ≤ 4 * U by omega) (show 60 * W + 88 ≤ 148 * U by omega)
    nlinarith
  have hpc : pointCost 2 (W - 2) + 4 ≤ 804 * U := by
    unfold pointCost emitShiftCost; rw [e1, e1]; omega
  have hcc : copyCost 2 (W - 2) + 4 ≤ 209 * U := by
    unfold copyCost; rw [e1]; omega
  have hLL : (16 * V + 1) * (16 * V + 1) ≤ 289 * U ^ 2 := by
    have := Nat.mul_le_mul hL hL; nlinarith
  have hP : pointsCost 2 (W - 2) (16 * V + 1) (16 * V + 1) ≤ 232492 * U ^ 3 + 10558 * U ^ 2 := by
    unfold pointsCost
    rw [e1]
    have h1 : (16 * V + 1) * (pointCost 2 (W - 2) + 4) ≤ 17 * U * (804 * U) := Nat.mul_le_mul hL hpc
    have h2 : (16 * V + 1) * ((16 * V + 1) * (pointCost 2 (W - 2) + 4) + 8) ≤ 17 * U * (17 * U * (804 * U) + 8) :=
      Nat.mul_le_mul hL (by omega)
    have h3 := natBitLength_le_succ' ((16 * V + 1) * (16 * V + 1))
    have h4 : 17 * U * (17 * U * (804 * U) + 8) ≤ 232492 * U ^ 3 := by nlinarith
    nlinarith
  have hC : (5 * (100000 * V ^ 5) + 1) * (copyCost 2 (W - 2) + 4) ≤ 104500209 * U ^ 6 := by
    have := Nat.mul_le_mul hR hcc
    have e : 500001 * U ^ 5 * (209 * U) = 104500209 * U ^ 6 := by ring
    omega
  unfold itemEmitCost
  rw [e1]
  nlinarith

end NearQuarticWires.Reconstruct
