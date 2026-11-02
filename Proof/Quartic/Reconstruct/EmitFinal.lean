import Proof.Quartic.Reconstruct.EmitBound

/-!
# The emission stage within `K (n+1)^e` times its cost

Paper: Step 3 of `sec:algorithm`, paper/paper.tex, and `prop:time`.

`emitBudget_le`: the compiled budget of the emission stage is at most `emitK B₁ (n+1)^{emitE B₁} · systemsCost q`.
`emitStage` is the stage `gatheredWord ↦ frame systemsWord` with this budget, the `emit` argument of
`SystemsSplit.systemsOfSplit`.
-/

set_option autoImplicit false

namespace NearQuarticWires.Reconstruct

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.Cells
open NearQuarticWires.Greedy NearQuarticWires.Program
open NearCubicWires.RepairOrdinary (WordFunction frame)

variable {B1 B2 : ℕ}

/-- The tape count of the (unused) callee of the stage. -/
noncomputable def emitTapes : ℕ := TSK NearCubicGates.Close.CounterMachine.PrefixProg.noCallee

/-- The constant of the emission stage. -/
noncomputable def emitK (B1 : ℕ) : ℕ :=
  30000000000000 * (201 + emitTapes) ^ 2 * ((emitSizes B1).a1 * 2 ^ (emitSizes B1).c1) ^ 8

/-- The exponent of the emission stage. -/
def emitE (B1 : ℕ) : ℕ := 8 * (emitSizes B1).c1

theorem scaleU_pow (q : ChildRequest B1 B2) :
    scaleU B1 q ^ 8 = ((emitSizes B1).a1 * 2 ^ (emitSizes B1).c1) ^ 8 * (q.call.n + 1) ^ emitE B1 := by
  unfold scaleU emitE
  rw [mul_pow, ← pow_mul, mul_comm (emitSizes B1).c1 8]

/-- **The budget of the emission stage.** -/
theorem emitBudget_le (q : ChildRequest B1 B2) :
    emitBudget B1 q ≤ emitK B1 * (q.call.n + 1) ^ emitE B1 * systemsCost q := by
  obtain ⟨ha, hc, hn, h128⟩ := scaleU_facts q
  have hWU := width_le_U q
  have hVU := envelope_le_U q
  set U := scaleU B1 q with hU
  set T := emitTapes with hT
  set S := U + 200 + T with hS
  have hL : leadOnes (gatheredWord q) ≤ S := by
    rw [leadOnes_gatheredWord]; have := natBitLength_le_succ' q.call.n; omega
  have hlang := NearQuarticWires.StageMain.Runtime.langBudget_le
    NearCubicGates.Close.CounterMachine.PrefixProg.noCallee (emitSizes B1) VV MM (gatheredWord q)
    (emitRunCost q ((emitSizes B1).W (leadOnes (gatheredWord q)))) S (by omega) (show (128 : ℕ) ≤ S by omega) (show (10 : ℕ) ≤ S by omega)
    (show T ≤ S by omega) (by omega) (by omega) (by simp [emitSizes]) (by simp [emitSizes]) (by simp [emitSizes])
    (by simp [emitSizes]) hL (by omega) (by simp [Sz.Lk, emitSizes]) (by simp [Sz.Bk, emitSizes])
  have hN := emitRunCost_le q ((emitSizes B1).W (leadOnes (gatheredWord q))) U (by omega) hWU hVU
  have hI := gatheredWord_length_le q U hVU
  have hTm := emit_terms_le q
  set m := (systemList q).length
  set Z := q.cellCall.ncol
  set G := (gammaWord q).length
  have hU1 : 1 ≤ U := by omega
  have p56 : U ^ 5 ≤ U ^ 6 := Nat.pow_le_pow_right hU1 (by norm_num)
  have hU6 : 1 ≤ U ^ 6 := Nat.one_le_pow _ _ (by omega)
  -- the run and the input
  have hNI : emitRunCost q ((emitSizes B1).W (leadOnes (gatheredWord q))) + (gatheredWord q).length + 1 ≤
      3000000000 * U ^ 6 * (m + Z + G + 1) := by
    have e1 : 2000000000 * U ^ 6 * (m + Z + 1) ≤ 2000000000 * (U ^ 6 * (m + Z + G + 1)) := by
      rw [mul_assoc]; exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))
    have e2 : 100200 * U ^ 5 * (G + m + 1) ≤ 100200 * (U ^ 6 * (m + Z + G + 1)) := by
      rw [mul_assoc]; exact Nat.mul_le_mul_left _ (Nat.mul_le_mul p56 (by omega))
    have e3 : 1 ≤ U ^ 6 * (m + Z + G + 1) := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by positivity) (by omega))
    have e4 : 3000000000 * U ^ 6 * (m + Z + G + 1) = 3000000000 * (U ^ 6 * (m + Z + G + 1)) := by ring
    omega
  have hSU : S ≤ (201 + T) * U := by nlinarith
  have hS2 : S ^ 2 ≤ (201 + T) ^ 2 * U ^ 2 := by
    rw [← mul_pow]; exact Nat.pow_le_pow_left hSU 2
  calc emitBudget B1 q ≤ 10000 * S ^ 2 * (emitRunCost q ((emitSizes B1).W (leadOnes (gatheredWord q))) +
        (gatheredWord q).length + 1) := hlang
    _ ≤ 10000 * ((201 + T) ^ 2 * U ^ 2) * (3000000000 * U ^ 6 * (m + Z + G + 1)) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ hS2) hNI
    _ = 30000000000000 * (201 + T) ^ 2 * U ^ 8 * (m + Z + G + 1) := by ring
    _ ≤ 30000000000000 * (201 + T) ^ 2 * U ^ 8 * systemsCost q := Nat.mul_le_mul_left _ hTm
    _ = emitK B1 * (q.call.n + 1) ^ emitE B1 * systemsCost q := by
        rw [scaleU_pow]; unfold emitK; ring

/-- **The emission stage** `gatheredWord ↦ frame systemsWord` within `emitK B₁ (n+1)^{emitE B₁} systemsCost q`. -/
noncomputable def emitStage (B1 B2 : ℕ) :
    WordFunction (ChildRequest B1 B2) gatheredWord (fun q => frame (systemsWord q))
      (fun q => emitK B1 * (q.call.n + 1) ^ emitE B1 * systemsCost q) :=
  WordFunction.enlargeBudget (emitWF B1 B2) emitBudget_le

end NearQuarticWires.Reconstruct
