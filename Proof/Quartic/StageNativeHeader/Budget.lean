import Proof.Quartic.StageNativeHeader.Sizes

/-!
# The clock of the native header printer

Paper: `prop:time`, paper/paper.tex.

With `V = n + p + 2` and `X = |stream| + U² + 1`, the run costs at most `10^20 V^6 X` steps (`runCost_le`): one call of
the column printer (`≤ 10^17 (n+2)^6`), the emission (`10^12 V^4 X`), and parts linear in the cut bytes, `U²` and the
output, times `V`. Hence `2·runCost + 2 ≤ 10^30 V^20 X`, the budget of `NativeHeaderPrinter` (`budget_le`).
-/

set_option autoImplicit false

namespace NearQuarticWires.StageNativeHeader

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearQuarticWires.StagePrint NearQuarticWires.StagePrint.Downstream

theorem tsk_col : NearCubicGates.Close.Cells.TSK StageColumns.columnCallee = 3 := by
  simp [NearCubicGates.Close.Cells.TSK, StageColumns.columnCallee, NearCubicGates.Close.Interfaces.wordFunction_of_wmx,
    NearCubicGates.Close.Interfaces.wmxProgram]

theorem columnBudget_le (P : StarParams) : StageColumns.columnBudget P ≤ 10 ^ 17 * (P.n + 2) ^ 6 := by
  have h := StageColumns.columnBudget_fixed P
  rw [tsk_col] at h
  have : 1 ≤ (P.n + 2) ^ 6 := Nat.one_le_pow _ _ (by omega)
  nlinarith

/-- **The clock of the run.** -/
theorem runCost_le (r : NativeHeaderRequest) :
    runCost r ≤ 10 ^ 20 * ((r.parameters.n + r.table.matrix.p + 2) ^ 6 * (r.stream.length + r.table.count + 1)) := by
  obtain ⟨V, hV⟩ : ∃ V, V = r.parameters.n + r.table.matrix.p + 2 := ⟨_, rfl⟩
  obtain ⟨X, hX⟩ : ∃ X, X = r.stream.length + r.table.count + 1 := ⟨_, rfl⟩
  rw [← hV, ← hX]
  obtain ⟨hr, hb, hs, hw, hd⟩ := params_le r.parameters
  have hX1 : 1 ≤ X := by omega
  have hV2 : 2 ≤ V := by omega
  have q2 : V ≤ V ^ 2 := by nlinarith
  have q26 : V ^ 2 ≤ V ^ 6 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have q46 : V ^ 4 ≤ V ^ 6 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have y6 : V ^ 6 ≤ V ^ 6 * X := Nat.le_mul_of_pos_right _ (by omega)
  have yX : X ≤ V ^ 6 * X := Nat.le_mul_of_pos_left _ (Nat.one_le_pow _ _ (by omega))
  have y4 : V ^ 4 * X ≤ V ^ 6 * X := Nat.mul_le_mul_right _ q46
  have yS : V * r.stream.length ≤ V ^ 6 * X := Nat.mul_le_mul (q2.trans q26) (by omega)
  have sq : ∀ x, x ≤ r.parameters.n + r.table.matrix.p → (x + 2) ^ 2 ≤ V ^ 2 := fun x hx =>
    Nat.pow_le_pow_left (by omega) 2
  -- the pieces
  have e1 : parseCost r ≤ 1000 * V ^ 2 + 4 := by
    unfold parseCost
    have := readCost_le r.parameters.n; have := readCost_le r.parameters.r; have := readCost_le r.parameters.b
    have := readCost_le r.parameters.s; have := readCost_le r.table.matrix.p
    have := sq r.parameters.n (by omega); have := sq r.parameters.r (by omega); have := sq r.parameters.b (by omega)
    have := sq r.parameters.s (by omega); have := sq r.table.matrix.p (by omega)
    omega
  have hci := StageColumns.columnInput_length_le r.parameters
  have e2 : bankCost r.parameters ≤ 8000 * V ^ 2 + 144 * V + 60 := by
    unfold bankCost
    have := writeCost_le r.parameters.n; have := writeCost_le r.parameters.r; have := writeCost_le r.parameters.b
    have := writeCost_le r.parameters.s
    have := sq r.parameters.n (by omega); have := sq r.parameters.r (by omega); have := sq r.parameters.b (by omega)
    have := sq r.parameters.s (by omega)
    omega
  have hB := columnBudget_le r.parameters
  have hB6 : (r.parameters.n + 2) ^ 6 ≤ V ^ 6 := Nat.pow_le_pow_left (by omega) 6
  have e3 : callAppendCost (StageColumns.columnInput r.parameters).length (StageColumns.columnBudget r.parameters) ≤
      3601 * V + 3 * 10 ^ 19 * V ^ 6 + 300 := by
    unfold callAppendCost; omega
  have hcc := colsContent_length_le r.parameters
  have e4 : widthCost r.parameters ≤ 800 * V ^ 2 + 100 := by
    unfold widthCost
    have := readCost_le (PrimT.C4Geo.width r.parameters); have := sq (PrimT.C4Geo.width r.parameters) (by omega)
    have := sq r.parameters.n (by omega)
    rw [RepairOrdinary.frame_length]; omega
  have e5 : dimsCost r.parameters ≤ 200 * V ^ 2 + 100 := by
    unfold dimsCost
    have h1 : r.parameters.r / 2 * (18 * r.parameters.s + 9) ≤ r.parameters.n * (18 * r.parameters.n + 9) :=
      Nat.mul_le_mul (by omega) (by omega)
    have h2 : r.parameters.r / 2 * r.parameters.s ≤ r.parameters.n * r.parameters.n :=
      Nat.mul_le_mul (by omega) (by omega)
    have h3 : (r.parameters.n + 2) ^ 2 ≤ V ^ 2 := sq r.parameters.n (by omega)
    nlinarith
  have hG := cuts_le_stream r
  have e6 : countCost r ≤ 100 * (V * r.stream.length) + 100 := by
    unfold countCost
    have h1 : r.table.matrix.cuts.length * (22 * (2 * PrimT.C4Geo.width r.parameters + 2) + 11) ≤
        r.stream.length * (55 * V) := Nat.mul_le_mul hG (by omega)
    have h2 : r.stream.length * (55 * V) = 55 * (V * r.stream.length) := by ring
    have h3 : 2 * r.stream.length ≤ V * r.stream.length := Nat.mul_le_mul_right _ hV2
    omega
  have e7 : emitCost r ≤ 10 ^ 12 * (V ^ 6 * X) := by
    unfold emitCost
    rw [← hV, ← hX]
    calc 10 ^ 12 * V ^ 4 * X = 10 ^ 12 * (V ^ 4 * X) := by ring
      _ ≤ 10 ^ 12 * (V ^ 6 * X) := Nat.mul_le_mul_left _ y4
  have e8 := tableWord_length_le r
  rw [← hV] at e8
  have e9 : V ^ 2 ≤ V ^ 6 * X := q26.trans y6
  unfold runCost preCost postCost
  omega

/-- **The budget of `NativeHeaderPrinter` covers the run.** -/
theorem budget_le (r : NativeHeaderRequest) :
    2 * runCost r + 2 ≤ 10 ^ 30 * (r.parameters.n + r.table.matrix.p + 2) ^ 20 *
      (r.stream.length + r.table.count + 1) := by
  have h := runCost_le r
  set V := r.parameters.n + r.table.matrix.p + 2
  set X := r.stream.length + r.table.count + 1
  have hV : 1 ≤ V := by omega
  have hX : 1 ≤ X := by omega
  have h620 : V ^ 6 ≤ V ^ 20 := Nat.pow_le_pow_right hV (by norm_num)
  have hY : 1 ≤ V ^ 6 * X := Nat.mul_pos (Nat.one_le_pow _ _ hV) hX
  have : V ^ 6 * X ≤ V ^ 20 * X := Nat.mul_le_mul_right _ h620
  calc 2 * runCost r + 2 ≤ 3 * 10 ^ 20 * (V ^ 6 * X) := by omega
    _ ≤ 10 ^ 30 * (V ^ 20 * X) := by omega
    _ = 10 ^ 30 * V ^ 20 * X := by ring

end NearQuarticWires.StageNativeHeader
