import Proof.Quartic.Reconstruct.EmitHeadRun
import Proof.Gates.CounterMachine.PrefixRun

/-!
# The emission stage: from the gathered word to the framed systems

Paper: Step 3 of `sec:algorithm`, paper/paper.tex.

`emitS` sets the constants, reads the context and the number of systems (`EmitHeadRun.headS_spec`), writes the
system of every gathered item (`EmitLoop.itemsLoopS_spec`) and the end mark. Run on `gatheredWord q` with a width of
at least `emitWidth q` it prints `frame (systemsWord q)` (`emitS_run`).
-/

set_option autoImplicit false

namespace NearQuarticWires.Reconstruct

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.Cells
open NearCubicGates.Close.Interfaces (listWord bitWord)
open NearQuarticWires.Greedy NearQuarticWires.Program

variable {B1 B2 : ℕ}

/-- The emission program. -/
def emitS : St VV MM :=
  .seq NearCubicGates.Close.CounterMachine.PrefixProg.cstInit (.seq headS (.seq itemsLoopS (putD 0 false)))

/-- The certified bits as numbers. -/
noncomputable def certNats (q : ChildRequest B1 B2) : List ℕ :=
  (certifiedBits q.cellCall).map fun b => if b then 1 else 0

/-- **The gathered word** is the word read by `headS` followed by the gathered items. -/
theorem gatheredWord_eq (q : ChildRequest B1 B2) :
    gatheredWord q = headWord q.call.n q.selected.1.M1 q.selected.1.A q.selected.1.Lambda q.cellCall.J
        (if decide (q.call.kind = .pair) then 1 else 0) (2 * Algorithm.traceOrder * Builder.occurrences q.call 0)
        (2 * Algorithm.traceOrder * Builder.occurrences q.call 1) q.cellCall.ncol (tablesPerGroup q)
        (systemList q).length q.selected.1.factors (certNats q) ++
      (systemList q).flatMap (gatheredItem q) := by
  unfold gatheredWord contextWord headWord certNats
  simp only [listWord, bitWord, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_map,
    List.flatMap_map, List.append_assoc]
  rfl

/-- **The framed systems word** as written by `emitS`. -/
theorem frame_systemsWord (q : ChildRequest B1 B2) :
    RepairOrdinary.frame (systemsWord q) = marksD 2 (natWord q.call.n) ++ bitD 1 false ++
      marksD 1 (natWord (systemList q).length) ++ marksD 1 ((systemList q).flatMap (systemOut q)) ++
      bitD 0 false := by
  rw [frame_eq_marksD]
  unfold systemsWord listWord
  rw [marksD_append, marksD_frame, marksD_append]
  simp only [bitD, pow_zero, Nat.sub_self, List.replicate_zero, List.nil_append, List.append_assoc]
  rfl

theorem certNats_length (q : ChildRequest B1 B2) : (certNats q).length = q.cellCall.ncol := by
  unfold certNats certifiedBits; simp

theorem certNats_le (q : ChildRequest B1 B2) : ∀ v ∈ certNats q, v ≤ 1 := by
  intro v hv
  unfold certNats at hv
  obtain ⟨b, -, rfl⟩ := List.mem_map.mp hv
  split <;> omega

theorem ncol_eq (q : ChildRequest B1 B2) : q.cellCall.ncol = 2 ^ (q.call.n - q.selected.1.k) := rfl

/-- The number of listed systems is below `2^(2E)`. -/
theorem systemList_length_lt (q : ChildRequest B1 B2) : (systemList q).length < 2 ^ (2 * emitExp q) := by
  obtain ⟨-, -, -, -, hn, hJ, -⟩ := child_le q
  have hP := P_le_envelope q
  have h1 := systemList_length_le q
  set V := envelope q
  have hc : q.cellCall.ncol ≤ 2 ^ V := by
    rw [ncol_eq]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hPw : q.selected.1.P ^ (2 * (q.cellCall.J + 1)) ≤ 2 ^ (V * (2 * V + 2)) := by
    calc q.selected.1.P ^ (2 * (q.cellCall.J + 1)) ≤ (V + 1) ^ (2 * V + 2) :=
          (Nat.pow_le_pow_left (by omega) _).trans (Nat.pow_le_pow_right (by omega) (by omega))
      _ ≤ 2 ^ (V * (2 * V + 2)) := succ_pow_le_two_pow _ _
  have h4 : 4 ^ Algorithm.traceOrder = 2 ^ 8 := by rfl
  have hS : systemCount q ≤ 2 ^ (1 + V + 8 + V * (2 * V + 2)) := by
    unfold systemCount
    rw [h4, pow_add, pow_add, pow_add, pow_one]
    calc 2 * q.cellCall.ncol * 2 ^ 8 * q.selected.1.P ^ (2 * (q.cellCall.J + 1))
        ≤ 2 * 2 ^ V * 2 ^ 8 * 2 ^ (V * (2 * V + 2)) :=
          Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul le_rfl hc) le_rfl) hPw
      _ = _ := by ring
  have hlt : 1 + V + 8 + V * (2 * V + 2) < 2 * emitExp q := by unfold emitExp; nlinarith
  exact lt_of_le_of_lt (h1.trans hS) (Nat.pow_lt_pow_right (by norm_num) hlt)

/-- The numbers read by `headS` for a child are below `2^(2E)`. -/
theorem head_values_lt (q : ChildRequest B1 B2) :
    ∀ v ∈ [q.call.n, q.selected.1.M1, q.selected.1.A, q.selected.1.Lambda, q.cellCall.J,
        (if decide (q.call.kind = .pair) then 1 else 0), 2 * Algorithm.traceOrder * Builder.occurrences q.call 0,
        2 * Algorithm.traceOrder * Builder.occurrences q.call 1, q.cellCall.ncol, tablesPerGroup q,
        (systemList q).length, q.selected.1.factors.length, (certNats q).length] ++ q.selected.1.factors ++
        certNats q, v < 2 ^ (2 * emitExp q) := by
  obtain ⟨hM, hA, hL, -, hn, hJ, hB⟩ := child_le q
  obtain ⟨y1, y2, -, y4⟩ := env_Y q
  have hP := P_le_envelope q
  have htg := tablesPerGroup_le q
  have hm := systemList_length_lt q
  set V := envelope q
  set E := emitExp q
  have hEE : 2 ^ E ≤ 2 ^ (2 * E) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hVE : V + 8 * V + 1 < 2 ^ E := by
    have : V + 1 ≤ (V + 1) ^ (V + 2) := by
      calc V + 1 = (V + 1) ^ 1 := (pow_one _).symm
        _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have hVE2 : V < 2 * E := by
    have : V ≤ V * (V + 2) := Nat.le_mul_of_pos_right _ (by omega)
    show V < 2 * (V * (V + 2) + 8)
    omega
  have hcol : q.cellCall.ncol < 2 ^ (2 * E) := by
    rw [ncol_eq]; exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  have htg' : tablesPerGroup q < 2 ^ (2 * E) := by
    have h3 : q.selected.1.P ^ 3 ≤ (V + 1) ^ (V + 2) :=
      (Nat.pow_le_pow_left (by omega) 3).trans (Nat.pow_le_pow_right (by omega) (by omega))
    omega
  have hfl := factors_length q
  have hcl := certNats_length q
  have small : ∀ v, v ≤ 8 * V → v < 2 ^ (2 * E) := fun v hv => by omega
  intro v hv
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with ((h | h | h | h | h | h | h | h | h | h | h | h | h) | h) | h
  · exact small v (by omega)
  · exact small v (by omega)
  · exact small v (by omega)
  · exact small v (by omega)
  · exact small v (by omega)
  · exact small v (by rw [h]; split <;> omega)
  · exact small v (by rw [h]; exact hB 0)
  · exact small v (by rw [h]; exact hB 1)
  · rw [h]; exact hcol
  · rw [h]; exact htg'
  · rw [h]; exact hm
  · exact small v (by omega)
  · rw [h, hcl]; exact hcol
  · have hv' : v ≤ q.call.n := Cells.ParameterRules.factor_member_preparation_bound (rules q) v h
    exact small v (by omega)
  · exact small v ((certNats_le q v h).trans (by omega))

end NearQuarticWires.Reconstruct
