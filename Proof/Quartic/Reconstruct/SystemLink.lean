import Proof.Quartic.Reconstruct.TagProgram
import Proof.Quartic.Reconstruct.PointsLink
import Proof.Quartic.Reconstruct.CopyProgram
import Proof.Quartic.Reconstruct.Answers

/-!
# The words of a listed system from the data the stage computes

Paper: Step 3 of `sec:algorithm`, paper/paper.tex.

For a listed system `x = (s, σ, δ, z)` the stage `emit` computes, for each coordinate `j`, the shifted start, the
number of points and the shift of the coordinate interval (`axisData`; `BoxArith.boxAxisOf_eq`). This file writes the
tag and the word of the system in these terms:

* `systemTag_eq`: `systemTag = intWord (±2) ++ natWord idx₀` (`κ_σ = 2` on listed systems, `kappa_eq_two`);
* `sysWord_systemAt`: `sysWord = natWord (len_1 len_2) ++ pointsWord … ++ listWord rowWord rows`.
-/

set_option autoImplicit false

namespace NearQuarticWires.Reconstruct

open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Interfaces (listWord)
open NearQuarticWires.Greedy NearQuarticWires.Program

variable {B1 B2 : ℕ}

/-- The data `(lo', len, B)` of coordinate `j` of the box of `δ` (`BoxArith.boxAxisOf_eq`); `(0, 1, 0)` for a
coordinate outside `𝒥`, whose list is `[0]`. -/
noncomputable def axisData (q : ChildRequest B1 B2) (δ : Fin 2 → Fin (q.cellCall.J + 1) → ℤ) (j : Fin 2) :
    ℕ × ℕ × ℕ := by
  classical
  exact if j ∈ Builder.circuitSet q.call then
    ((q.selected.1.M1 * hornerN (fun i => q.selected.1.factors.getD i 0) (digitPart q δ j true) q.cellCall.J +
        q.selected.1.A + q.selected.1.A * (2 * Algorithm.traceOrder * Builder.occurrences q.call j) -
        (q.selected.1.M1 * hornerN (fun i => q.selected.1.factors.getD i 0) (digitPart q δ j false) q.cellCall.J +
          q.selected.1.Lambda)) / q.selected.1.A,
      min ((q.selected.1.M1 * hornerN (fun i => q.selected.1.factors.getD i 0) (digitPart q δ j true) q.cellCall.J +
          (q.selected.1.Lambda - 1) + q.selected.1.A * (2 * Algorithm.traceOrder * Builder.occurrences q.call j) +
          q.selected.1.A - q.selected.1.M1 *
            hornerN (fun i => q.selected.1.factors.getD i 0) (digitPart q δ j false) q.cellCall.J) /
            q.selected.1.A) (2 * (2 * Algorithm.traceOrder * Builder.occurrences q.call j) + 1) -
        (q.selected.1.M1 * hornerN (fun i => q.selected.1.factors.getD i 0) (digitPart q δ j true) q.cellCall.J +
          q.selected.1.A + q.selected.1.A * (2 * Algorithm.traceOrder * Builder.occurrences q.call j) -
          (q.selected.1.M1 * hornerN (fun i => q.selected.1.factors.getD i 0) (digitPart q δ j false) q.cellCall.J +
            q.selected.1.Lambda)) / q.selected.1.A,
      2 * Algorithm.traceOrder * Builder.occurrences q.call j)
  else (0, 1, 0)

/-- **The coordinate lists of a box from the axis data.** -/
theorem boxAxisOf_axisData (q : ChildRequest B1 B2) (δ : Fin 2 → Fin (q.cellCall.J + 1) → ℤ) (j : Fin 2) :
    boxAxisOf q δ j = (List.range (axisData q δ j).2.1).map
      fun i : ℕ => (((axisData q δ j).1 : ℕ) : ℤ) - ((axisData q δ j).2.2 : ℕ) + (i : ℤ) := by
  classical
  by_cases hj : j ∈ Builder.circuitSet q.call
  · rw [boxAxisOf_eq q δ j hj]
    unfold axisData
    rw [if_pos hj]
  · unfold boxAxisOf axisData
    rw [if_neg hj, if_neg hj]
    simp

/-- The points of a listed system are the points of the box of its digit vector. -/
theorem systemAt_pts (q : ChildRequest B1 B2) (x : SystemIndex q) :
    (systemAt q x).pts = ((boxAxisOf q x.2.2.1 0) ×ˢ (boxAxisOf q x.2.2.1 1)).map pairList := rfl

/-- **The word of a listed system.** -/
theorem sysWord_systemAt (q : ChildRequest B1 B2) (x : SystemIndex q) :
    NearCubicGates.Close.Interfaces.Formats.sysWord (systemAt q x) =
      natWord ((axisData q x.2.2.1 0).2.1 * (axisData q x.2.2.1 1).2.1) ++
        pointsWord (axisData q x.2.2.1 0).1 (axisData q x.2.2.1 0).2.1 (axisData q x.2.2.1 0).2.2
          (axisData q x.2.2.1 1).1 (axisData q x.2.2.1 1).2.1 (axisData q x.2.2.1 1).2.2 ++
        listWord rowWord (systemAt q x).rows := by
  unfold NearCubicGates.Close.Interfaces.Formats.sysWord
  rw [systemAt_pts, boxPointsWord_eq _ _ _ _ _ _ _ _ (boxAxisOf_axisData q x.2.2.1 0)
    (boxAxisOf_axisData q x.2.2.1 1)]
  rfl

/-- `κ_σ ∈ {0, 2}`. -/
theorem kappa_eq_two (σ : Cycle.SignPattern Algorithm.traceOrder) (h : Cycle.kappa Algorithm.traceOrder σ ≠ 0) :
    Cycle.kappa Algorithm.traceOrder σ = 2 := by
  have hp : |∏ l, Cycle.signValue (σ l)| = 1 := by
    rw [Finset.abs_prod]
    simp [Cycle.abs_signValue]
  unfold Cycle.kappa at h ⊢
  rcases abs_eq (zero_le_one) |>.mp hp with h1 | h1
  · rw [h1]; norm_num
  · rw [h1] at h; norm_num at h

/-- **The tag of a listed system.** -/
theorem systemTag_eq (q : ChildRequest B1 B2) (x : SystemIndex q) (hx : x ∈ systemList q) :
    systemTag q x = NearCubicGates.Close.Interfaces.intWord (coefOf x.1) ++
      natWord (zeroIndex (axisData q x.2.2.1 0).1 (axisData q x.2.2.1 0).2.1 (axisData q x.2.2.1 0).2.2
        (axisData q x.2.2.1 1).1 (axisData q x.2.2.1 1).2.1 (axisData q x.2.2.1 1).2.2) := by
  have hk := kappa_eq_two x.2.1 (mem_systemList hx).1
  unfold systemTag
  congr 2
  · unfold systemCoef coefOf partSign
    rw [hk]
    split <;> norm_num
  · rw [systemAt_pts, boxAxisOf_axisData q x.2.2.1 0, boxAxisOf_axisData q x.2.2.1 1, idxOf_zero_box]
    rfl

/-! ## Frames at depth `d` -/

theorem frame_eq_marks (w : List Bool) : RepairOrdinary.frame w = NearCubicWires.RepairOrdinary.Streaming.marks w ++ [false] := by
  induction w with
  | nil => rfl
  | cons b w ih => simp [RepairOrdinary.frame, ih, NearCubicWires.RepairOrdinary.Streaming.marks]

theorem marksD_marks (d : ℕ) (w : List Bool) :
    marksD d (NearCubicWires.RepairOrdinary.Streaming.marks w) = marksD (d + 1) w := by
  induction d with
  | zero => rw [marksD_zero, marksD_succ, marksD_zero]
  | succ d ih => rw [marksD_succ, ih, ← marksD_succ]

/-- **A frame at depth `d`**: the framed word at depth `d` is the word at depth `d + 1` followed by the end mark
`false` at depth `d`. -/
theorem marksD_frame (d : ℕ) (w : List Bool) :
    marksD d (RepairOrdinary.frame w) = marksD (d + 1) w ++ bitD d false := by
  rw [frame_eq_marks, marksD_append, marksD_marks]
  simp [marksD]

/-- **The output of a stage**: `frame w` is `w` at depth `1` followed by the end mark. -/
theorem frame_eq_marksD (w : List Bool) : RepairOrdinary.frame w = marksD 1 w ++ [false] := by
  rw [← marksD_zero (RepairOrdinary.frame w), marksD_frame]
  rfl

end NearQuarticWires.Reconstruct

namespace NearQuarticWires.Reconstruct

open NearQuarticWires.Greedy

variable {B1 B2 : ℕ}

/-- The flattened digit vector is the digits of the first circuit followed by those of the second. -/
theorem digits_flatten {J : ℕ} (δ : Fin 2 → Fin (J + 1) → ℤ) :
    (List.ofFn fun i : Fin 2 => List.ofFn fun j : Fin (J + 1) => δ i j).flatten =
      List.ofFn (δ 0) ++ List.ofFn (δ 1) := by
  simp [List.ofFn_succ]

theorem digits_getD_zero {J : ℕ} (δ : Fin 2 → Fin (J + 1) → ℤ) (i : ℕ) (hi : i ≤ J) :
    (List.ofFn (δ 0) ++ List.ofFn (δ 1)).getD i 0 = δ 0 ⟨i, by omega⟩ := by
  rw [List.getD_append _ _ _ _ (by simp; omega), List.getD_eq_getElem _ _ (by simp; omega), List.getElem_ofFn]

theorem digits_getD_one {J : ℕ} (δ : Fin 2 → Fin (J + 1) → ℤ) (i : ℕ) (hi : i ≤ J) :
    (List.ofFn (δ 0) ++ List.ofFn (δ 1)).getD (J + 1 + i) 0 = δ 1 ⟨i, by omega⟩ := by
  rw [List.getD_append_right _ _ _ _ (by simp), List.length_ofFn, Nat.add_sub_cancel_left,
    List.getD_eq_getElem _ _ (by simp; omega), List.getElem_ofFn]

/-- The parts of a digit of circuit `j`, extended by zeros, are the parts of the digit itself on `i ≤ J`. -/
theorem digitPart_eq (q : ChildRequest B1 B2) (δ : Fin 2 → Fin (q.cellCall.J + 1) → ℤ) (j : Fin 2) (s : Bool)
    (i : ℕ) (hi : i ≤ q.cellCall.J) :
    digitPart q δ j s i = if s then (δ j ⟨i, by omega⟩).toNat else (-(δ j ⟨i, by omega⟩)).toNat := by
  unfold digitPart NearCubicGates.CertifiedScoreSupport.extendDigits
  rw [dif_pos (by omega)]

end NearQuarticWires.Reconstruct
