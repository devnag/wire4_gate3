import Proof.Quartic.StageColumns.WordFunction
import Proof.Quartic.StageColumns.Clock
import Proof.Gates.CellsPack.Lang

set_option autoImplicit false

namespace NearQuarticWires.StageColumns

open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicGates.Close.Cells
open NearCubicGates.Close.CellsPack (Gof)

/-- `prop:time`, paper/paper.tex: the complete
cold source clock, including output framing, is a fixed polynomial. -/
theorem sourceClock_le (P : StarParams) : sourceClock P ≤ 10000 * (P.n + 2) ^ 4 := by
  let V := P.n + 2
  have h := columnsClock_le P
  have hv : V ≤ V ^ 4 := Nat.le_self_pow (by decide : (4 : ℕ) ≠ 0) V
  have hv1 : 1 ≤ V ^ 4 := Nat.one_le_pow _ _ (by dsimp [V]; omega)
  change columnsClock P ≤ 140 * V ^ 4 at h
  change 3 * (1000 * V + columnsClock P + 6) + 2 ≤ 10000 * V ^ 4
  omega

/-- `prop:time`, paper/paper.tex: the actual
four-field binary source has linear length in original arity. -/
theorem columnInput_length_le (P : StarParams) : (columnInput P).length ≤ 12 * (P.n + 2) := by
  have hn := field_bitLength P P.n (by simp [fields])
  have hr := field_bitLength P P.r (by simp [fields])
  have hb := field_bitLength P P.b (by simp [fields])
  have hs := field_bitLength P P.s (by simp [fields])
  simp only [columnInput, List.length_append, natWord_length]
  omega

/-- `prop:time`, paper/paper.tex: n-first source
encoding gives linear compiled binary workspace without a supplied ruler. -/
theorem column_setup_width_le (P : StarParams) :
    columnSizes.W (leadOnes (columnInput P)) ≤ 128 * (P.n + 1) := by
  simp only [columnSizes, Sz.W, one_mul, input_leadOnes, natBitLength, pow_succ]
  have h := Nat.pow_log_le_add_one 2 P.n
  omega

/-- `prop:time`, paper/paper.tex: the actual cold
ordinary common-generator printer has one fixed polynomial physical
clock, including all setup, bit output, framing and final head reset. -/
theorem columnBudget_fixed (P : StarParams) :
    columnBudget P ≤ 10 ^ 12 * (TSK columnCallee + 300) ^ 2 * (P.n + 2) ^ 6 := by
  let V := P.n + 2
  let A := TSK columnCallee + 300
  have hV : 1 ≤ V := by dsimp [V]; omega
  have hA : 1 ≤ A := by dsimp [A]; omega
  have hL : leadOnes (columnInput P) ≤ V := by
    rw [input_leadOnes]
    unfold natBitLength
    have := Nat.log_le_self 2 P.n
    dsimp [V]
    omega
  have hG : Gof columnCallee columnSizes (leadOnes (columnInput P)) ≤ A * V := by
    have hw := column_setup_width_le P
    simp only [Gof, Sz.Lk, Sz.Bk, columnSizes, Nat.zero_mul, pow_zero,
      mul_zero, add_zero]
    change columnSizes.W (leadOnes (columnInput P)) + leadOnes (columnInput P) +
      64 + 0 + 0 + 1 + 0 + 0 + TSK columnCallee + 1 ≤ A * V
    dsimp [A, V] at *
    nlinarith
  have hN : sourceClock P + 1 ≤ 10001 * V ^ 4 := by
    have h := sourceClock_le P
    change sourceClock P ≤ 10000 * V ^ 4 at h
    have hv4 : 1 ≤ V ^ 4 := Nat.one_le_pow _ _ hV
    omega
  have hsmall : 120 * V ≤ 120 * A ^ 2 * V ^ 6 := by
    have hv : V ≤ V ^ 6 := Nat.le_self_pow (by decide : (6 : ℕ) ≠ 0) V
    have ha : 1 ≤ A ^ 2 := Nat.one_le_pow _ _ hA
    have hv' : V ≤ A ^ 2 * V ^ 6 := hv.trans (Nat.le_mul_of_pos_left _ ha)
    simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left 120 hv'
  have h := NearCubicGates.Close.CellsPack.lang_le2 columnCallee columnSizes
    (columnInput P) (sourceClock P)
  calc
    columnBudget P ≤ 10 ^ 6 * ((sourceClock P + 1) *
        Gof columnCallee columnSizes (leadOnes (columnInput P)) ^ 2) + 10 * (columnInput P).length := h
    _ ≤ 10 ^ 6 * ((10001 * V ^ 4) * (A * V) ^ 2) + 120 * V := by
      apply Nat.add_le_add
      · exact Nat.mul_le_mul_left _ (Nat.mul_le_mul hN (Nat.pow_le_pow_left hG 2))
      · have hi := Nat.mul_le_mul_left 10 (columnInput_length_le P)
        calc
          10 * (columnInput P).length ≤ 10 * (12 * (P.n + 2)) := hi
          _ = 120 * V := by dsimp [V]; ring
    _ ≤ 10 ^ 12 * A ^ 2 * V ^ 6 := by
      have he : 10 ^ 6 * ((10001 * V ^ 4) * (A * V) ^ 2) =
          10001000000 * A ^ 2 * V ^ 6 := by ring
      rw [he]
      nlinarith only [hsmall]
    _ = _ := rfl

/-- `prop:time`, paper/paper.tex: one pair of
natural constants bounds every original canonical-columns request. -/
theorem columnBudget_polynomial :
    ∃ C e : ℕ, ∀ P : StarParams, columnBudget P ≤ C * (P.n + 2) ^ e :=
  ⟨10 ^ 12 * (TSK columnCallee + 300) ^ 2, 6, columnBudget_fixed⟩

end NearQuarticWires.StageColumns
