import Proof.Quartic.Reconstruct.EmitBudget

/-!
# The emission stage within the cost of `prop:time`

Paper: `prop:time`, paper/paper.tex.

The run costs at most `2·10^9 U^6 (m + n_col + 1)` (`emitRunCost_le`), the gathered word has at most
`100200 U^5 (|γ| + m + 1)` bits (`gatheredWord_length_le`), and `m + n_col + |γ| + 1 ≤ systemsCost q`
(`emit_terms_le`). Hence the budget of `emitWF` is at most `emitK B₁ (n+1)^{emitE B₁} systemsCost q`
(`emitBudget_le`), and `emitStage` is the emission stage with that budget.
-/

set_option autoImplicit false

namespace NearQuarticWires.Reconstruct

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.Cells
open NearCubicGates.Close.Interfaces (listWord bitWord)
open NearQuarticWires.Greedy NearQuarticWires.Program
open NearCubicWires.RepairOrdinary (WordFunction frame)

variable {B1 B2 : ℕ}

theorem headCost_le (ℓ U J Z : ℕ) (hU : 1 ≤ U) (hℓ : ℓ ≤ U) (hJ : J ≤ U) :
    headCost ℓ J Z ≤ 1412 * (U ^ 2 * (Z + 1)) := by
  have e36 : emitNatDCost 2 ℓ = 36 * ℓ + 108 := by unfold emitNatDCost; norm_num; ring
  have hUZ : Z ≤ U * Z := Nat.le_mul_of_pos_left Z hU
  have h1 : J + Z + 13 ≤ 14 * (U * Z) + 14 * U := by omega
  have h2 := Nat.mul_le_mul h1 (show 30 * ℓ + 36 ≤ 66 * U by omega)
  have h4 : (14 * (U * Z) + 14 * U) * (66 * U) = 924 * (U ^ 2 * (Z + 1)) := by ring
  have h5 : U ^ 2 ≤ U ^ 2 * (Z + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have h8 : U ≤ U ^ 2 := by rw [pow_two]; exact Nat.le_mul_of_pos_left U hU
  have h7 : 1 ≤ U ^ 2 := Nat.one_le_pow _ _ (by omega)
  unfold headCost
  rw [e36]
  linarith

theorem runCost_arith (m Z I H U : ℕ) (hU : 1 ≤ U) (hI : I ≤ 1000000000 * U ^ 6)
    (hH : H ≤ 1412 * (U ^ 2 * (Z + 1))) :
    5 + H + (m * (I + 4) + 4) + 3 + 3 ≤ 2000000000 * U ^ 6 * (m + Z + 1) := by
  have p2 : U ^ 2 ≤ U ^ 6 := Nat.pow_le_pow_right hU (by norm_num)
  have hH' : 1412 * (U ^ 2 * (Z + 1)) ≤ 1412 * (U ^ 6 * (Z + 1)) :=
    Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ p2)
  have h6 : 1 ≤ U ^ 6 := Nat.one_le_pow _ _ (by omega)
  have hM := Nat.mul_le_mul_left m (show I + 4 ≤ 1000000004 * U ^ 6 by omega)
  have e : m * (1000000004 * U ^ 6) = 1000000004 * (U ^ 6 * m) := by ring
  have hf : 2000000000 * U ^ 6 * (m + Z + 1) = 2000000000 * (U ^ 6 * m) + 2000000000 * (U ^ 6 * (Z + 1)) := by ring
  have hD : 1 ≤ U ^ 6 * (Z + 1) := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by positivity) (by omega))
  omega

/-- **The run of the emission stage** costs at most `2·10^9 U^6 (m + n_col + 1)` steps. -/
theorem emitRunCost_le (q : ChildRequest B1 B2) (W U : ℕ) (hU : 1 ≤ U) (hW : W ≤ U) (hV : envelope q + 1 ≤ U) :
    emitRunCost q W ≤ 2000000000 * U ^ 6 * ((systemList q).length + q.cellCall.ncol + 1) := by
  have hJ : q.cellCall.J ≤ U := by have := (child_le q).2.2.2.2.2.1; omega
  have hI : itemCostQ q W ≤ 1000000000 * U ^ 6 := by
    unfold itemCostQ
    exact itemCost_le q.cellCall.J W (envelope q) U hU hJ hW (by omega)
  unfold emitRunCost
  exact runCost_arith _ _ _ _ U hU hI (headCost_le (W - 2) U q.cellCall.J q.cellCall.ncol hU (by omega) hJ)

/-- **The gathered items of a child** have at most `100100 (V+1)^5` bits. -/
theorem gatheredItem_length_le (q : ChildRequest B1 B2) (x : SystemIndex q) (hx : x ∈ systemList q) :
    (gatheredItem q x).length ≤ 100100 * (envelope q + 1) ^ 5 := by
  obtain ⟨-, -, -, hE, -, hJ, -⟩ := child_le q
  have hb : (bitWord x.1).length ≤ 5 := natWord_length_le_of_le (B := 1) (by split <;> norm_num)
  have hd : (listWord NearCubicGates.Close.Interfaces.intWord
      (List.ofFn fun i : Fin 2 => List.ofFn fun j : Fin (q.cellCall.J + 1) => x.2.2.1 i j).flatten).length ≤
      2 * (2 * (envelope q + 1)) + 3 + 2 * (envelope q + 1) * (2 * envelope q + 8) := by
    rw [digits_flatten]
    have hl := digits_length q x.2.2.1
    have h := listWord_length_le NearCubicGates.Close.Interfaces.intWord
      (List.ofFn (x.2.2.1 0) ++ List.ofFn (x.2.2.1 1)) (2 * envelope q + 8)
      (fun z hz => intWord_length_le z (B := envelope q) ((digits_natAbs_le q x hx z hz).trans
        (hE.trans (Nat.lt_two_pow_self).le)))
    rw [hl] at h
    have := Nat.mul_le_mul_right (2 * envelope q + 8) (show 2 * (q.cellCall.J + 1) ≤ 2 * (envelope q + 1) by omega)
    omega
  have hr : (listWord rowWord (systemAt q x).rows).length ≤ 100000 * envelope q ^ 5 := by
    have hs := sysWord_length_le_envelope q q.seedPrefix x.1 x.2.2.2 x.2.1 x.2.2.1
    change (NearCubicGates.Close.Interfaces.Formats.sysWord (systemAt q x)).length ≤ _ at hs
    rw [sysWord_systemAt] at hs
    simp only [List.length_append] at hs
    omega
  have h5 : envelope q ^ 5 ≤ (envelope q + 1) ^ 5 := Nat.pow_le_pow_left (by omega) 5
  have h2 : (envelope q + 1) ^ 2 ≤ (envelope q + 1) ^ 5 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have h1 : 1 ≤ (envelope q + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hq : 2 * (envelope q + 1) * (2 * envelope q + 8) ≤ 16 * (envelope q + 1) ^ 2 := by nlinarith
  unfold gatheredItem
  simp only [List.length_append]
  nlinarith

/-- **The gathered word** has at most `100200 U^5 (|γ| + m + 1)` bits. -/
theorem gatheredWord_length_le (q : ChildRequest B1 B2) (U : ℕ) (hV : envelope q + 1 ≤ U) :
    (gatheredWord q).length ≤ 100200 * U ^ 5 * ((gammaWord q).length + (systemList q).length + 1) := by
  have hc := contextWord_length_le q
  have hl := listWord_length_le (gatheredItem q) (systemList q) (100100 * (envelope q + 1) ^ 5)
    (fun x hx => gatheredItem_length_le q x hx)
  have h5 : (envelope q + 1) ^ 5 ≤ U ^ 5 := Nat.pow_le_pow_left hV 5
  have hU : 1 ≤ U := by omega
  have hU5 : U ≤ U ^ 5 := Nat.le_self_pow (by norm_num) _
  have hm := Nat.mul_le_mul_left (systemList q).length (Nat.mul_le_mul_left 100100 h5)
  unfold gatheredWord
  rw [List.length_append]
  have e : 100200 * U ^ 5 * ((gammaWord q).length + (systemList q).length + 1) =
      100200 * U ^ 5 * (gammaWord q).length + 100200 * U ^ 5 * (systemList q).length + 100200 * U ^ 5 := by ring
  have e2 : (systemList q).length * (100100 * U ^ 5) = 100100 * U ^ 5 * (systemList q).length := by ring
  have g1 : 9 * (gammaWord q).length ≤ 100200 * U ^ 5 * (gammaWord q).length :=
    Nat.mul_le_mul_right _ (by nlinarith)
  have g2 : 2 * (systemList q).length + 100100 * U ^ 5 * (systemList q).length ≤
      100200 * U ^ 5 * (systemList q).length := by nlinarith
  omega

/-- The terms of the emission cost are covered by `systemsCost`. -/
theorem emit_terms_le (q : ChildRequest B1 B2) :
    (systemList q).length + q.cellCall.ncol + (gammaWord q).length + 1 ≤ systemsCost q := by
  have hm := systemList_length_le q
  have hP := one_le_P q
  have ht : 1 ≤ tableCount q := by
    unfold tableCount
    have : 1 ≤ q.selected.1.P ^ (2 * (q.cellCall.J + 1) + 3) := Nat.one_le_pow _ _ (by omega)
    have : 1 ≤ 4 ^ Algorithm.traceOrder := Nat.one_le_pow _ _ (by norm_num)
    nlinarith
  have h1 := Nat.le_mul_of_pos_left (q.cellCall.ncol + (q.call.n + 1) ^ sizeExp B1 B2) ht
  have h2 : systemCount q ≤ systemCount q * (rowCount q + 1) := Nat.le_mul_of_pos_right _ (by omega)
  unfold systemsCost
  omega

end NearQuarticWires.Reconstruct
