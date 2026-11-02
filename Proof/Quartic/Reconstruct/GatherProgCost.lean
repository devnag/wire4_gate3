import Proof.Quartic.Reconstruct.GatherProgWF

/-!
# The gathering stage within `K (n+1)^e` times its cost

Paper: `prop:time`, paper/paper.tex.

With `U` the scale of a child (`scaleU`), the run of the gathering and its input cost at most `10^6 U^3` times the
cost `systemsCost` of the stage (`runCostQ_le`): the tables cost `poly(U)` per entry, the items `poly(U)` per row of a
listed system. Hence the budget of `gatherWF` is at most `gatherK B₁ (n+1)^{gatherE B₁} systemsCost q`
(`gatherBudget_le`), and **`gatherStage`** is the `gather` argument of `SystemsSplit.systemsOfSplit`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearQuarticWires.Reconstruct.GatherProg

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.Cells
open NearCubicGates.Close.Interfaces (listWord bitWord)
open NearQuarticWires.Greedy NearQuarticWires.Program
open NearQuarticWires.Reconstruct
open NearCubicWires.RepairOrdinary (WordFunction frame)

variable {B1 B2 : ℕ}

/-- The tables part of the cost of a group, per table, against the columns. -/
theorem tbl_part (ncol X D u : ℕ) (hX : 1 ≤ X) (hDu : D ≤ u) :
    2 * D + ncol + (8 + 2 * D + 2 * ncol + 12) * (u + 10) + 4 + 3 + 25 * ncol + 62 ≤
      (ncol + X) * ((2 * D + 100) * (u + 10)) := by
  have h1 : ncol * (2 * (u + 10) + 27) ≤ ncol * ((2 * D + 100) * (u + 10)) :=
    Nat.mul_le_mul_left _ (by nlinarith)
  have h2 : (2 * D + 100) * (u + 10) ≤ X * ((2 * D + 100) * (u + 10)) := Nat.le_mul_of_pos_left _ hX
  nlinarith

/-- The items part of the cost of a group, per item, against the rows. -/
theorem item_part (RC tg D u : ℕ) (h5 : tg ≤ RC) :
    2 * D + 3 * tg + D * (2 * u + 9) + tg * (5 * u + 22) + 3 * u + 30 + 2 ≤ (RC + 1) * ((D + 1) * (5 * u + 40)) := by
  have h1 : (tg + 1) * ((D + 1) * (5 * u + 40)) ≤ (RC + 1) * ((D + 1) * (5 * u + 40)) :=
    Nat.mul_le_mul_right _ (by omega)
  have h0 : 2 * D + 3 * tg + D * (2 * u + 9) + tg * (5 * u + 22) + 3 * u + 30 + 2 ≤
      (tg + 1) * ((D + 1) * (5 * u + 40)) := by
    have := Nat.zero_le (tg * D * u)
    have := Nat.zero_le (tg * D)
    nlinarith
  exact h0.trans h1

theorem cost_arith (TC SC RC X γ ncol nc tg gl J D u cc B L : ℕ) (hDu : D ≤ u)
    (h2 : gl * tg ≤ TC) (h3 : gl * nc ≤ 2 * SC) (h4 : gl ≤ TC) (h5 : tg ≤ RC) (h6 : nc ≤ ncol) (h8 : 1 ≤ TC)
    (h9 : 1 ≤ X) (hL : L ≤ B * (TC * (ncol + X) + γ + 1)) :
    (J + ncol + 20) * (cc + 9) + 2 * u + gl * ((tg * ((2 * D + ncol + (8 + 2 * D + 2 * ncol + 12) * (u + 10)) + 4) +
      nc * ((2 * D + 3 * tg + D * (2 * u + 9) + tg * (5 * u + 22) + 3 * u + 30) + 2) + 3 * tg + 25 * (tg * nc) + 60) +
        2) + 30 + L + 1 ≤
      ((2 * D + 100) * (u + 10) + (J + 20) * (cc + 9) + 2 * u + 31 + 2 * ((D + 1) * (5 * u + 40)) + B + 1) *
        (TC * (ncol + X) + SC * (RC + 1) + γ + 1) := by
  set T1 := 2 * D + ncol + (8 + 2 * D + 2 * ncol + 12) * (u + 10) + 4 with hT1
  set I1 := 2 * D + 3 * tg + D * (2 * u + 9) + tg * (5 * u + 22) + 3 * u + 30 + 2 with hI1
  set Z1 := (2 * D + 100) * (u + 10) with hZ1
  set Z2 := (D + 1) * (5 * u + 40) with hZ2
  set S1 := TC * (ncol + X) with hS1
  set S2 := SC * (RC + 1) with hS2
  have ht := tbl_part ncol X D u h9 hDu
  have hi := item_part RC tg D u h5
  -- the groups
  have eg : gl * ((tg * T1 + nc * I1 + 3 * tg + 25 * (tg * nc) + 60) + 2) =
      (gl * tg) * T1 + (gl * nc) * I1 + 3 * (gl * tg) + 25 * ((gl * tg) * nc) + 62 * gl := by ring
  have g1 : (gl * tg) * T1 ≤ TC * T1 := Nat.mul_le_mul_right _ h2
  have g2 : (gl * nc) * I1 ≤ (2 * SC) * I1 := Nat.mul_le_mul_right _ h3
  have g3 : (gl * tg) * nc ≤ TC * ncol := Nat.mul_le_mul h2 h6
  have g4 : TC * (T1 + 3 + 25 * ncol + 62) ≤ TC * ((ncol + X) * Z1) := Nat.mul_le_mul_left _ ht
  have g5 : (2 * SC) * I1 ≤ (2 * SC) * ((RC + 1) * Z2) := Nat.mul_le_mul_left _ hi
  have hG : gl * ((tg * T1 + nc * I1 + 3 * tg + 25 * (tg * nc) + 60) + 2) ≤ S1 * Z1 + S2 * (2 * Z2) := by
    have e1 : TC * ((ncol + X) * Z1) = S1 * Z1 := by rw [hS1]; ring
    have e2 : (2 * SC) * ((RC + 1) * Z2) = S2 * (2 * Z2) := by rw [hS2]; ring
    have e3 : TC * (T1 + 3 + 25 * ncol + 62) = TC * T1 + 3 * TC + 25 * (TC * ncol) + 62 * TC := by ring
    rw [eg]
    omega
  -- the context
  have hC1 : J + ncol + 20 ≤ (ncol + X) * (J + 20) := by nlinarith
  have hC2 : (J + ncol + 20) * (cc + 9) ≤ S1 * ((J + 20) * (cc + 9)) := by
    calc (J + ncol + 20) * (cc + 9) ≤ (ncol + X) * (J + 20) * (cc + 9) := Nat.mul_le_mul_right _ hC1
      _ = 1 * ((ncol + X) * ((J + 20) * (cc + 9))) := by ring
      _ ≤ TC * ((ncol + X) * ((J + 20) * (cc + 9))) := Nat.mul_le_mul_right _ h8
      _ = S1 * ((J + 20) * (cc + 9)) := by rw [hS1]; ring
  have hS1p : 1 ≤ S1 := by rw [hS1]; nlinarith
  have hC3 : 2 * u + 31 ≤ S1 * (2 * u + 31) := Nat.le_mul_of_pos_left _ hS1p
  have hLL : L + 1 ≤ (B + 1) * (S1 + γ + 1) := by nlinarith
  -- the sum
  have e4 : ((2 * D + 100) * (u + 10) + (J + 20) * (cc + 9) + 2 * u + 31 + 2 * ((D + 1) * (5 * u + 40)) + B + 1) *
      (S1 + S2 + γ + 1) = S1 * Z1 + S1 * ((J + 20) * (cc + 9)) + S1 * (2 * u + 31) + S2 * (2 * Z2) +
        (Z1 + (J + 20) * (cc + 9) + 2 * u + 31) * (S2 + γ + 1) + (2 * Z2) * (S1 + γ + 1) +
        (B + 1) * (S1 + γ + 1) + (B + 1) * S2 := by
    rw [hZ1, hZ2]; ring
  rw [e4]
  have hz : 0 ≤ (Z1 + (J + 20) * (cc + 9) + 2 * u + 31) * (S2 + γ + 1) + (2 * Z2) * (S1 + γ + 1) + (B + 1) * S2 :=
    Nat.zero_le _
  omega

/-! ## The run of a child -/

theorem zq_le (J V U ℓ u cc : ℕ) (hJ : J ≤ V) (hU : V + 1 ≤ U) (hℓ : ℓ = 100 * (V + 1) ^ 2) (hu : u = 30 * ℓ + 100)
    (hcc : cc = 58 * ℓ + 115) :
    (2 * (2 * (J + 1)) + 100) * (u + 10) + (J + 20) * (cc + 9) + 2 * u + 31 +
      2 * ((2 * (J + 1) + 1) * (5 * u + 40)) + (8 * V ^ 2 + 60 * V + 140) + 1 ≤ 1000000 * U ^ 3 := by
  have hU1 : 1 ≤ U := by omega
  have hV2 : (V + 1) ^ 2 ≤ U ^ 2 := Nat.pow_le_pow_left hU 2
  have hU23 : U ^ 2 ≤ U ^ 3 := Nat.pow_le_pow_right hU1 (by norm_num)
  have hU2 : 1 ≤ U ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hu' : u + 10 ≤ 3110 * U ^ 2 := by omega
  have hcc' : cc + 9 ≤ 5924 * U ^ 2 := by omega
  have h1 : (2 * (2 * (J + 1)) + 100) * (u + 10) ≤ (104 * U) * (3110 * U ^ 2) := Nat.mul_le_mul (by omega) hu'
  have h2 : (J + 20) * (cc + 9) ≤ (21 * U) * (5924 * U ^ 2) := Nat.mul_le_mul (by omega) hcc'
  have h3 : (2 * (J + 1) + 1) * (5 * u + 40) ≤ (3 * U) * (15550 * U ^ 2) := Nat.mul_le_mul (by omega) (by omega)
  have hV : 8 * V ^ 2 + 60 * V + 141 ≤ 209 * U ^ 2 := by
    have : V ^ 2 ≤ U ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have : V ≤ U ^ 2 := by nlinarith
    omega
  have e1 : (104 * U) * (3110 * U ^ 2) = 323440 * U ^ 3 := by ring
  have e2 : (21 * U) * (5924 * U ^ 2) = 124404 * U ^ 3 := by ring
  have e3 : (3 * U) * (15550 * U ^ 2) = 46650 * U ^ 3 := by ring
  omega

theorem tableCount_pos (q : ChildRequest B1 B2) : 1 ≤ tableCount q := by
  unfold tableCount
  have : 1 ≤ q.selected.1.P ^ (2 * (q.cellCall.J + 1) + 3) := Nat.one_le_pow _ _ (one_le_P q)
  have : 1 ≤ 4 ^ Algorithm.traceOrder := Nat.one_le_pow _ _ (by norm_num)
  nlinarith

/-- **The run of the gathering and its input cost at most `10^6 U^3 · systemsCost`.** -/
theorem runCostQ_le (q : ChildRequest B1 B2) (U : ℕ) (hU : envelope q + 1 ≤ U) :
    runCostQ q + (tablesWord q).length + 1 ≤ 1000000 * U ^ 3 * systemsCost q := by
  classical
  have hJ : q.cellCall.J ≤ envelope q := (child_le q).2.2.2.2.2.1
  have hgl : (groupList q).length * ncOf (certNats q) = 2 * (systemList q).length := by
    rw [groupList_length, systemList_length, ncOf_certNats]; ring
  have h2 : (groupList q).length * tablesPerGroup q ≤ tableCount q := by
    rw [← printList_length]; exact printList_length_le q
  have h3 : (groupList q).length * ncOf (certNats q) ≤ 2 * systemCount q := by
    rw [hgl]; have := systemList_length_le q; omega
  have h4 : (groupList q).length ≤ tableCount q :=
    (Nat.le_mul_of_pos_right _ (tablesPerGroup_pos q)).trans h2
  have h5 : tablesPerGroup q ≤ rowCount q := tablesPerGroup_le q
  have h6 : ncOf (certNats q) ≤ q.cellCall.ncol := by
    rw [ncOf_certNats, certList_eq]; exact (List.length_filter_le _ _).trans (by simp)
  have h9 : 1 ≤ (q.call.n + 1) ^ sizeExp B1 B2 := Nat.one_le_pow _ _ (by omega)
  have hL := tablesWord_length_le q
  have hDu : 2 * (q.cellCall.J + 1) ≤ unitC (ellQ q) := by
    unfold unitC ellQ; nlinarith
  have hA := cost_arith (tableCount q) (systemCount q) (rowCount q) ((q.call.n + 1) ^ sizeExp B1 B2)
    (gammaWord q).length q.cellCall.ncol (ncOf (certNats q)) (tablesPerGroup q) (groupList q).length q.cellCall.J
    (2 * (q.cellCall.J + 1)) (unitC (ellQ q)) (copyCost 1 (ellQ q)) (8 * envelope q ^ 2 + 60 * envelope q + 140)
    (tablesWord q).length hDu h2 h3 h4 h5 h6 (tableCount_pos q) h9 hL
  have hZ := zq_le q.cellCall.J (envelope q) U (ellQ q) (unitC (ellQ q)) (copyCost 1 (ellQ q)) hJ hU rfl rfl
    (by unfold copyCost; rw [emitNatDCost_one]; ring)
  have hrun : runCostQ q + (tablesWord q).length + 1 = (q.cellCall.J + q.cellCall.ncol + 20) *
      (copyCost 1 (ellQ q) + 9) + 2 * unitC (ellQ q) + (groupList q).length *
      ((tablesPerGroup q * ((2 * (2 * (q.cellCall.J + 1)) + q.cellCall.ncol + (8 + 2 * (2 * (q.cellCall.J + 1)) +
        2 * q.cellCall.ncol + 12) * (unitC (ellQ q) + 10)) + 4) + ncOf (certNats q) * ((2 * (2 * (q.cellCall.J + 1)) +
        3 * tablesPerGroup q + 2 * (q.cellCall.J + 1) * (2 * unitC (ellQ q) + 9) + tablesPerGroup q *
        (5 * unitC (ellQ q) + 22) + 3 * unitC (ellQ q) + 30) + 2) + 3 * tablesPerGroup q +
        25 * (tablesPerGroup q * ncOf (certNats q)) + 60) + 2) + 30 + (tablesWord q).length + 1 := by
    unfold runCostQ gatherCost ctxCost gcQ tblCostU itemCostG
    ring
  rw [hrun]
  refine hA.trans (Nat.mul_le_mul hZ (le_of_eq ?_))
  unfold systemsCost; ring

/-! ## The stage -/

/-- The constant of the gathering stage. -/
noncomputable def gatherK (B1 : ℕ) : ℕ :=
  10000000000 * (201 + emitTapes) ^ 2 * ((emitSizes B1).a1 * 2 ^ (emitSizes B1).c1) ^ 5

/-- The exponent of the gathering stage. -/
def gatherE (B1 : ℕ) : ℕ := 5 * (emitSizes B1).c1

theorem scaleU_pow5 (q : ChildRequest B1 B2) :
    scaleU B1 q ^ 5 = ((emitSizes B1).a1 * 2 ^ (emitSizes B1).c1) ^ 5 * (q.call.n + 1) ^ gatherE B1 := by
  unfold scaleU gatherE
  rw [mul_pow, ← pow_mul, mul_comm (emitSizes B1).c1 5]

/-- **The budget of the gathering stage.** -/
theorem gatherBudget_le (q : ChildRequest B1 B2) :
    gatherBudget B1 q ≤ gatherK B1 * (q.call.n + 1) ^ gatherE B1 * systemsCost q := by
  obtain ⟨ha, hc, hn, h128⟩ := scaleU_facts q
  have hWU : (emitSizes B1).W (leadOnes (tablesWord q)) ≤ scaleU B1 q := by
    rw [leadOnes_tablesWord, ← leadOnes_gatheredWord]; exact width_le_U q
  have hVU := envelope_le_U q
  have hN := runCostQ_le q (scaleU B1 q) hVU
  set U := scaleU B1 q with hU
  set T := emitTapes with hT
  set S := U + 200 + T with hS
  have hL : leadOnes (tablesWord q) ≤ S := by
    rw [leadOnes_tablesWord]; have := natBitLength_le_succ' q.call.n; omega
  have hlang := NearQuarticWires.StageMain.Runtime.langBudget_le
    NearCubicGates.Close.CounterMachine.PrefixProg.noCallee (emitSizes B1) VV MM (tablesWord q) (runCostQ q) S
    (by omega) (show (128 : ℕ) ≤ S by omega) (show (10 : ℕ) ≤ S by omega) (show T ≤ S by omega) (by omega) (by omega)
    (by simp [emitSizes]) (by simp [emitSizes]) (by simp [emitSizes]) (by simp [emitSizes]) hL (by omega)
    (by simp [Sz.Lk, emitSizes]) (by simp [Sz.Bk, emitSizes])
  have hSU : S ≤ (201 + T) * U := by nlinarith
  have hS2 : S ^ 2 ≤ (201 + T) ^ 2 * U ^ 2 := by
    rw [← mul_pow]; exact Nat.pow_le_pow_left hSU 2
  calc gatherBudget B1 q ≤ 10000 * S ^ 2 * (runCostQ q + (tablesWord q).length + 1) := hlang
    _ ≤ 10000 * ((201 + T) ^ 2 * U ^ 2) * (1000000 * U ^ 3 * systemsCost q) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ hS2) hN
    _ = 10000000000 * (201 + T) ^ 2 * U ^ 5 * systemsCost q := by ring
    _ = gatherK B1 * (q.call.n + 1) ^ gatherE B1 * systemsCost q := by
        rw [scaleU_pow5]; unfold gatherK; ring

/-- **The gathering stage** `tablesWord ↦ frame gatheredWord` within `gatherK B₁ (n+1)^{gatherE B₁} systemsCost q`:
the `gather` argument of `SystemsSplit.systemsOfSplit`. -/
noncomputable def gatherStage (B1 B2 : ℕ) :
    WordFunction (ChildRequest B1 B2) tablesWord (fun q => frame (gatheredWord q))
      (fun q => gatherK B1 * (q.call.n + 1) ^ gatherE B1 * systemsCost q) :=
  WordFunction.enlargeBudget (gatherWF B1 B2) gatherBudget_le

/-- The gathering stage at any constants `K ≥ gatherK B₁`, `e ≥ gatherE B₁` (the `gather` argument of
`SystemsSplit.systemsOfSplit` for the common constants of the two parts). -/
noncomputable def gatherAt (B1 B2 K e : ℕ) (hK : gatherK B1 ≤ K) (he : gatherE B1 ≤ e) :
    WordFunction (ChildRequest B1 B2) tablesWord (fun q => frame (gatheredWord q))
      (fun q => K * (q.call.n + 1) ^ e * systemsCost q) :=
  WordFunction.enlargeBudget (gatherStage B1 B2) fun q =>
    Nat.mul_le_mul (Nat.mul_le_mul hK (Nat.pow_le_pow_right (by omega) he)) le_rfl

/-- The two parts dock into `systemsOfSplit`. -/
noncomputable example (B1 B2 : ℕ) : WordFunction (ChildRequest B1 B2) tablesWord (fun q => frame (systemsWord q))
    (fun q => (8 * max (gatherK B1) (emitK B1) + 12) * (q.call.n + 1) ^ max (gatherE B1) (emitE B1) *
      systemsCost q) :=
  systemsOfSplit (max (gatherK B1) (emitK B1)) (max (gatherE B1) (emitE B1))
    (gatherAt B1 B2 _ _ (le_max_left _ _) (le_max_left _ _))
    (WordFunction.enlargeBudget (emitStage B1 B2) fun q =>
      Nat.mul_le_mul (Nat.mul_le_mul (le_max_right _ _) (Nat.pow_le_pow_right (by omega) (le_max_right _ _))) le_rfl)

end NearQuarticWires.Reconstruct.GatherProg
