import Proof.Quartic.Reconstruct.ItemLink

/-!
# The sizes of the numbers of one item

Paper: `prop:time`, paper/paper.tex.

Every number computed while writing a listed system of a child is below `2^E` with `E = V(V+2) + 8` for the
envelope `V` of the child (`axisData_sum_lt`, `horner_lt`, `itemBig_lt`), and the numbers of the rows have bit length
at most `10^5 V^5` (`rows_natBitLength_le`). A width of `emitWidth q = 10^5 (V+1)^5 + 6 (V+1)^2 + 20` covers them
all (`emitExp_le`).
-/

set_option autoImplicit false

namespace NearQuarticWires.Reconstruct

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.Cells
open NearCubicGates.Close.Interfaces (listWord bitWord)
open NearQuarticWires.Greedy NearQuarticWires.Program

variable {B1 B2 : ℕ}

/-- The width needed by the emission of the systems of a child. -/
noncomputable def emitWidth (q : ChildRequest B1 B2) : ℕ :=
  100000 * (envelope q + 1) ^ 5 + 6 * (envelope q + 1) ^ 2 + 20

/-- The exponent bounding the numbers of the boxes. -/
noncomputable def emitExp (q : ChildRequest B1 B2) : ℕ := envelope q * (envelope q + 2) + 8

theorem succ_pow_le_two_pow (V k : ℕ) : (V + 1) ^ k ≤ 2 ^ (V * k) := by
  rw [pow_mul]; exact Nat.pow_le_pow_left Nat.lt_two_pow_self k

theorem emitExp_le (q : ChildRequest B1 B2) : 2 * emitExp q + 2 ≤ emitWidth q := by
  unfold emitExp emitWidth
  have h1 : 1 ≤ (envelope q + 1) ^ 5 := Nat.one_le_pow _ _ (by omega)
  nlinarith [h1]

/-- The scalars of a child against its envelope. -/
theorem child_le (q : ChildRequest B1 B2) :
    q.selected.1.M1 ≤ envelope q ∧ q.selected.1.A ≤ envelope q ∧ q.selected.1.Lambda ≤ envelope q ∧
      q.selected.1.hE ≤ envelope q ∧ q.call.n + 1 ≤ envelope q ∧ q.cellCall.J ≤ envelope q ∧
      ∀ j, 2 * Algorithm.traceOrder * Builder.occurrences q.call j ≤ 8 * envelope q := by
  have hS := scalarBounds q
  refine ⟨hS.M1, hS.A, hS.Lambda, hE_le_envelope q, n_succ_le_envelope q, by have := J_le_envelope q; omega,
    fun j => ?_⟩
  have := G_le_envelope q j
  change Builder.occurrences q.call j ≤ _ at this
  have e : 2 * Algorithm.traceOrder = 8 := rfl
  rw [e]; omega

/-- The Horner bound `(h_E + 1)(n + 1)^J` of a child. -/
theorem horner_le_env (q : ChildRequest B1 B2) :
    (q.selected.1.hE + 1) * (q.call.n + 1) ^ q.cellCall.J ≤ (envelope q + 1) ^ (envelope q + 1) := by
  obtain ⟨-, -, -, hE, hn, hJ, -⟩ := child_le q
  calc (q.selected.1.hE + 1) * (q.call.n + 1) ^ q.cellCall.J
      ≤ (envelope q + 1) * (envelope q + 1) ^ envelope q :=
        Nat.mul_le_mul (by omega) ((Nat.pow_le_pow_left (by omega) _).trans (Nat.pow_le_pow_right (by omega) hJ))
    _ = (envelope q + 1) ^ (envelope q + 1) := by ring

/-- `Y = (V+1)^(V+2)` and `256 Y ≤ 2^E`. -/
theorem env_Y (q : ChildRequest B1 B2) :
    1 ≤ (envelope q + 1) ^ (envelope q + 2) ∧ (envelope q + 1) ^ 2 ≤ (envelope q + 1) ^ (envelope q + 2) ∧
      (envelope q + 1) * (envelope q + 1) ^ (envelope q + 1) = (envelope q + 1) ^ (envelope q + 2) ∧
      256 * (envelope q + 1) ^ (envelope q + 2) ≤ 2 ^ emitExp q := by
  refine ⟨Nat.one_le_pow _ _ (by omega), Nat.pow_le_pow_right (by omega) (by omega), by ring, ?_⟩
  unfold emitExp
  rw [pow_add 2 (envelope q * (envelope q + 2)) 8, mul_comm (256 : ℕ)]
  exact Nat.mul_le_mul (succ_pow_le_two_pow _ _) (by norm_num)

theorem lt_two_pow_of_le {v w E : ℕ} (h : v < w) (hw : w ≤ 2 ^ E) : v < 2 ^ E := lt_of_lt_of_le h hw

/-- The numbers below `2^E` have at most `E` bits. -/
theorem natBitLength_le_emitExp (q : ChildRequest B1 B2) {v : ℕ} (h : v < 2 ^ emitExp q) :
    natBitLength v ≤ emitExp q :=
  natBitLength_le_of_lt_two_pow h (by unfold emitExp; omega)

/-- **The big number of the interval program** is below `2^E`. -/
theorem itemBig_lt (q : ChildRequest B1 B2) (j : Fin 2) :
    2 * (q.selected.1.M1 * ((q.selected.1.hE + 1) * (q.call.n + 1) ^ q.cellCall.J) +
        q.selected.1.M1 * ((q.selected.1.hE + 1) * (q.call.n + 1) ^ q.cellCall.J) +
        q.selected.1.A * (2 * Algorithm.traceOrder * Builder.occurrences q.call j) + q.selected.1.A +
        q.selected.1.Lambda + 2 * (2 * Algorithm.traceOrder * Builder.occurrences q.call j) + 2) < 2 ^ emitExp q := by
  obtain ⟨hM, hA, hL, -, -, -, hB⟩ := child_le q
  obtain ⟨y1, y2, y3, y4⟩ := env_Y q
  have hX := horner_le_env q
  set V := envelope q
  set Y := (V + 1) ^ (V + 2)
  set X := (q.selected.1.hE + 1) * (q.call.n + 1) ^ q.cellCall.J
  set B := 2 * Algorithm.traceOrder * Builder.occurrences q.call j
  have hBj := hB j
  have h1 : q.selected.1.M1 * X ≤ Y := by
    rw [← y3]; exact Nat.mul_le_mul (by omega) hX
  have h2 : q.selected.1.A * B ≤ 8 * Y := by
    calc q.selected.1.A * B ≤ (V + 1) * (8 * (V + 1)) := Nat.mul_le_mul (by omega) (by omega)
      _ = 8 * (V + 1) ^ 2 := by ring
      _ ≤ 8 * Y := Nat.mul_le_mul_left _ y2
  have h3 : V + 1 ≤ Y := le_trans (by nlinarith) y2
  omega

/-- The coordinate data of a triple: `lo' + len + B ≤ M_1 H⁺ + A + AB + 3B + 1`. -/
theorem axisTriple_sum_le (M A L B Hp Hn : ℕ) (hA : 1 ≤ A) :
    (axisTriple M A L B Hp Hn).1 + (axisTriple M A L B Hp Hn).2.1 + (axisTriple M A L B Hp Hn).2.2 ≤
      M * Hp + A + A * B + 3 * B + 1 := by
  unfold axisTriple
  simp only
  have h1 : (M * Hp + A + A * B - (M * Hn + L)) / A ≤ M * Hp + A + A * B :=
    (Nat.div_le_self _ _).trans (Nat.sub_le _ _)
  have h2 : min ((M * Hp + (L - 1) + A * B + A - M * Hn) / A) (2 * B + 1) ≤ 2 * B + 1 := min_le_right _ _
  omega

theorem digitPart_le (q : ChildRequest B1 B2) (x : SystemIndex q) (hx : x ∈ systemList q) (j : Fin 2) (s : Bool)
    (i : ℕ) : digitPart q x.2.2.1 j s i ≤ q.selected.1.hE := by
  have hd := digits_natAbs_le q x hx
  unfold digitPart NearCubicGates.CertifiedScoreSupport.extendDigits
  by_cases hi : i < q.cellCall.J + 1
  · have hz : x.2.2.1 j ⟨i, hi⟩ ∈ List.ofFn (x.2.2.1 0) ++ List.ofFn (x.2.2.1 1) := by
      fin_cases j
      · exact List.mem_append_left _ (List.mem_ofFn.mpr ⟨_, rfl⟩)
      · exact List.mem_append_right _ (List.mem_ofFn.mpr ⟨_, rfl⟩)
    have := toNat_le_of_natAbs_le (hd _ hz)
    rw [dif_pos hi]
    split <;> omega
  · rw [dif_neg hi]
    split <;> simp

/-- **The data of a coordinate of a listed system** is below `35 (V+1)^(V+2)`. -/
theorem axisData_sum_le (q : ChildRequest B1 B2) (x : SystemIndex q) (hx : x ∈ systemList q) (j : Fin 2) :
    (axisData q x.2.2.1 j).1 + (axisData q x.2.2.1 j).2.1 + (axisData q x.2.2.1 j).2.2 ≤
      35 * (envelope q + 1) ^ (envelope q + 2) := by
  classical
  obtain ⟨hM, hA, hL, -, -, -, hB⟩ := child_le q
  obtain ⟨y1, y2, y3, -⟩ := env_Y q
  have hX := horner_le_env q
  by_cases hj : j ∈ Builder.circuitSet q.call
  · have he : axisData q x.2.2.1 j = axisTriple q.selected.1.M1 q.selected.1.A q.selected.1.Lambda
        (2 * Algorithm.traceOrder * Builder.occurrences q.call j)
        (hornerN (fun i => q.selected.1.factors.getD i 0) (digitPart q x.2.2.1 j true) q.cellCall.J)
        (hornerN (fun i => q.selected.1.factors.getD i 0) (digitPart q x.2.2.1 j false) q.cellCall.J) := by
      unfold axisData; rw [if_pos hj]; rfl
    rw [he]
    refine (axisTriple_sum_le _ _ _ _ _ _ (one_le_A q)).trans ?_
    have hH := hornerN_le (fun i => q.selected.1.factors.getD i 0) (digitPart q x.2.2.1 j true) q.call.n
      q.selected.1.hE (factors_getD_le q) (digitPart_le q x hx j true) q.cellCall.J
    set V := envelope q
    set Y := (V + 1) ^ (V + 2)
    have h1 : q.selected.1.M1 * hornerN (fun i => q.selected.1.factors.getD i 0) (digitPart q x.2.2.1 j true)
        q.cellCall.J ≤ Y := by
      rw [← y3]; exact Nat.mul_le_mul (by omega) (hH.trans hX)
    have hBj := hB j
    have h2 : q.selected.1.A * (2 * Algorithm.traceOrder * Builder.occurrences q.call j) ≤ 8 * Y := by
      calc _ ≤ (V + 1) * (8 * (V + 1)) := Nat.mul_le_mul (by omega) (by omega)
        _ = 8 * (V + 1) ^ 2 := by ring
        _ ≤ 8 * Y := Nat.mul_le_mul_left _ y2
    have h3 : V + 1 ≤ Y := le_trans (by nlinarith) y2
    omega
  · have he : axisData q x.2.2.1 j = (0, 1, 0) := by unfold axisData; rw [if_neg hj]
    rw [he]
    simp only
    omega

/-- The number of points of a coordinate interval is at most `2B + 1 ≤ 16 V + 1`. -/
theorem axisData_len_le (q : ChildRequest B1 B2) (δ : Fin 2 → Fin (q.cellCall.J + 1) → ℤ) (j : Fin 2) :
    (axisData q δ j).2.1 ≤ 16 * envelope q + 1 := by
  classical
  have hB := (child_le q).2.2.2.2.2.2 j
  unfold axisData
  split
  · exact (Nat.sub_le _ _).trans ((min_le_right _ _).trans (by omega))
  · simp only
    omega

/-- **The rows of a listed system** have numbers of bit length at most `10^5 V^5`, and at most `10^5 V^5` rows. -/
theorem rows_natBitLength_le (q : ChildRequest B1 B2) (x : SystemIndex q) :
    ∀ v ∈ (systemAt q x).rows.length :: (systemAt q x).rows.flatMap rowNats,
      natBitLength v ≤ 100000 * envelope q ^ 5 := by
  have hs := sysWord_length_le_envelope q q.seedPrefix x.1 x.2.2.2 x.2.1 x.2.2.1
  change (NearCubicGates.Close.Interfaces.Formats.sysWord (systemAt q x)).length ≤ _ at hs
  rw [sysWord_systemAt, rowsWord_eq _ (systemAt_rows_two q x)] at hs
  simp only [List.length_append] at hs
  intro v hv
  rcases List.mem_cons.mp hv with rfl | hv
  · have := natWord_length (systemAt q x).rows.length
    omega
  · have h1 : (natWord v).length ≤ (((systemAt q x).rows.flatMap rowNats).flatMap natWord).length := by
      obtain ⟨l1, l2, hl⟩ := List.append_of_mem hv
      rw [hl, List.flatMap_append, List.flatMap_cons]
      simp only [List.length_append]
      omega
    have := natWord_length v
    omega

theorem length_le_flatMap_natWord : ∀ l : List ℕ, l.length ≤ (l.flatMap natWord).length
  | [] => by simp
  | v :: l => by
    rw [List.flatMap_cons, List.length_append, List.length_cons, natWord_length]
    have := length_le_flatMap_natWord l
    omega

theorem rows_length_le (q : ChildRequest B1 B2) (x : SystemIndex q) :
    5 * (systemAt q x).rows.length ≤ 100000 * envelope q ^ 5 := by
  have hs := sysWord_length_le_envelope q q.seedPrefix x.1 x.2.2.2 x.2.1 x.2.2.1
  change (NearCubicGates.Close.Interfaces.Formats.sysWord (systemAt q x)).length ≤ _ at hs
  rw [sysWord_systemAt, rowsWord_eq _ (systemAt_rows_two q x)] at hs
  simp only [List.length_append] at hs
  have h1 := length_le_flatMap_natWord ((systemAt q x).rows.flatMap rowNats)
  rw [rowNats_length] at h1
  omega

end NearQuarticWires.Reconstruct
