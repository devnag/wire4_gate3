import Proof.Quartic.Reconstruct.GatherProgBounds
import Proof.Quartic.Reconstruct.EmitFinal

/-!
# The gathering stage as a word function

Paper: Step 3 of `sec:algorithm`, paper/paper.tex.

On the printed tables of a child (`tablesWord`), with a width of at least `emitWidth q`, the gathering program
writes the framed gathered word (`gatherS_runQ`); with the sizes `emitSizes` of the emission stage it is the word
function `gatherWF`.
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

/-- The cost of one group of a child (the same for every group). -/
noncomputable def gcQ (q : ChildRequest B1 B2) : ℕ :=
  tablesPerGroup q * (tblCostU (ellQ q) 8 (2 * (q.cellCall.J + 1)) q.cellCall.ncol + 4) +
    ncOf (certNats q) * (itemCostG (ellQ q) (2 * (q.cellCall.J + 1)) (tablesPerGroup q) + 2) +
    3 * tablesPerGroup q + 25 * (tablesPerGroup q * ncOf (certNats q)) + 60

/-- The cost of the run of a child. -/
noncomputable def runCostQ (q : ChildRequest B1 B2) : ℕ :=
  gatherCost (ellQ q) q.cellCall.J q.cellCall.ncol (groupList q).length (gcQ q)

theorem dflat_length (q : ChildRequest B1 B2) (δ : Fin 2 → Fin (q.cellCall.J + 1) → ℤ) :
    (dflat q δ).length = 2 * (q.cellCall.J + 1) := by
  unfold dflat; rw [digits_flatten, digits_length]

theorem grpCost_eq (q : ChildRequest B1 B2) (G : Grp q) : grpCost (ellQ q) (grpD q G) (certNats q) = gcQ q := by
  unfold grpCost gcQ
  have h1 : (grpD q G).rows.length = tablesPerGroup q := by rw [grpD_rows_length, rowList_length]
  have h2 : (grpD q G).pat.length = 8 := by simp [grpD]
  have h3 : (grpD q G).dl.length = 2 * (q.cellCall.J + 1) := dflat_length q G.2.2
  rw [h1, h2, h3, certNats_length]

theorem lt_pow_of_le {X k W : ℕ} (hX : X ≤ 2 ^ k) (hk : k + 1 ≤ W) : 2 * X ≤ 2 ^ W ∧ X < 2 ^ W := by
  have h1 : 2 * 2 ^ k ≤ 2 ^ W := by rw [← pow_succ']; exact Nat.pow_le_pow_right (by norm_num) hk
  have h2 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  omega

/-- **The run of the gathering on a child.** -/
theorem gatherS_runQ (q : ChildRequest B1 B2) (C : Ctx) (hinp : C.inp = tablesWord q) (hW : emitWidth q ≤ C.Wd) :
    Hs C gatherS (a0 : DS VV MM) (runCostQ q) (fun b => b.out = frame (gatheredWord q)) := by
  classical
  obtain ⟨e1, e2, e3, e4⟩ := ellQ_ge q
  have hWd0 := hW
  unfold emitWidth at hWd0
  obtain ⟨-, -, -, -, hn, hJ, -⟩ := child_le q
  have hP := P_le_envelope q
  have hcfQ := cfOf_le q
  set V := envelope q with hV
  have hWd : 100000 * (V + 1) ^ 5 ≤ C.Wd := by omega
  have hV2 : (V + 1) ^ 2 ≤ (V + 1) ^ 5 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hVV : V * V + 8 * V + 2 ≤ C.Wd := by nlinarith
  have hℓW : ellQ q + 2 ≤ C.Wd := by unfold ellQ; nlinarith
  have hEW : 2 * emitExp q + 2 ≤ C.Wd := (emitExp_le q).trans hW
  -- the counts
  have htg3 : tablesPerGroup q ≤ 2 ^ (3 * V) := by
    calc tablesPerGroup q ≤ q.selected.1.P ^ 3 := tablesPerGroup_le q
      _ ≤ (V + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
      _ ≤ 2 ^ (V * 3) := succ_pow_le_two_pow V 3
      _ = 2 ^ (3 * V) := by rw [Nat.mul_comm]
  have hncol : q.cellCall.ncol ≤ 2 ^ V := by
    rw [ncol_eq]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hnc : ncOf (certNats q) ≤ 2 ^ V := by
    rw [ncOf_certNats]
    exact (List.length_filter_le _ _).trans (by simp [certList_eq]; exact hncol) |>.trans le_rfl
  have htn : tablesPerGroup q * ncOf (certNats q) ≤ 2 ^ (4 * V) := by
    calc tablesPerGroup q * ncOf (certNats q) ≤ 2 ^ (3 * V) * 2 ^ V := Nat.mul_le_mul htg3 hnc
      _ = 2 ^ (4 * V) := by rw [← pow_add]; ring_nf
  have hm : (printList q).length ≤ 2 ^ (9 + V * (2 * V + 5)) := by
    calc (printList q).length ≤ tableCount q := printList_length_le q
      _ = 2 * 4 ^ Algorithm.traceOrder * q.selected.1.P ^ (2 * (q.cellCall.J + 1) + 3) := rfl
      _ ≤ 2 * 256 * (V + 1) ^ (2 * V + 5) := by
          have : q.selected.1.P ^ (2 * (q.cellCall.J + 1) + 3) ≤ (V + 1) ^ (2 * V + 5) :=
            (Nat.pow_le_pow_left (by omega) _).trans (Nat.pow_le_pow_right (by omega) (by omega))
          have e : (4 : ℕ) ^ Algorithm.traceOrder = 256 := rfl
          rw [e]; omega
      _ ≤ 2 ^ 9 * 2 ^ (V * (2 * V + 5)) := by
          have := succ_pow_le_two_pow V (2 * V + 5); norm_num; omega
      _ = 2 ^ (9 + V * (2 * V + 5)) := by rw [← pow_add]
  have hmℓ : 9 + V * (2 * V + 5) + 1 ≤ ellQ q := by unfold ellQ; nlinarith
  have hglm : (groupList q).length ≤ (printList q).length := by
    rw [printList_length]; exact Nat.le_mul_of_pos_right _ (tablesPerGroup_pos q)
  -- the groups
  have hok : ∀ g ∈ grpsQ q, GrpOK C (ellQ q) (2 * (q.cellCall.J + 1)) (tablesPerGroup q) (certNats q) g := by
    intro g hg
    unfold grpsQ at hg
    obtain ⟨G, hG, rfl⟩ := List.mem_map.mp hg
    have hrows : (grpD q G).rows.length = tablesPerGroup q := by rw [grpD_rows_length, rowList_length]
    have hcf := hcfQ G
    have hcfl : (cfOf (grpD q G) (certNats q)).length = tablesPerGroup q * ncOf (certNats q) := by
      rw [cfOf, cntsOf_flatMap_length _ _ (grpD_ents q G), hrows, Nat.mul_comm]
    have hsum : (cfOf (grpD q G) (certNats q)).sum ≤ tablesPerGroup q * ncOf (certNats q) * 2 ^ (V * V) := by
      have := List.sum_le_card_nsmul _ _ hcf
      rw [hcfl, smul_eq_mul] at this; exact this
    have hPW : pwOf (grpD q G) (certNats q) ≤ 2 ^ (4 * V + V * V + 1) := by
      unfold pwOf
      have h1 : tablesPerGroup q * ncOf (certNats q) * 2 ^ (V * V) ≤ 2 ^ (4 * V) * 2 ^ (V * V) :=
        Nat.mul_le_mul_right _ htn
      have h2 : 2 ^ (4 * V) * 2 ^ (V * V) = 2 ^ (4 * V + V * V) := by rw [← pow_add]
      have h3 : 2 ^ (4 * V + V * V + 1) = 2 * 2 ^ (4 * V + V * V) := by rw [pow_succ]; ring
      have h4 : 1 ≤ 2 ^ (4 * V + V * V) := Nat.one_le_two_pow
      omega
    refine ⟨?_, hrows, dflat_length q G.2.2, grpD_ents q G, grpD_nats_bits q G hG, ?_, ?_, ?_, ?_⟩
    · intro h
      have : (grpD q G).rows.length = 0 := by rw [h]; rfl
      have := tablesPerGroup_pos q
      omega
    · intro x hx
      have := nbl_le_of_le_pow (hcf x hx); omega
    · have h1 : tablesPerGroup q * ncOf (certNats q) * pwOf (grpD q G) (certNats q) ≤
          2 ^ (4 * V) * 2 ^ (4 * V + V * V + 1) := Nat.mul_le_mul htn hPW
      have h2 : 2 ^ (4 * V) * 2 ^ (4 * V + V * V + 1) = 2 ^ (V * V + 8 * V + 1) := by rw [← pow_add]; ring_nf
      exact (lt_pow_of_le (h1.trans h2.le) (by omega)).2
    · exact (lt_pow_of_le hPW (by omega)).1
    · have hl : (grpD q G).pat.length = 8 := by simp [grpD]
      have hs : (grpD q G).pat.sum ≤ 8 := by
        have : ∀ x ∈ (grpD q G).pat, x ≤ 1 := by
          intro x hx; simp only [grpD, List.mem_map] at hx
          obtain ⟨b, -, rfl⟩ := hx; unfold bitNat; split <;> omega
        have := List.sum_le_card_nsmul _ _ this
        rw [hl, smul_eq_mul] at this; omega
      exact (lt_pow_of_le (show (grpD q G).pat.sum + (grpD q G).pat.length ≤ 2 ^ 4 by omega) (by omega)).2
  -- the run
  have hsysl := systemList_length_lt q
  rw [systemList_length_eq] at hsysl
  have hH := head_values_lt q
  have hb : ∀ v, v < 2 ^ (2 * emitExp q) → natBitLength v ≤ ellQ q := fun v hv => by
    have := natBitLength_le_of_lt_two_pow hv (by unfold emitExp; omega); omega
  have hctx : ∀ v ∈ ctxQ q, natBitLength v ≤ ellQ q := by
    unfold ctxQ ctxNats pre5 mid4
    simp only [List.forall_mem_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, forall_const,
      implies_true, and_true]
    refine ⟨⟨⟨⟨⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩, ?_⟩, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩, ?_⟩
    all_goals first
      | (intro x hx; exact hb x (hH x (by simp [hx])))
      | exact hb _ (hH _ (by simp [bitNat]))
  have hinp' : C.inp = (ctxNats (pre5 q) q.selected.1.factors (mid4 q) (tablesPerGroup q) (certNats q) ++
      (printList q).length :: (grpsQ q).flatMap GrpD.nats).flatMap natWord := by
    rw [hinp, tablesWord_nats]; rfl
  have hcost : ∀ g ∈ grpsQ q, grpCost (ellQ q) g (certNats q) ≤ gcQ q := fun g hg => by
    unfold grpsQ at hg; obtain ⟨G, -, rfl⟩ := List.mem_map.mp hg; rw [grpCost_eq]
  have hGN : (printList q).length / tablesPerGroup q = (grpsQ q).length := by
    rw [printList_length, Nat.mul_div_cancel _ (tablesPerGroup_pos q), grpsQ, List.length_map]
  have h2ℓ : 2 ≤ ellQ q := by unfold ellQ; nlinarith
  have hmb : natBitLength (printList q).length ≤ ellQ q := by have := nbl_le_of_le_pow hm; omega
  have hmsb : natBitLength ((printList q).length / tablesPerGroup q / 2 * ncOf (certNats q)) ≤ ellQ q := by
    have := natBitLength_le_of_lt_two_pow hsysl (by unfold emitExp; omega); omega
  have hWb : (certNats q).sum + (certNats q).length < 2 ^ C.Wd := by
    have hs : (certNats q).sum ≤ (certNats q).length := by
      have := List.sum_le_card_nsmul _ _ (certNats_le q); rw [smul_eq_mul] at this; omega
    rw [certNats_length] at hs ⊢
    exact (lt_pow_of_le (show (certNats q).sum + q.cellCall.ncol ≤ 2 ^ (V + 1) by rw [pow_succ]; omega)
      (by omega)).2
  have hfs : q.selected.1.factors.length < 2 ^ C.Wd := by
    rw [factors_length]; exact (lt_pow_of_le (Nat.lt_two_pow_self (n := q.cellCall.J)).le (by omega)).2
  have hmsW : (printList q).length / tablesPerGroup q / 2 * ncOf (certNats q) < 2 ^ C.Wd :=
    lt_of_lt_of_le hsysl (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hdl : 2 * (q.cellCall.J + 1) < 2 ^ C.Wd :=
    (lt_pow_of_le (show 2 * (q.cellCall.J + 1) ≤ 2 ^ (2 * V + 2) from
      (Nat.lt_two_pow_self (n := 2 * (q.cellCall.J + 1))).le.trans (Nat.pow_le_pow_right (by norm_num) (by omega)))
      (by omega)).2
  have hGs : (grpsQ q).length < 2 ^ C.Wd := by
    rw [grpsQ, List.length_map]; exact (lt_pow_of_le (hglm.trans hm) (by omega)).2
  have hrun := gatherS_run C (pre5 q) q.selected.1.factors (mid4 q) rfl rfl (tablesPerGroup q) (certNats q)
    (printList q).length (grpsQ q) (ellQ q) (2 * (q.cellCall.J + 1)) (gcQ q) hinp' hok hcost
    (tablesPerGroup_pos q) hGN (sum_eq_ncOf _ (certNats_le q)) h2ℓ hℓW hctx hmb hmsb
    (lt_pow_of_le hnc (by omega)).1 (lt_pow_of_le htg3 (by omega)).1 hWb hfs hmsW hdl
    (lt_pow_of_le hnc (by omega)).2 hGs
  refine hrun.mono (by
    unfold runCostQ
    rw [factors_length, certNats_length, grpsQ, List.length_map]) ?_
  intro b hb
  rw [hb, frame_gatheredWord_nats]
  rfl

end NearQuarticWires.Reconstruct.GatherProg
