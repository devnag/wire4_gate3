import Proof.Quartic.Reconstruct.GatherProgLinkLists

/-!
# The gathering program: the numbers of the printed tables

Paper: Step 3 of `sec:algorithm`, paper/paper.tex.

The data of a group `(s, σ, δ)` (`grpD`): the part, the pattern bits, the digits and, for every row `(p, ρ_Y)` of
`rowList`, the table printed for `(s, σ, p, δ, ρ_Y)`. The words of the group's tables are the numbers of `grpD`
(`groupIn_eq`), and the input of the gathering is the context, `|printList|` and the numbers of the groups
(`tablesWord_nats`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearQuarticWires.Reconstruct.GatherProg

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.Cells
open NearCubicGates.Close.Interfaces (listWord bitWord)
open NearQuarticWires.Greedy NearQuarticWires.Program
open NearQuarticWires.Reconstruct

variable {B1 B2 : ℕ}

theorem listWord_bit (L : List Bool) : listWord bitWord L = (L.length :: L.map bitNat).flatMap natWord := by
  simp only [listWord, List.flatMap_cons, List.length_map, List.flatMap_map]
  rfl

theorem listWord_int (L : List ℤ) :
    listWord NearCubicGates.Close.Interfaces.intWord L = (L.length :: L.flatMap intNats).flatMap natWord := by
  simp only [listWord, List.flatMap_cons, List.flatMap_assoc]
  congr 1
  exact List.flatMap_congr fun z _ => intWord_eq_nats z

/-- The digits of a group, flattened. -/
noncomputable def dflat (q : ChildRequest B1 B2) (δ : Fin 2 → Fin (q.cellCall.J + 1) → ℤ) : List ℤ :=
  (List.ofFn fun i : Fin 2 => List.ofFn fun j : Fin (q.cellCall.J + 1) => δ i j).flatten

/-- The row of a group for `(p, ρ_Y)`: the prime, the residues and the table printed for it. -/
noncomputable def rowD (q : ChildRequest B1 B2) (G : Grp q) (pr : {p // p ∈ primeList q.cellCall} × (Fin 2 → ℤ)) :
    RowD := (pr.1.1, pr.2 0, pr.2 1, printTable (tableAt q G pr))

/-- **The data of a group of printed tables.** -/
noncomputable def grpD (q : ChildRequest B1 B2) (G : Grp q) : GrpD :=
  ⟨bitNat G.1, (List.ofFn G.2.1).map bitNat, dflat q G.2.2, (rowList q).map (rowD q G)⟩

theorem tableItemWord_eq (q : ChildRequest B1 B2) (G : Grp q) (pr : {p // p ∈ primeList q.cellCall} × (Fin 2 → ℤ)) :
    tableItemWord (tableAt q G pr) = (tblNats ((grpD q G).tbl (rowD q G pr))).flatMap natWord := by
  have e1 : tableItemWord (tableAt q G pr) = bitWord G.1 ++ listWord bitWord (List.ofFn G.2.1) ++
      natWord pr.1.1 ++ listWord NearCubicGates.Close.Interfaces.intWord (dflat q G.2.2) ++
      listWord NearCubicGates.Close.Interfaces.intWord [pr.2 0, pr.2 1] ++
      listWord NearCubicGates.Close.Interfaces.intWord (printTable (tableAt q G pr)) := by
    simp only [tableItemWord, printIndexWord, tableAt, printRequestOf, dflat, List.ofFn_succ, List.ofFn_zero]
    rfl
  rw [e1, listWord_bit, listWord_int, listWord_int, listWord_int]
  simp only [tblNats, GrpD.tbl, grpD, rowD, bitWord, bitNat, List.flatMap_append, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.length_map, List.length_cons, List.length_nil, List.append_assoc,
    List.cons_append, List.nil_append]

/-- **The words of the tables of a group** are the numbers of its data. -/
theorem groupIn_eq (q : ChildRequest B1 B2) (G : Grp q) : groupIn q G = (grpD q G).nats.flatMap natWord := by
  unfold groupIn GrpD.nats
  rw [List.flatMap_map, List.flatMap_assoc]
  simp only [grpD, List.flatMap_map]
  exact List.flatMap_congr fun pr _ => tableItemWord_eq q G pr

/-! ## The gathered items of a group -/

theorem active_eq (σ : Cycle.SignPattern Algorithm.traceOrder) :
    active σ = decide (((List.ofFn σ).map bitNat).sum % 2 = 0) := by
  have h : ∀ σ ∈ patternList, active σ = decide (((List.ofFn σ).map bitNat).sum % 2 = 0) := by decide
  exact h σ (mem_patternList σ)

theorem rowList_length (q : ChildRequest B1 B2) : (rowList q).length = tablesPerGroup q := by
  unfold rowList tablesPerGroup
  rw [List.length_flatMap, List.length_flatMap]
  conv_rhs => rw [← List.attach_map_subtype_val (primeList q.cellCall), List.map_map]
  congr 1
  refine List.map_congr_left fun p _ => ?_
  simp

theorem residue_nonneg (q : ChildRequest B1 B2) (p : ℕ) (ρ : Fin 2 → ℤ) (hρ : ρ ∈ residueListOf q p) (i : Fin 2) :
    0 ≤ ρ i := by
  have h := mem_residueListOf hρ
  unfold residueSet at h
  rw [Fintype.mem_piFinset] at h
  have hi := h i
  split_ifs at hi with hc
  · exact (Finset.mem_Ico.mp hi).1
  · rw [Finset.mem_singleton.mp hi]

theorem mem_rowList (q : ChildRequest B1 B2) (pr : {p // p ∈ primeList q.cellCall} × (Fin 2 → ℤ))
    (h : pr ∈ rowList q) : pr.2 ∈ residueListOf q pr.1.1 := by
  unfold rowList at h
  obtain ⟨p, -, hp⟩ := List.mem_flatMap.mp h
  obtain ⟨ρ, hρ, rfl⟩ := List.mem_map.mp hp
  exact hρ

/-- The row of a listed system for `(p, ρ_Y)`. -/
noncomputable def rowOf (q : ChildRequest B1 B2) (G : Grp q) (z : Fin q.cellCall.ncol)
    (pr : {p // p ∈ primeList q.cellCall} × (Fin 2 → ℤ)) : ℕ × List ℕ × ℕ :=
  (pr.1.1, [(pr.2 0).toNat, (pr.2 1).toNat], ((printTable (tableAt q G pr)).getD z.val 0).toNat)

theorem systemAt_rows_rowList (q : ChildRequest B1 B2) (G : Grp q) (z : Fin q.cellCall.ncol) :
    (systemAt q (G.1, G.2.1, G.2.2, z)).rows = (rowList q).map (rowOf q G z) := by
  rw [systemAt_rows]
  unfold rowList
  rw [List.map_flatMap]
  refine List.flatMap_congr fun p _ => ?_
  rw [List.map_map]
  rfl

theorem printTable_length (r : PrintRequest B1 B2) : (printTable r).length = r.child.cellCall.ncol := by
  simp [printTable]

theorem grpD_rows_length (q : ChildRequest B1 B2) (G : Grp q) : (grpD q G).rows.length = (rowList q).length := by
  simp [grpD]

theorem grpD_ents (q : ChildRequest B1 B2) (G : Grp q) :
    ∀ r ∈ (grpD q G).rows, r.2.2.2.length = (certNats q).length := by
  intro r hr
  simp only [grpD, List.mem_map] at hr
  obtain ⟨pr, -, rfl⟩ := hr
  rw [certNats_length]
  exact printTable_length _

theorem cfOf_lt (g : GrpD) (bits : List ℕ) : ∀ x ∈ cfOf g bits, x < pwOf g bits := fun x hx => by
  unfold pwOf; have := List.le_sum_of_mem hx; omega

theorem rowN_eq (q : ChildRequest B1 B2) (G : Grp q) (j : ℕ) (hj : j < (certList q).length) (k : ℕ)
    (hk : k < (rowList q).length) :
    (rowN ((grpD q G).rows.flatMap rowI)
      (recsJ (grpD q G).rows.length (ncOf (certNats q)) (pwOf (grpD q G) (certNats q)) (cfOf (grpD q G) (certNats q)))
      (pwOf (grpD q G) (certNats q)) (j * (grpD q G).rows.length) k).flatMap natWord =
      rowWord (rowOf q G (certList q)[j] (rowList q)[k]) := by
  set tg := (grpD q G).rows.length with htg
  have htg' : tg = (rowList q).length := grpD_rows_length q G
  have hnc : ncOf (certNats q) = (certList q).length := ncOf_certNats q
  have hkg : k < (grpD q G).rows.length := by rw [grpD_rows_length]; exact hk
  have hrk : (grpD q G).rows[k] = rowD q G (rowList q)[k] := by simp [grpD]
  -- the row index
  have hI : ∀ i < 3, ((grpD q G).rows.flatMap rowI).getD (3 * k + i) 0 = (rowI (rowD q G (rowList q)[k])).getD i 0 :=
    fun i hi => by
      rw [flatMap_getD_uniform _ rowI 3 (fun _ _ => rfl) k i hkg hi, hrk]
  have hI0 := hI 0 (by norm_num)
  have hI1 := hI 1 (by norm_num)
  have hI2 := hI 2 (by norm_num)
  rw [Nat.add_zero] at hI0
  -- the count
  have hlt : j * tg + k < tg * ncOf (certNats q) := by
    rw [hnc]
    calc j * tg + k < j * tg + tg := by omega
      _ = (j + 1) * tg := by ring
      _ ≤ (certList q).length * tg := Nat.mul_le_mul_right _ hj
      _ = tg * (certList q).length := Nat.mul_comm _ _
  have hC := recsJ_getD_mod tg (ncOf (certNats q)) (pwOf (grpD q G) (certNats q)) (cfOf (grpD q G) (certNats q))
    (by unfold pwOf; omega) (cfOf_lt _ _) (j * tg + k) hlt
  have hcnt : cntAt tg (ncOf (certNats q)) (cfOf (grpD q G) (certNats q)) (j * tg + k) =
      ((printTable (tableAt q G (rowList q)[k])).getD ((certList q)[j]).val 0).toNat := by
    unfold cntAt
    have htg0 : 0 < tg := by omega
    rw [Nat.add_comm (j * tg) k, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega : k < tg),
      Nat.add_mul_div_right _ _ htg0, Nat.div_eq_of_lt (by omega : k < tg), Nat.zero_add, Nat.mul_comm k]
    unfold cfOf
    rw [flatMap_getD_uniform _ (cntsOf (certNats q)) (ncOf (certNats q)) (fun r hr => by
      unfold cntsOf; exact cnts_length _ _ (grpD_ents q G r hr)) k j hkg (by rw [hnc]; exact hj), hrk]
    unfold cntsOf rowD
    simp only
    rw [cnts_certNats q _ (printTable_length _), List.getD_eq_getElem _ _ (by simp; exact hj), List.getElem_map]
  -- the residues
  have hmem := mem_rowList q (rowList q)[k] (List.getElem_mem hk)
  have hr0 := residue_nonneg q _ _ hmem 0
  have hr1 := residue_nonneg q _ _ hmem 1
  rw [rowWord_eq _ (by simp [rowOf])]
  unfold rowN
  rw [hI0, hI1, hI2, hC, hcnt]
  simp only [rowI, rowD, rowOf, rowNats, List.getD_cons_zero, List.getD_cons_succ]
  have e0 : ((rowList q)[k].2 0).toNat = ((rowList q)[k].2 0).natAbs := by omega
  have e1 : ((rowList q)[k].2 1).toNat = ((rowList q)[k].2 1).natAbs := by omega
  rw [e0, e1]

end NearQuarticWires.Reconstruct.GatherProg
