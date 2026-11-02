import Proof.Quartic.Reconstruct.GatherProgLink

/-!
# The gathering program: the words of the input and of the output

Paper: Step 3 of `sec:algorithm`, paper/paper.tex.

The numbers written for a group are its gathered items (`groupOut_eq`); the input of the gathering is the context,
`|printList|` and the numbers of the groups (`tablesWord_nats`), and its framed output the context,
`|systemList| = (|printList| / tg / 2)·n_c` and the outputs of the groups (`frame_gatheredWord_nats`).
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

theorem itemN_eq (q : ChildRequest B1 B2) (G : Grp q) (j : ℕ) (hj : j < (certList q).length) :
    (itemN (grpD q G).s (grpD q G).dl.length ((grpD q G).dl.flatMap intNats) ((grpD q G).rows.flatMap rowI)
      (recsJ (grpD q G).rows.length (ncOf (certNats q)) (pwOf (grpD q G) (certNats q)) (cfOf (grpD q G) (certNats q)))
      (pwOf (grpD q G) (certNats q)) (grpD q G).rows.length j).flatMap natWord =
      gatheredItem q (G.1, G.2.1, G.2.2, (certList q)[j]) := by
  unfold itemN gatheredItem
  rw [systemAt_rows_rowList, listWord_int]
  have hrows : (rowsN ((grpD q G).rows.flatMap rowI)
      (recsJ (grpD q G).rows.length (ncOf (certNats q)) (pwOf (grpD q G) (certNats q)) (cfOf (grpD q G) (certNats q)))
      (pwOf (grpD q G) (certNats q)) (j * (grpD q G).rows.length) (grpD q G).rows.length).flatMap natWord =
      ((rowList q).map (rowOf q G (certList q)[j])).flatMap rowWord := by
    unfold rowsN
    rw [List.flatMap_assoc, List.flatMap_map, grpD_rows_length]
    exact range_flatMap_eq (rowList q) _ _ fun k hk => by
      rw [← rowN_eq q G j hj k hk, grpD_rows_length]
  simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, hrows, listWord]
  simp only [grpD, dflat, List.length_map, bitWord, bitNat, List.append_assoc]

/-- **The output of a group** is its gathered items. -/
theorem groupOut_eq (q : ChildRequest B1 B2) (G : Grp q) :
    groupOut q G = (grpOut (grpD q G) (certNats q)).flatMap natWord := by
  unfold groupOut grpOut
  have hpat : (grpD q G).pat = (List.ofFn G.2.1).map bitNat := rfl
  rw [hpat, active_eq]
  by_cases h : ((List.ofFn G.2.1).map bitNat).sum % 2 = 0
  · rw [if_pos (by simpa using h), if_pos h]
    unfold itemsN
    rw [List.flatMap_assoc, show List.range (ncOf (certNats q)) = List.range (certList q).length by
      rw [ncOf_certNats]]
    exact (range_flatMap_eq (certList q) _ _ fun j hj => itemN_eq q G j hj).symm
  · rw [if_neg (by simpa using h), if_neg h]
    rfl

/-! ## The words -/

/-- The first five numbers of the context. -/
noncomputable def pre5 (q : ChildRequest B1 B2) : List ℕ :=
  [q.call.n, q.selected.1.M1, q.selected.1.A, q.selected.1.Lambda, q.cellCall.J]

/-- The four numbers of the context after the rates. -/
noncomputable def mid4 (q : ChildRequest B1 B2) : List ℕ :=
  [bitNat (decide (q.call.kind = .pair)), 2 * Algorithm.traceOrder * Builder.occurrences q.call 0,
    2 * Algorithm.traceOrder * Builder.occurrences q.call 1, q.cellCall.ncol]

/-- The numbers of the context of a child. -/
noncomputable def ctxQ (q : ChildRequest B1 B2) : List ℕ :=
  ctxNats (pre5 q) q.selected.1.factors (mid4 q) (tablesPerGroup q) (certNats q)

theorem contextWord_nats (q : ChildRequest B1 B2) : contextWord q = (ctxQ q).flatMap natWord := by
  unfold contextWord ctxQ ctxNats pre5 mid4 certNats
  simp only [listWord, bitWord, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.length_map, List.flatMap_map, List.append_assoc, bitNat]
  rfl

/-- The groups of a child. -/
noncomputable def grpsQ (q : ChildRequest B1 B2) : List GrpD := (groupList q).map (grpD q)

/-- **The input of the gathering.** -/
theorem tablesWord_nats (q : ChildRequest B1 B2) :
    tablesWord q = (ctxQ q ++ (printList q).length :: (grpsQ q).flatMap GrpD.nats).flatMap natWord := by
  rw [tablesWord_groups, contextWord_nats]
  simp only [List.flatMap_append, List.flatMap_cons, grpsQ, List.flatMap_map, List.flatMap_assoc, List.append_assoc]
  congr 2
  exact List.flatMap_congr fun G _ => groupIn_eq q G

/-! ## The counts -/

theorem tablesPerGroup_pos (q : ChildRequest B1 B2) : 0 < tablesPerGroup q := by
  classical
  obtain ⟨p, hp⟩ := (rules q).primes_nonempty
  have hp' : p ∈ primeList q.cellCall := (mem_primeList _ p).mpr hp
  have hp2 : 2 ≤ p := (PrintRequest.prime_prime (printRequestOf q true (fun _ => true) (fun _ _ => 0) ⟨p, hp'⟩
    (fun _ => 0))).two_le
  have hne : residueListOf q p ≠ [] := by
    have hA : ∀ c : Fin 2, 0 < (if c ∈ Builder.circuitSet q.call then (List.range p).map Int.ofNat
        else [0]).length := by
      intro c; split_ifs <;> simp; omega
    unfold residueListOf
    apply List.ne_nil_of_length_pos
    rw [List.length_map, List.length_product]
    exact Nat.mul_pos (hA 0) (hA 1)
  unfold tablesPerGroup
  rw [List.length_pos_iff]
  intro h
  rw [List.flatMap_eq_nil_iff] at h
  exact hne (h p hp')

theorem printList_length (q : ChildRequest B1 B2) :
    (printList q).length = (groupList q).length * tablesPerGroup q := by
  rw [printList_groups, List.length_flatMap, ← rowList_length]
  simp [List.map_const', List.sum_replicate, Nat.mul_comm]

theorem length_flatMap_const {α β : Type} (L : List α) (f : α → List β) (c : ℕ) (h : ∀ a ∈ L, (f a).length = c) :
    (L.flatMap f).length = L.length * c := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.flatMap_cons, List.length_append, h a List.mem_cons_self,
      ih (fun b hb => h b (List.mem_cons_of_mem _ hb)), List.length_cons]
    ring

theorem groupList_length (q : ChildRequest B1 B2) : (groupList q).length = 2 * (256 * (digitList q).length) := by
  unfold groupList
  rw [length_flatMap_const _ _ (256 * (digitList q).length) fun s _ => by
    rw [length_flatMap_const _ _ (digitList q).length fun σ _ => by simp, patternList_length]; rfl]
  rfl

theorem systemList_length (q : ChildRequest B1 B2) :
    (systemList q).length = 2 * (128 * ((digitList q).length * (certList q).length)) := by
  unfold systemList
  rw [length_flatMap_const _ _ (128 * ((digitList q).length * (certList q).length)) fun s _ => by
    rw [length_flatMap_const _ _ ((digitList q).length * (certList q).length) fun σ _ => by
      rw [length_flatMap_const _ _ (certList q).length fun δ _ => by simp], activePatterns_length]]
  rfl

theorem systemList_length_eq (q : ChildRequest B1 B2) :
    (systemList q).length = (printList q).length / tablesPerGroup q / 2 * ncOf (certNats q) := by
  rw [printList_length, Nat.mul_div_cancel _ (tablesPerGroup_pos q), groupList_length, systemList_length,
    ncOf_certNats]
  have : 2 * (256 * (digitList q).length) / 2 = 256 * (digitList q).length := by omega
  rw [this]; ring

/-- **The output of the gathering.** -/
theorem frame_gatheredWord_nats (q : ChildRequest B1 B2) :
    RepairOrdinary.frame (gatheredWord q) = marksD 1 ((ctxQ q ++
      ((printList q).length / tablesPerGroup q / 2 * ncOf (certNats q)) ::
        (grpsQ q).flatMap (grpOut · (certNats q))).flatMap natWord) ++ [false] := by
  rw [frame_eq_marksD, gatheredWord_groups, contextWord_nats, ← systemList_length_eq]
  congr 1
  simp only [List.flatMap_append, List.flatMap_cons, grpsQ, List.flatMap_map, List.flatMap_assoc, List.append_assoc]
  congr 3
  exact List.flatMap_congr fun G _ => groupOut_eq q G

end NearQuarticWires.Reconstruct.GatherProg
