import Proof.Quartic.Reconstruct.TotalProgLink
import Proof.Quartic.Reconstruct.GatherProgCost

/-!
# The sum of the answers: the stage

Paper: Step 3 of `sec:algorithm`, paper/paper.tex, and `prop:time`.

Every number of an answered system has at most `ℓ₀ = 20000 (V+1)^4` bits (`systemTag_length_le`,
`solveWord_length_le_envelope`), and the sums at most `2ℓ₀ + 2E + 4` bits. With the width of the emission stage the
program `totalS` writes `intWord Ψ̃(π)` on `solvedWord` (`totalS_runQ`, `totalWF`), within `totalK B₁ (n+1)^{totalE B₁}`
times the cost `solvedCost` (`totalBudget_le`): **`totalStage`** is the field `ReconstructPhases.total`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearQuarticWires.Reconstruct.TotalProg

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.Cells
open NearCubicGates.Close.Interfaces (listWord bitWord ratWord)
open NearCubicGates.Close.Interfaces.Formats (SolveMachine solveWord SysReq sysWord)
open NearQuarticWires.Greedy NearQuarticWires.Program
open NearQuarticWires.Reconstruct NearQuarticWires.Reconstruct.GatherProg
open NearCubicWires.RepairOrdinary (WordFunction frame)

variable {B1 B2 : ℕ}

/-- The bit bound of the numbers of an answered system. -/
noncomputable def ell0 (q : ChildRequest B1 B2) : ℕ := 20000 * (envelope q + 1) ^ 4

/-- The bit bound of the sum program. -/
noncomputable def ellT (q : ChildRequest B1 B2) : ℕ := 3 * ell0 q + 2 * emitExp q + 10

theorem valOf_mem (d : ItD) : (valOf d).2 = 0 ∨ (valOf d).2 ∈ itN d := by
  unfold valOf
  cases h : d.ans with
  | none => exact Or.inl rfl
  | some L =>
    simp only
    split_ifs with hi
    · right
      rw [List.getD_eq_getElem _ _ hi]
      have hm : L[d.idx].2.1 ∈ L.flatMap entN := List.mem_flatMap.mpr ⟨L[d.idx], List.getElem_mem hi, by simp [entN]⟩
      simp only [itN, h, ansN]
      exact List.mem_append_right _ (List.mem_append_right _ hm)
    · exact Or.inl rfl

theorem item_bits (q : ChildRequest B1 B2) (S : SolveMachine) (x : SystemIndex q) (hx : x ∈ systemList q) :
    ∀ v ∈ itN (itD q S x), natBitLength v ≤ ell0 q := by
  intro v hv
  have h1 := nbl_mem_flatMap _ v hv
  rw [itN_word, List.length_append] at h1
  have h2 := systemTag_length_le q x
  have h3 := solveWord_length_le_envelope S q x hx
  have h4 : envelope q ^ 4 ≤ (envelope q + 1) ^ 4 := Nat.pow_le_pow_left (by omega) 4
  have h5 : 17 * envelope q * (17 * envelope q) ≤ 289 * (envelope q + 1) ^ 4 := by
    have : (envelope q + 1) ^ 2 ≤ (envelope q + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
    nlinarith
  have h6 : 1 ≤ (envelope q + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
  unfold ell0
  omega

theorem itD_lt (q : ChildRequest B1 B2) (S : SolveMachine) (x : SystemIndex q) (hx : x ∈ systemList q) :
    prodOf (itD q S x) ≤ 2 ^ (2 * ell0 q) := by
  have hb := item_bits q S x hx
  have hca : (itD q S x).ca ≤ 2 ^ ell0 q :=
    (lt_natBitLength _).le.trans (Nat.pow_le_pow_right (by norm_num) (hb _ (by simp [itN])))
  have hva : (valOf (itD q S x)).2 ≤ 2 ^ ell0 q := by
    rcases valOf_mem (itD q S x) with h | h
    · rw [h]; exact Nat.zero_le _
    · exact (lt_natBitLength _).le.trans (Nat.pow_le_pow_right (by norm_num) (hb _ h))
  unfold prodOf
  calc (itD q S x).ca * (valOf (itD q S x)).2 ≤ 2 ^ ell0 q * 2 ^ ell0 q := Nat.mul_le_mul hca hva
    _ = 2 ^ (2 * ell0 q) := by rw [← pow_add]; ring_nf

theorem pos_add_neg (d : ItD) : posOf d + negOf d = prodOf d := by
  unfold posOf negOf; split_ifs <;> omega

theorem sum_pos_neg (L : List ItD) : (L.map posOf).sum + (L.map negOf).sum = (L.map prodOf).sum := by
  induction L with
  | nil => rfl
  | cons d L ih => simp only [List.map_cons, List.sum_cons]; have := pos_add_neg d; omega

theorem sum_prod_le (q : ChildRequest B1 B2) (S : SolveMachine) :
    ((itsQ q S).map prodOf).sum ≤ 2 ^ (2 * emitExp q) * 2 ^ (2 * ell0 q) := by
  have h := List.sum_le_card_nsmul ((itsQ q S).map prodOf) (2 ^ (2 * ell0 q)) (by
    intro v hv
    simp only [itsQ, List.map_map, List.mem_map] at hv
    obtain ⟨x, hx, rfl⟩ := hv
    exact itD_lt q S x hx)
  rw [smul_eq_mul, List.length_map, itsQ, List.length_map] at h
  exact h.trans (Nat.mul_le_mul_right _ (systemList_length_lt q).le)

/-- **The run of the sum on a child.** -/
theorem totalS_runQ (q : ChildRequest B1 B2) (S : SolveMachine) (C : Ctx) (hinp : C.inp = solvedWord q S)
    (hW : emitWidth q ≤ C.Wd) :
    Hs C totalS (a0 : DS VV MM) (totalCost (ellT q) (itsQ q S))
      (fun b => b.out = NearCubicGates.Close.Interfaces.intWord (childObjective q)) := by
  have hE := emitExp_le q
  have hWd0 := hW
  unfold emitWidth at hWd0
  have hV4 : (envelope q + 1) ^ 4 ≤ (envelope q + 1) ^ 5 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hV24 : (envelope q + 1) ^ 2 ≤ (envelope q + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hV14 : envelope q + 1 ≤ (envelope q + 1) ^ 4 := by
    calc envelope q + 1 = (envelope q + 1) ^ 1 := (pow_one _).symm
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hEx : emitExp q ≤ 9 * (envelope q + 1) ^ 4 := by
    unfold emitExp
    have : envelope q * (envelope q + 2) ≤ (envelope q + 1) ^ 2 := by nlinarith
    have : 1 ≤ (envelope q + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
    omega
  have hEW : 2 * emitExp q + 2 * ell0 q + 4 ≤ C.Wd := by unfold ell0; omega
  have hℓW : ellT q + 2 ≤ C.Wd := by unfold ellT ell0; omega
  have hsp := sum_prod_le q S
  have hs2 : 2 ^ (2 * emitExp q) * 2 ^ (2 * ell0 q) = 2 ^ (2 * emitExp q + 2 * ell0 q) := by rw [← pow_add]
  have hm := systemList_length_lt q
  have hmb : 2 ^ (2 * emitExp q) ≤ 2 ^ (2 * emitExp q + 2 * ell0 q) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hpn := sum_pos_neg (itsQ q S)
  have h8 : 8 * 2 ^ (2 * emitExp q + 2 * ell0 q) ≤ 2 ^ C.Wd := by
    calc 8 * 2 ^ (2 * emitExp q + 2 * ell0 q) = 2 ^ (2 * emitExp q + 2 * ell0 q + 3) := by rw [pow_add]; ring
      _ ≤ 2 ^ C.Wd := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hlen : (itsQ q S).length = (systemList q).length := by simp [itsQ]
  refine (totalS_run C q.call.n (itsQ q S) (ellT q) (by rw [hinp, solvedWord_nats]) hℓW ?_ ?_ ?_ ?_ ?_).mono le_rfl ?_
  · have := natBitLength_le_succ' q.call.n
    have := n_succ_le_envelope q
    unfold ellT ell0; omega
  · rw [hlen]
    have := natBitLength_le_of_lt_two_pow hm (by unfold emitExp; omega)
    unfold ellT; omega
  · intro d hd v hv
    simp only [itsQ, List.mem_map] at hd
    obtain ⟨x, hx, rfl⟩ := hd
    have := item_bits q S x hx v hv
    unfold ellT; omega
  · rw [hlen, hpn]; omega
  · rw [hpn]
    have hlt : ((itsQ q S).map prodOf).sum < 2 ^ (2 * emitExp q + 2 * ell0 q + 1) := by
      rw [pow_succ]; omega
    have := natBitLength_le_of_lt_two_pow hlt (by omega)
    unfold ellT; omega
  · intro b hb
    rw [hb, childObjective_eq_sums q S]

/-- The budget of the sum stage. -/
noncomputable def totalBudget (B1 : ℕ) (S : SolveMachine) (q : ChildRequest B1 B2) : ℕ :=
  langBudget NearCubicGates.Close.CounterMachine.PrefixProg.noCallee (emitSizes B1) VV MM (solvedWord q S)
    (totalCost (ellT q) (itsQ q S))

theorem leadOnes_solvedWord (q : ChildRequest B1 B2) (S : SolveMachine) :
    leadOnes (solvedWord q S) = natBitLength q.call.n := by
  unfold solvedWord
  exact NearCubicGates.Close.CounterMachine.PrefixProg.leadOnes_natWord _ _

theorem totalWidth_le (q : ChildRequest B1 B2) (S : SolveMachine) :
    emitWidth q ≤ (emitSizes B1).W (leadOnes (solvedWord q S)) := by
  rw [leadOnes_solvedWord, ← leadOnes_gatheredWord]; exact emitWidth_le q

/-- **The sum stage** `solvedWord ↦ intWord Ψ̃(π)` for an exact solver. -/
noncomputable def totalWF (B1 B2 : ℕ) (S : SolveMachine) :
    WordFunction (ChildRequest B1 B2) (fun q => solvedWord q S)
      (fun q => NearCubicGates.Close.Interfaces.intWord (childObjective q)) (totalBudget B1 S) :=
  wordFunction_of_lang (fun q => solvedWord q S) (fun q => NearCubicGates.Close.Interfaces.intWord (childObjective q))
    NearCubicGates.Close.CounterMachine.PrefixProg.noCallee (emitSizes B1) totalS
    (fun q => totalCost (ellT q) (itsQ q S))
    (fun q => by
      obtain ⟨b, n, hex, hn, hb⟩ := totalS_runQ q S
        (ctxOf NearCubicGates.Close.CounterMachine.PrefixProg.noCallee (emitSizes B1) (solvedWord q S)) rfl
        (totalWidth_le q S)
      exact ⟨b, n, hex, hb, hn⟩) (fun q => by
      have := totalWidth_le q S
      unfold emitWidth at this
      omega)

end NearQuarticWires.Reconstruct.TotalProg
