import Proof.Quartic.Reconstruct.PrintRun2
import Proof.Quartic.StageMain.CallSize
import Proof.Quartic.Cells.ParametersPrepWord

/-!
# The width of the printing stage

Paper: Step 3 of `sec:algorithm`, paper/paper.tex, and `prop:time`.

`printWidth q = |prepWord| + 4 (V+1)^3 + 64` (`V` the envelope of the child) covers every value of the printing stage:
`preBounds_of_le`, `postBounds_of_le`. The number of tables is at most `512 P^{2J+5} < 2^{V(2V+5)+10}`
(`cntOf_le`); the word after parameter preparation has polynomial length (`prepWord_le`).
-/

set_option autoImplicit false

namespace NearQuarticWires.Reconstruct

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.Cells
open NearCubicGates.Close.Interfaces (listWord bitWord kindTag callWord)
open NearCubicWires.RepairOrdinary (frame)
open NearQuarticWires.Greedy NearQuarticWires.Program

variable {B1 B2 : ℕ}

/-- The exponent of the bound on the word after parameter preparation. -/
def prepE (B1 B2 : ℕ) : ℕ := (B2 + 8) * (B1 + 12)

/-- The constant of the bound on the word after parameter preparation. -/
noncomputable def prepC (B1 : ℕ) : ℕ :=
  200 * (Cells.ParameterArithmetic.preparationCoefficient B1 + 5) * 1002 ^ (B1 + 12) + 1

/-- **The word after parameter preparation has polynomial length** (`prop:time`). -/
theorem prepWord_le (q : ChildRequest B1 B2) :
    (prepWord B1 B2 q.call q.witness).length + 1 ≤ prepC B1 * (q.call.n + 1) ^ prepE B1 B2 := by
  have h1 := Cells.dispatched_prepWord_length q.dispatched q.witness
  have h2 := StageMain.CallSize.dispatched_callWord_polynomial q.dispatched
  set c := Cells.ParameterArithmetic.preparationCoefficient B1
  set m := (q.call.n + 1) ^ (B2 + 8) with hm
  set X := (q.call.n + 1) ^ prepE B1 B2 with hX
  have hm1 : 1 ≤ m := Nat.one_le_pow _ _ (by omega)
  have h3 : (callWord q.call).length + 1 ≤ 1002 * m := by omega
  have h4 : ((callWord q.call).length + 1) ^ (B1 + 12) ≤ 1002 ^ (B1 + 12) * X := by
    calc _ ≤ (1002 * m) ^ (B1 + 12) := Nat.pow_le_pow_left h3 _
      _ = _ := by rw [mul_pow, hm, ← pow_mul]; rfl
  have h5 := Nat.mul_le_mul_left (200 * (c + 5)) h4
  have hX1 : 1 ≤ X := Nat.one_le_pow _ _ (by omega)
  have e : (200 * (c + 5) * 1002 ^ (B1 + 12) + 1) * X = 200 * (c + 5) * (1002 ^ (B1 + 12) * X) + X := by ring
  unfold prepC
  rw [e]
  omega

/-- The width of the printing stage. -/
noncomputable def printWidth (q : ChildRequest B1 B2) : ℕ :=
  (prepWord B1 B2 q.call q.witness).length + 4 * (envelope q + 1) ^ 3 + 64

theorem length_primes_le (q : ChildRequest B1 B2) :
    (q.selected.1.primes.sort (· ≤ ·)).length ≤ q.selected.1.P := by
  rw [Finset.length_sort]; exact card_primes_le q

theorem le_P_of_mem_sort (q : ChildRequest B1 B2) {p : ℕ} (hp : p ∈ q.selected.1.primes.sort (· ≤ ·)) :
    p ≤ q.selected.1.P :=
  le_P_of_mem_primes q ((Finset.mem_sort _).mp hp)

theorem tgOf_le (q : ChildRequest B1 B2) : tgOf q ≤ q.selected.1.P ^ 3 := by
  have h : ∀ x ∈ (q.selected.1.primes.sort (· ≤ ·)).map (groupSize (pairBit q)), x ≤ q.selected.1.P ^ 2 := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    have := le_P_of_mem_sort q hp
    unfold groupSize
    split
    · rw [sq]; exact Nat.mul_le_mul this this
    · nlinarith
  have hs := List.sum_le_card_nsmul _ _ h
  rw [List.length_map, smul_eq_mul] at hs
  have hl := length_primes_le q
  calc tgOf q ≤ _ := hs
    _ ≤ q.selected.1.P * q.selected.1.P ^ 2 := Nat.mul_le_mul_right _ hl
    _ = _ := by ring

theorem baseOf_le (q : ChildRequest B1 B2) : baseOf q ≤ q.selected.1.P := by
  have := hE_mul_four_le q; unfold baseOf; omega

theorem one_le_baseOf (q : ChildRequest B1 B2) : 1 ≤ baseOf q := by
  have := one_le_hE q; unfold baseOf; omega

theorem a1Of_le (q : ChildRequest B1 B2) : a1Of q ≤ q.selected.1.P ^ (q.cellCall.J + 1) := by
  have hP := one_le_P q
  unfold a1Of
  split
  · exact Nat.pow_le_pow_left (baseOf_le q) _
  · exact Nat.one_le_pow _ _ hP

theorem one_le_a1Of (q : ChildRequest B1 B2) : 1 ≤ a1Of q := by
  unfold a1Of; split
  · exact Nat.one_le_pow _ _ (one_le_baseOf q)
  · exact le_rfl

/-- The bound `512 P^{2J+5}` on the counts of the printing stage. -/
noncomputable def bigOf (q : ChildRequest B1 B2) : ℕ := 512 * q.selected.1.P ^ (2 * q.cellCall.J + 5)

theorem cntOf_le (q : ChildRequest B1 B2) :
    baseOf q ^ q.cellCall.J ≤ bigOf q ∧ 512 * baseOf q ^ (q.cellCall.J + 1) ≤ bigOf q ∧
      512 * baseOf q ^ (q.cellCall.J + 1) * a1Of q ≤ bigOf q ∧ cntOf q ≤ bigOf q ∧ a1Of q ≤ bigOf q := by
  set P := q.selected.1.P
  set J := q.cellCall.J
  have hP := one_le_P q
  have hB := baseOf_le q
  have hA0 : baseOf q ^ (J + 1) ≤ P ^ (J + 1) := Nat.pow_le_pow_left hB _
  have hA1 : a1Of q ≤ P ^ (J + 1) := a1Of_le q
  have hT : tgOf q ≤ P ^ 3 := tgOf_le q
  have hJ : baseOf q ^ J ≤ P ^ (J + 1) :=
    (Nat.pow_le_pow_left hB _).trans (Nat.pow_le_pow_right hP (by omega))
  have hp1 : 1 ≤ P ^ (J + 1) := Nat.one_le_pow _ _ hP
  have hp3 : 1 ≤ P ^ 3 := Nat.one_le_pow _ _ hP
  have e : P ^ (2 * J + 5) = P ^ (J + 1) * P ^ (J + 1) * P ^ 3 := by rw [← pow_add, ← pow_add]; ring_nf
  have hpp : P ^ (J + 1) ≤ P ^ (2 * J + 5) := by rw [e]; nlinarith
  have hcnt : cntOf q ≤ 512 * (P ^ (J + 1) * P ^ (J + 1) * P ^ 3) := by
    unfold cntOf
    have := Nat.mul_le_mul (Nat.mul_le_mul hA0 hA1) hT
    calc 512 * baseOf q ^ (J + 1) * a1Of q * tgOf q = 512 * (baseOf q ^ (J + 1) * a1Of q * tgOf q) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ this
  have h2 : 512 * baseOf q ^ (J + 1) * a1Of q ≤ 512 * (P ^ (J + 1) * P ^ (J + 1) * P ^ 3) := by
    have := Nat.mul_le_mul (Nat.mul_le_mul hA0 hA1) hp3
    calc 512 * baseOf q ^ (J + 1) * a1Of q = 512 * (baseOf q ^ (J + 1) * a1Of q * 1) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ this
  unfold bigOf
  rw [e]
  rw [e] at hpp
  refine ⟨by omega, by omega, h2, hcnt, by omega⟩

theorem bigOf_lt (q : ChildRequest B1 B2) :
    bigOf q < 2 ^ (envelope q * (2 * envelope q + 5) + 10) := by
  set V := envelope q
  have hPV := P_le_envelope q
  have hJV : q.cellCall.J ≤ V := (child_le q).2.2.2.2.2.1
  have h1 : q.selected.1.P ^ (2 * q.cellCall.J + 5) ≤ (V + 1) ^ (2 * V + 5) :=
    (Nat.pow_le_pow_left (by omega) _).trans (Nat.pow_le_pow_right (by omega) (by omega))
  have h2 := succ_pow_le_two_pow V (2 * V + 5)
  have e : 2 ^ (V * (2 * V + 5) + 10) = 1024 * 2 ^ (V * (2 * V + 5)) := by rw [pow_add]; ring
  have h3 : 1 ≤ 2 ^ (V * (2 * V + 5)) := Nat.one_le_two_pow
  unfold bigOf
  rw [e]
  omega

theorem lt_two_pow_of_lt_W {v W : ℕ} (h : v < W) : v < 2 ^ W := h.trans Nat.lt_two_pow_self

theorem env_cube (V : ℕ) : V * (2 * V + 5) + 10 + 3 ≤ 4 * (V + 1) ^ 3 + 61 := by
  have e1 : V * (2 * V + 5) = 2 * V ^ 2 + 5 * V := by ring
  have e2 : (V + 1) ^ 3 = V ^ 3 + 3 * V ^ 2 + 3 * V + 1 := by ring
  omega

/-- **The bounds of the input and the context part.** -/
theorem preBounds_of_le (q : ChildRequest B1 B2) (W : ℕ) (hW : printWidth q ≤ W) : PreBounds q W := by
  unfold printWidth at hW
  set V := envelope q with hV
  obtain ⟨hM, hA, hL, hE, hn, hJ, hG⟩ := child_le q
  have hPV := P_le_envelope q
  have hT := tgOf_le q
  have hl := length_primes_le q
  have hP3 : q.selected.1.P ^ 3 ≤ V ^ 3 := Nat.pow_le_pow_left hPV 3
  have hV3 : V ^ 3 + 3 * V + 1 ≤ (V + 1) ^ 3 := by nlinarith
  have hsplit := congrArg List.length (prepWord_split q)
  simp only [List.length_cons, List.length_append, RepairOrdinary.frame_length] at hsplit
  have hnb : ∀ v, v + 4 ≤ W → natBitLength v ≤ W - 3 := fun v hv =>
    (natBitLength_le_succ' v).trans (by omega)
  refine ⟨by omega, lt_two_pow_of_lt_W (by omega), Nat.pow_lt_pow_right (by norm_num) (by omega),
    lt_two_pow_of_lt_W (by omega), fun p hp => lt_two_pow_of_lt_W ?_, lt_two_pow_of_lt_W (by omega), ?_, by omega⟩
  · have := le_P_of_mem_sort q hp
    have : p * p ≤ V ^ 3 := by nlinarith
    omega
  · intro v hv
    simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hv
    have hG0 := hG 0
    have hG1 := hG 1
    rcases hv with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | hf
    · exact hnb _ (by omega)
    · exact hnb _ (by omega)
    · exact hnb _ (by omega)
    · exact hnb _ (by omega)
    · exact hnb _ (by omega)
    · exact hnb _ (by split <;> omega)
    · exact hnb _ (by omega)
    · exact hnb _ (by omega)
    · rw [ncol_eq]
      exact (natBitLength_le_of_lt_two_pow (Nat.pow_lt_pow_right (by norm_num) (show q.call.n - q.selected.1.k <
        q.call.n + 1 by omega)) (by omega)).trans (by omega)
    · exact hnb _ (by omega)
    · have := Cells.ParameterRules.factor_member_preparation_bound (rules q) v hf
      exact hnb _ (by change v ≤ q.call.n at this; omega)

/-- **The bounds of the tables part.** -/
theorem postBounds_of_le (q : ChildRequest B1 B2) (W : ℕ) (hW : printWidth q ≤ W) : PostBounds q W := by
  unfold printWidth at hW
  set V := envelope q with hV
  obtain ⟨hM, hA, hL, hE, hn, hJ, hG⟩ := child_le q
  have hPV := P_le_envelope q
  have hV3 : V * (2 * V + 5) + 10 + 3 ≤ 4 * (V + 1) ^ 3 + 61 := env_cube V
  have hV1 : V + 1 ≤ (V + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
  obtain ⟨b1, b2, b3, b4, b5⟩ := cntOf_le q
  have hbig : bigOf q < 2 ^ (V * (2 * V + 5) + 10) := bigOf_lt q
  have hEW : 2 ^ (V * (2 * V + 5) + 10) ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hnb : ∀ v, v + 4 ≤ W → natBitLength v ≤ W - 3 := fun v hv =>
    (natBitLength_le_succ' v).trans (by omega)
  have hBP := baseOf_le q
  have h512 : 512 < 2 ^ W := lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (show 0 < 2 by norm_num)
    (show 10 ≤ W by omega))
  have hcb : natBitLength (cntOf q) ≤ V * (2 * V + 5) + 10 :=
    natBitLength_le_of_lt_two_pow (lt_of_le_of_lt b4 hbig) (by omega)
  refine ⟨lt_two_pow_of_lt_W (by omega), h512, lt_two_pow_of_lt_W (by omega), by omega, by omega, by omega, by omega,
    lt_two_pow_of_lt_W (by omega), by omega, lt_two_pow_of_lt_W (by omega), ?_, hnb _ (by omega), hnb _ (by omega)⟩
  intro v hv
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl
  · exact hnb _ (by omega)
  · exact hnb _ (by omega)
  · exact hnb _ (by omega)
  · exact hnb _ (by omega)
  · exact hnb _ (by split <;> omega)

end NearQuarticWires.Reconstruct
