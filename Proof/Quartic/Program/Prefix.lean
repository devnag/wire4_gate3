import Proof.Quartic.Program.Stages

/-!
# The algorithm reads only the witness prefix

Paper: the witness, paper/paper.tex (a witness has length `k + (J + 1)(G_1 + G_2)`; missing or
malformed bits are read as zeros), and `prop:time` (the algorithm reads a witness prefix of
polynomial length).

The cell call of a dispatched call depends on the witness word only through the bits (W1)–(W3), i.e. through
`witnessPrefix` (`runCall_witnessPrefix`). Hence every stage of the program after `prep` computes its output from
the word written by `prep`, which contains this prefix and never the rest of the witness.
-/

set_option autoImplicit false

namespace NearQuarticWires.Program

open NearCubicGates.Close.Interfaces

/-- Below the read length, the prefix and the witness word have the same bits. -/
theorem witnessBit_witnessPrefix (c : Call) (p : Cells.Parameters) (w : List Bool) {m : ℕ}
    (hm : m < witnessReadLength c p) :
    Algorithm.witnessBit (witnessPrefix c p w) m = Algorithm.witnessBit w m := by
  unfold witnessPrefix Algorithm.witnessBit
  rw [List.getD_eq_getElem _ _ (by simpa using hm), List.getElem_ofFn]

/-- The witness of `sec:algorithm` is read from its first `k + (J + 1)(G_1 + G_2)` bits. -/
theorem decodeWitness_congr (k J : ℕ) (G : Fin 2 → ℕ) {bits bits' : List Bool}
    (h : ∀ m, m < k + (J + 1) * (G 0 + G 1) → Algorithm.witnessBit bits m = Algorithm.witnessBit bits' m) :
    Algorithm.decodeWitness k J G bits = Algorithm.decodeWitness k J G bits' := by
  unfold Algorithm.decodeWitness
  have hG : G 0 + G 1 ≤ (J + 1) * (G 0 + G 1) := Nat.le_mul_of_pos_left _ (by omega)
  congr 1
  · apply Fin.ext
    simp only
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    rw [h i (by omega)]
  · funext j i
    apply h
    have hi := i.isLt
    fin_cases j
    · simp only [Fin.zero_eta, Fin.isValue, if_true] at hi ⊢; omega
    · simp only [Fin.mk_one, Fin.isValue, one_ne_zero, if_false] at hi ⊢; omega
  · funext j r i
    apply h
    have hi := i.isLt
    have hr := r.isLt
    have hrJ : ((r : ℕ) + 1) * (G 0 + G 1) ≤ J * (G 0 + G 1) := Nat.mul_le_mul_right _ (by omega)
    have hexp : (J + 1) * (G 0 + G 1) = J * (G 0 + G 1) + (G 0 + G 1) := by ring
    have hexp2 : ((r : ℕ) + 1) * (G 0 + G 1) = (r : ℕ) * (G 0 + G 1) + (G 0 + G 1) := by ring
    fin_cases j
    · simp only [Fin.zero_eta, Fin.isValue, if_true] at hi ⊢; omega
    · simp only [Fin.mk_one, Fin.isValue, one_ne_zero, if_false] at hi ⊢; omega

/-- The cell call depends on the witness word only through the decoded witness and the selection `𝒮`. -/
theorem cellCall_congr (c : Call) {p : Cells.Parameters} (hs : Cells.ParameterRules (Builder.callInput c) p)
    {w w' : List Bool} (hwit : Builder.witness c (p := p) w = Builder.witness c (p := p) w')
    (hsel : Builder.selection c (p := p) w = Builder.selection c (p := p) w') :
    Builder.cellCall c hs w = Builder.cellCall c hs w' := by
  unfold Builder.cellCall Builder.columnData Builder.contribution Builder.chainBit Builder.center
    Builder.translation
  rw [hwit, hsel]

/-- **The algorithm reads only the witness prefix** (`sec:algorithm`): the cell call of a dispatched
call at the witness word `w` equals the cell call at its prefix `witnessPrefix`. -/
theorem runCall_witnessPrefix (c : Call) (p : Selected c) (w : List Bool) :
    runCall c p (witnessPrefix c p.1 w) = runCall c p w := by
  have hlen : (Builder.allGates c).length = Builder.occurrences c 0 + Builder.occurrences c 1 := by
    simp [Builder.allGates, Builder.occurrences, Builder.gatesOf]
  have hbit : ∀ m, m < witnessReadLength c p.1 →
      Algorithm.witnessBit (witnessPrefix c p.1 w) m = Algorithm.witnessBit w m :=
    fun m hm => witnessBit_witnessPrefix c p.1 w hm
  unfold runCall
  apply cellCall_congr
  · exact decodeWitness_congr _ _ _ hbit
  · funext i
    unfold Builder.selection
    apply hbit
    have hi : (i : ℕ) < Builder.occurrences c 0 + Builder.occurrences c 1 := hlen ▸ i.isLt
    unfold witnessReadLength
    have : Builder.occurrences c 0 + Builder.occurrences c 1 ≤
        (p.1.J + 1) * (Builder.occurrences c 0 + Builder.occurrences c 1) := Nat.le_mul_of_pos_left _ (by omega)
    omega

end NearQuarticWires.Program
