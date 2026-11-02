import Proof.Quartic.Cells.ParametersCertCodec

set_option autoImplicit false

namespace NearQuarticWires.Cells.ParameterArithmetic

open NearCubicGates.Close.Tabulator

/-- `lem:print`, paper/paper.tex: the right-linear
sum's syntactic weight pays each literal carry, without interpreting
that weight as a native coefficient width. -/
theorem cert_sumList_weight_le {V : ℕ} (fs : List (Formula V)) (B : ℕ)
    (h : ∀ f ∈ fs, f.weight ≤ B) :
    (Formula.sumList fs).weight ≤ fs.length * (B + 1) := by
  induction fs with
  | nil => simp [Formula.sumList, Formula.weight]
  | cons f fs ih =>
    have hf := h f (by simp)
    have ht := ih (fun g hg => h g (by simp [hg]))
    have hm : max f.weight (Formula.sumList fs).weight ≤ B + fs.length * (B + 1) :=
      max_le (hf.trans (Nat.le_add_right _ _)) (ht.trans (Nat.le_add_left _ _))
    simp only [Formula.sumList, Formula.weight, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-- `lem:print`, paper/paper.tex: multiplication
adds the syntactic child weights, including the empty product's one. -/
theorem cert_prodList_weight_le {V : ℕ} (fs : List (Formula V)) (B : ℕ)
    (h : ∀ f ∈ fs, f.weight ≤ B) :
    (Formula.prodList fs).weight ≤ fs.length * B + 1 := by
  induction fs with
  | nil => simp [Formula.prodList, Formula.weight]
  | cons f fs ih =>
    have hf := h f (by simp)
    have ht := ih (fun g hg => h g (by simp [hg]))
    simp only [Formula.prodList, Formula.weight, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-- `lem:maskpoly` and `lem:print`, paper/paper.tex: the original finite subset sum pays all its actual carries. -/
theorem cert_formulaSum_weight_le {ι : Type*} {V : ℕ} (s : Finset ι)
    (f : ι → Formula V) (B : ℕ) (h : ∀ i ∈ s, (f i).weight ≤ B) :
    (Mask.formulaSum s f).weight ≤ s.card * (B + 1) := by
  classical
  unfold Mask.formulaSum
  rw [← StageLift.formula_sumList_eq]
  apply (cert_sumList_weight_le _ B ?_).trans
  · simp
  · intro F hF
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hF
    exact h i (by simpa using hi)

/-- `lem:maskpoly` and `lem:print`, paper/paper.tex: the original finite subset product has additive weight. -/
theorem cert_formulaProd_weight_le {ι : Type*} {V : ℕ} (s : Finset ι)
    (f : ι → Formula V) (B : ℕ) (h : ∀ i ∈ s, (f i).weight ≤ B) :
    (Mask.formulaProd s f).weight ≤ s.card * B + 1 := by
  classical
  unfold Mask.formulaProd
  rw [← StageLift.formula_prodList_eq]
  apply (cert_prodList_weight_le _ B ?_).trans
  · simp
  · intro F hF
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hF
    exact h i (by simpa using hi)

/-- `lem:maskpoly`, paper/paper.tex: each actual
Newton leaf has at most one more bit than its difference order. -/
theorem cert_newton_coefficient_bits (tau a : ℕ) :
    Nat.size (Mask.newtonCoeff tau a).natAbs ≤ a + 1 := by
  have h := Mask.newtonCoeff_abs_le tau a
  rw [← Int.natCast_natAbs] at h
  have hn : (Mask.newtonCoeff tau a).natAbs ≤ 2 ^ a := by exact_mod_cast h
  exact Nat.size_le.mpr (hn.trans_lt (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self a)))

/-- `lem:maskpoly` and `lem:print`, paper/paper.tex: the literal mask weight retains its full subset count,
while its fixed factors are explicit rather than hidden. -/
theorem cert_mask_formula_weight_le {G V : ℕ} (structural : Bool)
    (b : Fin G → Formula V) (tau X B : ℕ) (hb : ∀ i, (b i).weight ≤ B) :
    (Mask.maskFormula structural b tau X).weight ≤
      1 + (X + 1) * (X + 2 + (G + 1) ^ X * (X * B + 2)) := by
  classical
  have hinner (a : ℕ) (ha : a ≤ X) :
      (Mask.formulaSum (Finset.univ.powersetCard a)
        (fun s => Mask.formulaProd s b)).weight ≤ (G + 1) ^ X * (X * B + 2) := by
    have hs := cert_formulaSum_weight_le (Finset.univ.powersetCard a)
      (fun s => Mask.formulaProd s b) (X * B + 1) (by
        intro s hs
        have hp := cert_formulaProd_weight_le s b B (fun i _ => hb i)
        rw [(Finset.mem_powersetCard.mp hs).2] at hp
        exact hp.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ ha) _))
    have hc : (Finset.univ.powersetCard a : Finset (Finset (Fin G))).card ≤ (G + 1) ^ X := by
      rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
      exact (Nat.choose_le_pow _ _).trans
        ((Nat.pow_le_pow_left (Nat.le_succ G) a).trans
          (Nat.pow_le_pow_right (Nat.succ_pos G) ha))
    exact hs.trans (by simpa only [Nat.add_assoc] using Nat.mul_le_mul_right (X * B + 2) hc)
  have hs := cert_formulaSum_weight_le (Finset.range (X + 1))
    (fun a => Formula.mul (.const (Mask.newtonCoeff tau a))
      (Mask.formulaSum (Finset.univ.powersetCard a) (fun s => Mask.formulaProd s b)))
    (X + 1 + (G + 1) ^ X * (X * B + 2)) (by
      intro a ha
      have haX : a ≤ X := by simpa using ha
      have hn := (cert_newton_coefficient_bits tau a).trans (Nat.add_le_add_right haX 1)
      have hi := hinner a haX
      simpa only [Formula.weight] using Nat.add_le_add hn hi)
  simp only [Finset.card_range] at hs
  have he : (X + 1) * (X + 1 + (G + 1) ^ X * (X * B + 2) + 1) =
      (X + 1) * (X + 2 + (G + 1) ^ X * (X * B + 2)) := by ring
  rw [he] at hs
  have hf : Nat.size (if structural then (1 : ℤ) else 0).natAbs ≤ 1 := by
    cases structural <;> decide
  change Nat.size (if structural then (1 : ℤ) else 0).natAbs + _ ≤ _
  omega

/-- `sec:cells` and `lem:print`, paper/paper.tex: a residual square has syntactic weight at most eight. -/
theorem cert_selected_square_weight_le {m G : ℕ} (hm : 0 < m)
    (selection : Fin G → Bool) (e : Fin (2 * m)) (g : Fin G) :
    (StagePrint.selectedSquare hm selection e g).weight ≤ 8 := by
  unfold StagePrint.selectedSquare
  split <;> simp [Formula.weight, edgeFormula, deltaFormula]

/-- `lem:print`, paper/paper.tex: the actual selected
mask's syntax weight grows with its construction count, not its native field. -/
theorem cert_selected_mask_weight_le {m G : ℕ} (hm : 0 < m)
    (selection : Fin G → Bool) (structural : Bool) (e : Fin (2 * m)) (tau X : ℕ) :
    (StagePrint.selectedMaskFormula hm selection structural e tau X).weight ≤
      1 + (X + 1) * (X + 2 + (G + 1) ^ X * (8 * X + 2)) := by
  simpa only [StagePrint.selectedMaskFormula, Nat.mul_comm X 8] using
    cert_mask_formula_weight_le structural (StagePrint.selectedSquare hm selection e) tau X 8
      (cert_selected_square_weight_le hm selection e)

/-- `sec:walks` and `lem:print`, paper/paper.tex: the literal linear walk syntax has a polynomial
weight once its actual integer leaf bits are bounded. -/
theorem cert_pooled_walk_weight_le {m G : ℕ} (hm : 0 < m)
    (weight : Fin G → ℤ) (sign : Fin (2 * m) → ℤ) (L : ℕ)
    (hw : ∀ g, Nat.size (weight g).natAbs ≤ L)
    (hs : ∀ e, (sign e).natAbs ≤ 1) :
    (pooledWalkFormula hm weight sign).weight ≤ G * (2 * m * (L + 5) + 1) := by
  unfold pooledWalkFormula walkFormula
  apply (cert_sumList_weight_le _ (2 * m * (L + 5)) ?_).trans
  · simp
  · intro F hF
    obtain ⟨g, rfl⟩ := List.mem_ofFn.mp hF
    apply (cert_sumList_weight_le _ (L + 4) ?_).trans
    · simp
    · intro f hf
      obtain ⟨e, rfl⟩ := List.mem_ofFn.mp hf
      have hp : (weight g * sign e).natAbs ≤ (weight g).natAbs := by
        simp only [Int.natAbs_mul]
        simpa only [mul_one] using Nat.mul_le_mul_left (weight g).natAbs (hs e)
      have hb : Nat.size (weight g * sign e).natAbs ≤ L :=
        Nat.size_le.mpr (hp.trans_lt (Nat.size_le.mp (hw g)))
      simp only [Formula.weight, deltaFormula]
      omega

end NearQuarticWires.Cells.ParameterArithmetic
