import Proof.Quartic.StagePrint.SelectedFormulas

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open scoped BigOperators
open NearCubicGates.Close.Tabulator

/-- `lem:maskpoly` and `lem:print`, paper/paper.tex: a literal finite sum adds the syntactic sizes of its
children and one operator for each summand. -/
theorem formulaListSum_size_le {V : ℕ} (fs : List (Formula V)) (B : ℕ)
    (h : ∀ f ∈ fs, f.size ≤ B) :
    (Mask.formulaListSum fs).size ≤ fs.length * (B + 1) + 1 := by
  induction fs with
  | nil => simp [Mask.formulaListSum, Formula.size]
  | cons f fs ih =>
      have hh := h f (by simp)
      have ht := ih (fun g hg => h g (by simp [hg]))
      simp only [Mask.formulaListSum, Formula.size, List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

/-- `lem:maskpoly` and `lem:print`, paper/paper.tex: multiplying formulas adds their syntactic sizes,
independently of the number of monomials in their eventual product. -/
theorem formulaListProd_size_le {V : ℕ} (fs : List (Formula V)) (B : ℕ)
    (h : ∀ f ∈ fs, f.size ≤ B) :
    (Mask.formulaListProd fs).size ≤ fs.length * (B + 1) + 1 := by
  induction fs with
  | nil => simp [Mask.formulaListProd, Formula.size]
  | cons f fs ih =>
      have hh := h f (by simp)
      have ht := ih (fun g hg => h g (by simp [hg]))
      simp only [Mask.formulaListProd, Formula.size, List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

/-- `lem:maskpoly`, paper/paper.tex: each actual
size-a subset product has linear syntactic construction cost in a. -/
theorem formulaProd_size_le {ι : Type*} {V : ℕ} (s : Finset ι)
    (f : ι → Formula V) (B : ℕ) (h : ∀ i ∈ s, (f i).size ≤ B) :
    (Mask.formulaProd s f).size ≤ s.card * (B + 1) + 1 := by
  classical
  unfold Mask.formulaProd
  apply (formulaListProd_size_le _ B ?_).trans
  · simp
  · intro g hg
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hg
    exact h i (by simpa using hi)

/-- `lem:maskpoly`, paper/paper.tex: a literal
subset sum pays its actual cardinality rather than an assumed small size. -/
theorem formulaSum_size_le {ι : Type*} {V : ℕ} (s : Finset ι)
    (f : ι → Formula V) (B : ℕ) (h : ∀ i ∈ s, (f i).size ≤ B) :
    (Mask.formulaSum s f).size ≤ s.card * (B + 1) + 1 := by
  classical
  unfold Mask.formulaSum
  apply (formulaListSum_size_le _ B ?_).trans
  · simp
  · intro g hg
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hg
    exact h i (by simpa using hi)

/-- `lem:maskpoly` and `lem:print`, paper/paper.tex: the original literal mask retains its complete subset
construction cost, including unary syntactic exponent contributions. -/
theorem maskFormula_size_le {ι : Type*} [Fintype ι] {V : ℕ}
    (structural : Bool) (b : ι → Formula V) (tau Xmax B : ℕ)
    (hb : ∀ i, (b i).size ≤ B) :
    (Mask.maskFormula structural b tau Xmax).size ≤
      (Xmax + 1) * ((Fintype.card ι + 1) ^ Xmax * (Xmax * (B + 1) + 2) + 4) + 3 := by
  classical
  have hp (a : ℕ) (ha : a ≤ Xmax) :
      (Finset.univ.powersetCard a : Finset (Finset ι)).card ≤
        (Fintype.card ι + 1) ^ Xmax := by
    rw [Finset.card_powersetCard]
    exact (Nat.choose_le_pow _ _).trans
      ((Nat.pow_le_pow_left (by omega : Fintype.card ι ≤ Fintype.card ι + 1) a).trans
        (Nat.pow_le_pow_right (by omega) ha))
  have inner (a : ℕ) (ha : a ≤ Xmax) :
      (Mask.formulaSum (Finset.univ.powersetCard a)
        (fun s => Mask.formulaProd s b)).size ≤
          (Fintype.card ι + 1) ^ Xmax * (Xmax * (B + 1) + 2) + 1 := by
    refine (formulaSum_size_le _ _ (Xmax * (B + 1) + 1) ?_).trans ?_
    · intro s hs
      have hs' := (Finset.mem_powersetCard.mp hs).2
      refine (formulaProd_size_le s b B (fun i _ => hb i)).trans ?_
      rw [hs']
      exact Nat.add_le_add_right (Nat.mul_le_mul_right _ ha) _
    · exact Nat.add_le_add_right (Nat.mul_le_mul_right _ (hp a ha)) _
  have hs := formulaSum_size_le (Finset.range (Xmax + 1))
    (fun a => Formula.mul (.const (Mask.newtonCoeff tau a))
      (Mask.formulaSum (Finset.univ.powersetCard a) (fun s => Mask.formulaProd s b)))
    ((Fintype.card ι + 1) ^ Xmax * (Xmax * (B + 1) + 2) + 3) (by
      intro a ha
      have hh := inner a (by simpa using ha)
      simp only [Formula.size]
      omega)
  simp only [Finset.card_range] at hs
  simp only [Mask.maskFormula, Formula.size]
  convert Nat.add_le_add_left hs 2 using 1 <;> ring

/-- `lem:print`, paper/paper.tex: the actual
mixed-residual square has unary-exponent syntactic size at most ten. -/
theorem selectedSquare_size_le {m G : ℕ} (hm : 0 < m) (selection : Fin G → Bool)
    (edge : Fin (2 * m)) (g : Fin G) :
    (StagePrint.selectedSquare hm selection edge g).size ≤ 10 := by
  unfold StagePrint.selectedSquare
  split <;> simp [Formula.size, Cells.edgeFormula, Cells.deltaFormula]

/-- `lem:maskpoly` and `lem:print`, paper/paper.tex: this is the complete original mask Formula.size bound;
the exponent (G+1)^Xmax is retained in the physical construction ledger. -/
theorem selectedMask_size_le {m G : ℕ} (hm : 0 < m) (selection : Fin G → Bool)
    (structural : Bool) (edge : Fin (2 * m)) (tau Xmax : ℕ) :
    (StagePrint.selectedMaskFormula hm selection structural edge tau Xmax).size ≤
      (Xmax + 1) * ((G + 1) ^ Xmax * (11 * Xmax + 2) + 4) + 3 := by
  simpa only [StagePrint.selectedMaskFormula, Fintype.card_fin, Nat.mul_comm Xmax 11] using
    maskFormula_size_le structural (StagePrint.selectedSquare hm selection edge) tau Xmax 10
      (selectedSquare_size_le hm selection edge)

end NearQuarticWires.StageLift
