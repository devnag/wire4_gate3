import Proof.Quartic.StageLift.MaskSize

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open NearCubicGates.Close.Tabulator

/-- `lem:print`, paper/paper.tex: the shared
sum constructor and mask sum constructor have the identical literal AST. -/
theorem formula_sumList_eq (V : ℕ) (fs : List (Formula V)) :
    Formula.sumList fs = Mask.formulaListSum fs := by
  induction fs with
  | nil => rfl
  | cons f fs ih => simp only [Formula.sumList, Mask.formulaListSum, ih]

/-- `lem:print`, paper/paper.tex: the shared
product constructor adds, rather than multiplies, its children's ASTs. -/
theorem formula_prodList_eq (V : ℕ) (fs : List (Formula V)) :
    Formula.prodList fs = Mask.formulaListProd fs := by
  induction fs with
  | nil => rfl
  | cons f fs ih => simp only [Formula.prodList, Mask.formulaListProd, ih]

/-- `lem:print`, paper/paper.tex: the complete
literal sum costs its actual number of children at their syntactic bound. -/
theorem sumList_size_le {V : ℕ} (fs : List (Formula V)) (B : ℕ)
    (h : ∀ f ∈ fs, f.size ≤ B) :
    (Formula.sumList fs).size ≤ fs.length * (B + 1) + 1 := by
  rw [formula_sumList_eq]
  exact formulaListSum_size_le fs B h

/-- `lem:print`, paper/paper.tex: the complete
literal product has additive syntax, independent of expanded coefficients. -/
theorem prodList_size_le {V : ℕ} (fs : List (Formula V)) (B : ℕ)
    (h : ∀ f ∈ fs, f.size ≤ B) :
    (Formula.prodList fs).size ≤ fs.length * (B + 1) + 1 := by
  rw [formula_prodList_eq]
  exact formulaListProd_size_le fs B h

/-- `imp:amp` and `lem:print`, paper/paper.tex: the literal amplifier duplicates its argument only
linearly in e, retaining unary exponent costs in the syntax bound. -/
theorem amp_size_le {V : ℕ} (e : ℕ) (F : Formula V) :
    (Formula.amp e F).size ≤ (e + 1) * (F.size + e + 7) := by
  have hs := sumList_size_le
    ((List.range e).map fun j => Formula.mul
      (.const ((e - 1 + j).choose j : ℤ)) (.pow F j)) (F.size + e + 3) (by
        intro f hf
        obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hf
        have hj' : j < e := List.mem_range.mp hj
        simp only [Formula.size]
        omega)
  simp only [List.length_map, List.length_range] at hs
  simp only [Formula.amp, Formula.size]
  nlinarith

/-- `sec:walks` and `lem:print`, paper/paper.tex: the linear original-pool form has syntax linear in
the occurrence count, regardless of the integer coefficient values. -/
theorem walkFormula_size_le {V m G : ℕ} (weight : Fin G → ℤ)
    (sign : Fin (2 * m) → ℤ) (corners : Fin G → Fin (2 * m) → Fin 4 → Fin V) :
    (Cells.walkFormula weight sign corners).size ≤ G * (20 * m + 2) + 1 := by
  unfold Cells.walkFormula
  apply (sumList_size_le _ (20 * m + 1) ?_).trans
  · simp only [List.length_ofFn]
    exact le_rfl
  · intro f hf
    obtain ⟨g, rfl⟩ := List.mem_ofFn.mp hf
    apply (sumList_size_le _ 9 ?_).trans
    · simp only [List.length_ofFn]
      ring_nf
      exact le_rfl
    · intro F hF
      obtain ⟨edge, rfl⟩ := List.mem_ofFn.mp hF
      simp [Formula.size, Cells.deltaFormula]

end NearQuarticWires.StageLift
