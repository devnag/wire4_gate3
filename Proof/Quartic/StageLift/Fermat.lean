import Proof.Quartic.StageLift.Forms

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open NearCubicGates.Close.Tabulator
open scoped BigOperators

/-- `lem:residue`, paper/paper.tex: canonical
residue-form order, circuit first, score followed by its chain digits. -/
def formIndices (J : ℕ) : List (Fin 2 × Option (Fin (J + 1))) :=
  (List.ofFn fun j : Fin 2 => (j, none) :: List.ofFn fun r : Fin (J + 1) => (j, some r)).flatten

/-- `lem:residue`, paper/paper.tex: the index
stream contains exactly the two score and all two-circuit digit tests. -/
theorem formIndices_length (J : ℕ) : (formIndices J).length = 2 * (J + 2) := by
  simp [formIndices]
  omega

/-- `lem:residue`, paper/paper.tex: the concrete
index order computes the literal product over the original form domain. -/
theorem formIndices_product {R : Type*} [CommMonoid R] (J : ℕ)
    (f : Fin 2 × Option (Fin (J + 1)) → R) :
    ((formIndices J).map f).prod = ∏ i, f i := by
  simp [formIndices, List.map_ofFn, List.prod_ofFn, Fintype.prod_prod_type, Fintype.prod_option]
  simp only [Fin.prod_univ_succ]
  ac_rfl

/-- `lem:residue`, paper/paper.tex: the actual
Fermat conjunction uses the unchanged score and digit Formula codec. -/
def indexedFermatFormula {V J : ℕ} (prime : ℕ)
    (forms : Fin 2 × Option (Fin (J + 1)) → Formula V)
    (rho : Fin 2 × Option (Fin (J + 1)) → ℤ) : Formula V :=
  Formula.prodList ((formIndices J).map fun i =>
    .sub (.const 1) (.pow (.sub (forms i) (.const (rho i))) (prime - 1)))

/-- `lem:residue`, paper/paper.tex: each decoded
test has exactly the integer Fermat-product semantics, for every input. -/
theorem indexedFermatFormula_eval {V J : ℕ} (prime : ℕ)
    (forms : Fin 2 × Option (Fin (J + 1)) → Formula V)
    (rho : Fin 2 × Option (Fin (J + 1)) → ℤ) (β : Fin V → ℤ) :
    (indexedFermatFormula prime forms rho).eval β =
      NearCubicGates.ResidueCounts.fermatProduct prime (fun i => (forms i).eval β) rho := by
  rw [indexedFermatFormula, Formula.eval_prodList, List.map_map]
  exact formIndices_product J (fun i => 1 - ((forms i).eval β - rho i) ^ (prime - 1))

/-- `lem:print`, paper/paper.tex: the conjunction
preserves the literal score-and-digit formal degree budget. -/
theorem indexedFermatFormula_degree {V J : ℕ} (prime : ℕ)
    (forms : Fin 2 × Option (Fin (J + 1)) → Formula V)
    (rho : Fin 2 × Option (Fin (J + 1)) → ℤ)
    (hforms : ∀ i, (forms i).degree ≤ 1) :
    (indexedFermatFormula prime forms rho).degree ≤ 2 * (J + 2) * (prime - 1) := by
  have hprod (fs : List (Formula V)) (D : ℕ) (h : ∀ f ∈ fs, f.degree ≤ D) :
      (Formula.prodList fs).degree ≤ fs.length * D := by
    induction fs with
    | nil => simp [Formula.prodList, Formula.degree]
    | cons f fs ih =>
        change f.degree + (Formula.prodList fs).degree ≤ _
        have hi := ih (fun g hg => h g (by simp [hg]))
        have hf := h f (by simp)
        simp only [List.length_cons]
        nlinarith
  unfold indexedFermatFormula
  apply (hprod _ (prime - 1) ?_).trans
    (by simp only [List.length_map, formIndices_length]; exact le_rfl)
  intro f hf
  obtain ⟨i, _hi, rfl⟩ := List.mem_map.mp hf
  simp only [Formula.degree, zero_max, _root_.max_zero]
  have h := Nat.mul_le_mul_left (prime - 1) (hforms i)
  simpa only [mul_one] using h

end NearQuarticWires.StageLift
