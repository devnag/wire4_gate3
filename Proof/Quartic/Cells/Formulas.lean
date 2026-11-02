import Proof.Quartic.Cells.Score
import Proof.Gates.Tabulator.Formula

set_option autoImplicit false

namespace NearQuarticWires.Cells
open NearCubicWires Finset
open NearCubicWires.WireExponent3_5.Shared
open NearCubicGates.Close.Tabulator

/-- `sec:cells`, paper/paper.tex, and `lem:print`:
the residual is an integer linear formula in its four threshold atoms. -/
def deltaFormula {V : ℕ} (corners : Fin 4 → Fin V) : Formula V :=
  .add (.sub (.sub (.var (corners 0)) (.var (corners 1))) (.var (corners 2))) (.var (corners 3))

/-- `sec:cells`, paper/paper.tex: the population indicator is the square of that integer formula. -/
def residualIndicatorFormula {V : ℕ} (corners : Fin 4 → Fin V) : Formula V :=
  .pow (deltaFormula corners) 2

/-- `lem:print`, paper/paper.tex: exact linear degree of a mixed residual. -/
theorem deltaFormula_degree {V : ℕ} (corners : Fin 4 → Fin V) : (deltaFormula corners).degree = 1 := rfl

/-- `lem:print`, paper/paper.tex: exact quadratic degree of an occurrence's population indicator. -/
theorem residualIndicatorFormula_degree {V : ℕ} (corners : Fin 4 → Fin V) :
    (residualIndicatorFormula corners).degree = 2 := rfl

/-- `sec:cells`, paper/paper.tex: evaluation is the literal integer four-corner difference. -/
theorem deltaFormula_eval {V : ℕ} (corners : Fin 4 → Fin V) (β : Fin V → ℤ) :
    (deltaFormula corners).eval β = β (corners 0) - β (corners 1) - β (corners 2) + β (corners 3) := rfl

/-- `lem:print`, paper/paper.tex: the residual formula evaluates to the actual star residual. -/
theorem deltaFormula_eval_star {V : ℕ} (P : StarParams) (g : NormalizedThresholdGate P.n)
    (c : BitInput P.n) (u v : P.Errors) (corners : Fin 4 → Fin V) (β : Fin V → Bool)
    (hβ : ∀ j, β (corners j) = NearCubicWires.WireExponent3_5.Stars.corners g.eval c
      (P.errorVector P.leftBlock u) (P.errorVector P.rightBlock v) j) :
    (deltaFormula corners).eval (boolPoint β) = delta P g c u v := by
  simp only [deltaFormula_eval, boolPoint, hβ]
  rfl

/-- `sec:cells`, paper/paper.tex: the quadratic formula is exactly the nonzero-residual indicator. -/
theorem residualIndicatorFormula_eval_star {V : ℕ} (P : StarParams) (g : NormalizedThresholdGate P.n)
    (c : BitInput P.n) (u v : P.Errors) (corners : Fin 4 → Fin V) (β : Fin V → Bool)
    (hβ : ∀ j, β (corners j) = NearCubicWires.WireExponent3_5.Stars.corners g.eval c
      (P.errorVector P.leftBlock u) (P.errorVector P.rightBlock v) j) :
    (residualIndicatorFormula corners).eval (boolPoint β) = if delta P g c u v ≠ 0 then 1 else 0 := by
  change (deltaFormula corners).eval (boolPoint β) ^ 2 = _
  rw [deltaFormula_eval_star P g c u v corners β hβ, ← delta_abs_eq_sq]
  have h := delta_range P g c u v
  simp only [Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with h | h | h <;> simp [h]

/-- `sec:walks`, paper/paper.tex: a sampled or signed linear combination of edge residuals. -/
def walkFormula {V m G : ℕ} (weight : Fin G → ℤ) (sign : Fin (2 * m) → ℤ)
    (corners : Fin G → Fin (2 * m) → Fin 4 → Fin V) : Formula V :=
  Formula.sumList (List.ofFn fun i => Formula.sumList (List.ofFn fun e =>
    Formula.mul (.const (weight i * sign e)) (deltaFormula (corners i e))))

/-- `lem:print`, paper/paper.tex: all sampled walk sums remain linear in threshold atoms. -/
theorem walkFormula_degree {V m G : ℕ} (weight : Fin G → ℤ) (sign : Fin (2 * m) → ℤ)
    (corners : Fin G → Fin (2 * m) → Fin 4 → Fin V) :
    (walkFormula weight sign corners).degree ≤ 1 := by
  apply Formula.degree_sumList_le
  intro f hf
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hf
  apply Formula.degree_sumList_le
  intro f hf
  obtain ⟨e, rfl⟩ := List.mem_ofFn.mp hf
  simp [Formula.degree, deltaFormula_degree]

/-- `sec:walks`, paper/paper.tex: exact signed integer evaluation, including repeated occurrences. -/
theorem walkFormula_eval {V m G : ℕ} (weight : Fin G → ℤ) (sign : Fin (2 * m) → ℤ)
    (corners : Fin G → Fin (2 * m) → Fin 4 → Fin V) (β : Fin V → ℤ) :
    (walkFormula weight sign corners).eval β =
      ∑ i, ∑ e, weight i * sign e *
        (β (corners i e 0) - β (corners i e 1) - β (corners i e 2) + β (corners i e 3)) := by
  simp [walkFormula, Formula.eval_sumList, List.map_ofFn, List.sum_ofFn, Formula.eval, deltaFormula]

/-- `lem:print`, paper/paper.tex: multiply the exact masks on the 2m edges. -/
def walkMaskFormula {V m : ℕ} (masks : Fin (2 * m) → Formula V) : Formula V :=
  Formula.prodList (List.ofFn masks)

/-- `lem:print`, paper/paper.tex: the 2m quadratic masks contribute degree at most 4m Xmax. -/
theorem walkMaskFormula_degree {V m Xmax : ℕ} (masks : Fin (2 * m) → Formula V)
    (h : ∀ e, (masks e).degree ≤ 2 * Xmax) :
    (walkMaskFormula masks).degree ≤ 4 * m * Xmax := by
  refine (Formula.degree_prodList_le _).trans ?_
  simp only [List.map_ofFn, List.sum_ofFn]
  calc ∑ e, (masks e).degree ≤ ∑ _e : Fin (2 * m), 2 * Xmax := Finset.sum_le_sum fun e _ => h e
    _ = _ := by simp; ring

/-- `lem:residue`, paper/paper.tex: the literal Fermat conjunction for integer linear forms. -/
def fermatFormula {V d : ℕ} (p : ℕ) (forms : Fin d → Formula V) (rho : Fin d → ℤ) : Formula V :=
  Formula.prodList (List.ofFn fun i => .sub (.const 1) (.pow (.sub (forms i) (.const (rho i))) (p - 1)))

/-- `lem:print`, paper/paper.tex: the Fermat conjunction's degree counts every digit and score form. -/
theorem fermatFormula_degree {V d : ℕ} (p : ℕ) (forms : Fin d → Formula V) (rho : Fin d → ℤ)
    (h : ∀ i, (forms i).degree ≤ 1) : (fermatFormula p forms rho).degree ≤ d * (p - 1) := by
  refine (Formula.degree_prodList_le _).trans ?_
  simp only [List.map_ofFn, List.sum_ofFn, Function.comp_def, Formula.degree, zero_max, _root_.max_zero]
  calc ∑ i, (p - 1) * (forms i).degree ≤ ∑ _i : Fin d, (p - 1) :=
        Finset.sum_le_sum fun i _ => by have := Nat.mul_le_mul_left (p - 1) (h i); simpa using this
    _ = _ := by simp

/-- `lem:print`(a), paper/paper.tex: one signed walk's exact integer polynomial. -/
def residueWalkFormula {V m d : ℕ} (weight : ℤ) (masks : Fin (2 * m) → Formula V)
    (forms : Fin d → Formula V) (rho : Fin d → ℤ) (p e : ℕ) : Formula V :=
  .mul (.const weight) (.mul (walkMaskFormula masks) (Formula.amp e (fermatFormula p forms rho)))

/-- `lem:print`(a), paper/paper.tex: exact degree 4m Xmax + (2e−1)d(p−1), where d counts the digit and score tests. -/
theorem residueWalkFormula_degree {V m d Xmax : ℕ} (weight : ℤ) (masks : Fin (2 * m) → Formula V)
    (forms : Fin d → Formula V) (rho : Fin d → ℤ) (p e : ℕ)
    (hmasks : ∀ a, (masks a).degree ≤ 2 * Xmax) (hforms : ∀ i, (forms i).degree ≤ 1) :
    (residueWalkFormula weight masks forms rho p e).degree ≤
      4 * m * Xmax + (2 * e - 1) * d * (p - 1) := by
  simp only [residueWalkFormula, Formula.degree, zero_add]
  apply Nat.add_le_add (walkMaskFormula_degree masks hmasks)
  calc (Formula.amp e (fermatFormula p forms rho)).degree ≤
      (2 * e - 1) * (fermatFormula p forms rho).degree := Formula.degree_amp_le _ _
    _ ≤ (2 * e - 1) * (d * (p - 1)) := Nat.mul_le_mul_left _ (fermatFormula_degree p forms rho hforms)
    _ = _ := by ring

/-- `lem:print`(b), paper/paper.tex: one masked even moment on a walk. -/
def momentWalkFormula {V m : ℕ} (masks : Fin (2 * m) → Formula V) (form : Formula V) (k : ℕ) : Formula V :=
  .mul (walkMaskFormula masks) (.pow form (2 * m * k))

/-- `lem:print`(b), paper/paper.tex: the mask plus moment degree is 4m Xmax + 2mk. -/
theorem momentWalkFormula_degree {V m Xmax : ℕ} (masks : Fin (2 * m) → Formula V)
    (form : Formula V) (k : ℕ) (hmasks : ∀ a, (masks a).degree ≤ 2 * Xmax) (hf : form.degree ≤ 1) :
    (momentWalkFormula masks form k).degree ≤ 4 * m * Xmax + 2 * m * k := by
  simp only [momentWalkFormula, Formula.degree]
  exact Nat.add_le_add (walkMaskFormula_degree masks hmasks)
    (by have := Nat.mul_le_mul_left (2 * m * k) hf; simpa using this)

/-- `lem:print`(c), paper/paper.tex: the population moment has degree at most 4k. -/
theorem populationMomentFormula_degree {V : ℕ} (populationForm : Formula V) (k : ℕ)
    (h : populationForm.degree ≤ 2) : (Formula.pow populationForm (2 * k)).degree ≤ 4 * k := by
  change (2 * k) * populationForm.degree ≤ _
  calc _ ≤ (2 * k) * 2 := Nat.mul_le_mul_left _ h
    _ = _ := by ring

end NearQuarticWires.Cells
