import Proof.Quartic.Cells.ParametersCertSyntaxWeight

set_option autoImplicit false

namespace NearQuarticWires.Cells.ParameterArithmetic

open NearCubicGates.Close.Tabulator

/-- `lem:print`, paper/paper.tex: the literal
finite sum preserves the bounds on all of its integer leaves. -/
theorem cert_sumList_constant_bits {V : ℕ} (fs : List (Formula V)) (L : ℕ)
    (h : ∀ f ∈ fs, formulaConstantBits L f) : formulaConstantBits L (Formula.sumList fs) := by
  induction fs with
  | nil => exact Nat.zero_le L
  | cons f fs ih => exact ⟨h f (by simp), ih (fun g hg => h g (by simp [hg]))⟩

/-- `lem:print`, paper/paper.tex: the literal
finite product adds only the fixed empty-product constant one. -/
theorem cert_prodList_constant_bits {V : ℕ} (fs : List (Formula V)) (L : ℕ) (hL : 1 ≤ L)
    (h : ∀ f ∈ fs, formulaConstantBits L f) : formulaConstantBits L (Formula.prodList fs) := by
  induction fs with
  | nil => exact hL
  | cons f fs ih => exact ⟨h f (by simp), ih (fun g hg => h g (by simp [hg]))⟩

/-- `lem:maskpoly` and `lem:print`, paper/paper.tex: listing a finite index set introduces no new integer leaves. -/
theorem cert_formulaSum_constant_bits {ι : Type*} {V : ℕ} (s : Finset ι)
    (f : ι → Formula V) (L : ℕ) (h : ∀ i ∈ s, formulaConstantBits L (f i)) :
    formulaConstantBits L (Mask.formulaSum s f) := by
  classical
  unfold Mask.formulaSum
  rw [← StageLift.formula_sumList_eq]
  apply cert_sumList_constant_bits
  intro F hF
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hF
  exact h i (by simpa using hi)

/-- `lem:maskpoly` and `lem:print`, paper/paper.tex: a finite subset product preserves its actual leaf bounds. -/
theorem cert_formulaProd_constant_bits {ι : Type*} {V : ℕ} (s : Finset ι)
    (f : ι → Formula V) (L : ℕ) (hL : 1 ≤ L)
    (h : ∀ i ∈ s, formulaConstantBits L (f i)) :
    formulaConstantBits L (Mask.formulaProd s f) := by
  classical
  unfold Mask.formulaProd
  rw [← StageLift.formula_prodList_eq]
  apply cert_prodList_constant_bits _ _ hL
  intro F hF
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hF
  exact h i (by simpa using hi)

/-- `sec:cells` and `lem:print`, paper/paper.tex: the residual's four leaves are formal variables. -/
theorem cert_delta_constant_bits {V : ℕ} (corners : Fin 4 → Fin V) (L : ℕ) :
    formulaConstantBits L (deltaFormula corners) := by
  simp [deltaFormula, formulaConstantBits]

/-- `lem:print`, paper/paper.tex: selected squares
add only the literal zero leaf for unselected occurrences. -/
theorem cert_selected_square_constant_bits {m G : ℕ} (hm : 0 < m)
    (selection : Fin G → Bool) (edge : Fin (2 * m)) (g : Fin G) (L : ℕ) :
    formulaConstantBits L (StagePrint.selectedSquare hm selection edge g) := by
  unfold StagePrint.selectedSquare
  split <;> simp [formulaConstantBits, edgeFormula, deltaFormula]

/-- `lem:maskpoly` and `lem:print`, paper/paper.tex: all original mask constants fit the difference order
or the supplied literal residual-square leaf bound. -/
theorem cert_mask_constant_bits {G V : ℕ} (structural : Bool)
    (b : Fin G → Formula V) (tau X L : ℕ) (hXL : X + 1 ≤ L)
    (hb : ∀ i, formulaConstantBits L (b i)) :
    formulaConstantBits L (Mask.maskFormula structural b tau X) := by
  have hL : 1 ≤ L := by omega
  change formulaConstantBits L (.const (if structural then 1 else 0)) ∧ _
  refine ⟨?_, ?_⟩
  · cases structural with
    | false => exact Nat.zero_le L
    | true => exact hL
  · apply cert_formulaSum_constant_bits
    intro a ha
    have haX : a ≤ X := by simpa using ha
    refine ⟨(cert_newton_coefficient_bits tau a).trans (by omega), ?_⟩
    apply cert_formulaSum_constant_bits
    intro s _
    exact cert_formulaProd_constant_bits s b L hL (fun i _ => hb i)

/-- `lem:print`, paper/paper.tex: every literal
selected mask satisfies its raw constant-bit bound uniformly. -/
theorem cert_selected_mask_constant_bits {m G : ℕ} (hm : 0 < m)
    (selection : Fin G → Bool) (structural : Bool) (edge : Fin (2 * m))
    (tau X L : ℕ) (hXL : X + 1 ≤ L) :
    formulaConstantBits L (StagePrint.selectedMaskFormula hm selection structural edge tau X) :=
  cert_mask_constant_bits structural (StagePrint.selectedSquare hm selection edge) tau X L hXL
    (fun g => cert_selected_square_constant_bits hm selection edge g L)

/-- `sec:walks` and `lem:print`, paper/paper.tex: signs do not enlarge an original occurrence coefficient's
leaf bits in the complete raw linear walk AST. -/
theorem cert_pooled_walk_constant_bits {m G : ℕ} (hm : 0 < m)
    (weight : Fin G → ℤ) (sign : Fin (2 * m) → ℤ) (L : ℕ)
    (hw : ∀ g, Nat.size (weight g).natAbs ≤ L)
    (hs : ∀ e, (sign e).natAbs ≤ 1) :
    formulaConstantBits L (pooledWalkFormula hm weight sign) := by
  unfold pooledWalkFormula walkFormula
  apply cert_sumList_constant_bits
  intro F hF
  obtain ⟨g, rfl⟩ := List.mem_ofFn.mp hF
  apply cert_sumList_constant_bits
  intro f hf
  obtain ⟨e, rfl⟩ := List.mem_ofFn.mp hf
  refine ⟨?_, cert_delta_constant_bits _ _⟩
  have hp : (weight g * sign e).natAbs ≤ (weight g).natAbs := by
    simp only [Int.natAbs_mul]
    simpa only [mul_one] using Nat.mul_le_mul_left (weight g).natAbs (hs e)
  exact Nat.size_le.mpr (hp.trans_lt (Nat.size_le.mp (hw g)))

/-- `lem:print`, paper/paper.tex: the complete
moment constructor preserves mask and linear-form leaf bounds;
its actual exponent is handled by the raw unary syntax codec. -/
theorem cert_moment_constant_bits {V : ℕ} (masks : Fin 8 → Formula V)
    (form : Formula V) (k L : ℕ) (hL : 1 ≤ L)
    (hm : ∀ e, formulaConstantBits L (masks e))
    (hf : formulaConstantBits L form) :
    formulaConstantBits L (momentWalkFormula (m := 4) masks form k) := by
  refine ⟨?_, hf⟩
  unfold walkMaskFormula
  apply cert_prodList_constant_bits _ _ hL
  intro F hF
  obtain ⟨e, rfl⟩ := List.mem_ofFn.mp hF
  exact hm e

/-- `eq:testX` and `lem:print`, paper/paper.tex: the actual population moment adds only the structural
zero/one leaf to the selected residual-square sum. -/
theorem cert_population_constant_bits {m G : ℕ} (hm : 0 < m)
    (selection : Fin G → Bool) (edge : Fin (2 * m)) (structural : Bool) (k L : ℕ)
    (hL : 1 ≤ L) :
    formulaConstantBits L (StagePrint.selectedPopulationMomentFormula hm selection edge structural k) := by
  refine ⟨?_, ?_⟩
  · cases structural with
    | false => exact Nat.zero_le L
    | true => exact hL
  · unfold StagePrint.selectedPopulationFormula
    apply cert_sumList_constant_bits
    intro F hF
    obtain ⟨g, rfl⟩ := List.mem_ofFn.mp hF
    exact cert_selected_square_constant_bits hm selection edge g L

end NearQuarticWires.Cells.ParameterArithmetic
