import Proof.Quartic.Cells.WalkFormulas

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StagePrint
open NearCubicWires NearCubicWires.WireExponent3_5.Shared
open NearQuarticWires.Cells
open NearCubicGates.Close.Tabulator

/-- `eq:testX` and `lem:print`(c), paper/paper.tex: only the occurrence labels selected by the retained witness contribute to population. -/
def selectedSquare {m G : ℕ} (hm : 0 < m) (selection : Fin G → Bool) (e : Fin (2 * m))
    (g : Fin G) : Formula ((4 * m + 1) * G) :=
  if selection g then .pow (edgeFormula hm e g) 2 else .const 0

/-- `lem:print`(c), paper/paper.tex: every selected square is quadratic in the unchanged shared atom pool. -/
theorem selectedSquare_degree {m G : ℕ} (hm : 0 < m) (selection : Fin G → Bool)
    (e : Fin (2 * m)) (g : Fin G) : (selectedSquare hm selection e g).degree ≤ 2 := by
  unfold selectedSquare
  split <;> simp [Formula.degree, edgeFormula_degree]

/-- `eq:testX` and `lem:print`(c), paper/paper.tex: the exact selected population formula. -/
def selectedPopulationFormula {m G : ℕ} (hm : 0 < m) (selection : Fin G → Bool)
    (e : Fin (2 * m)) : Formula ((4 * m + 1) * G) :=
  Formula.sumList (List.ofFn (selectedSquare hm selection e))

/-- `lem:print`(c), paper/paper.tex: the retained-witness population is quadratic. -/
theorem selectedPopulationFormula_degree {m G : ℕ} (hm : 0 < m) (selection : Fin G → Bool)
    (e : Fin (2 * m)) : (selectedPopulationFormula hm selection e).degree ≤ 2 := by
  apply Formula.degree_sumList_le
  intro f hf
  obtain ⟨g, rfl⟩ := List.mem_ofFn.mp hf
  exact selectedSquare_degree hm selection e g

/-- `eq:testX` and `lem:print`(c), paper/paper.tex: the selected formula equals the actual integer sum of absolute residuals. -/
theorem selectedPopulationFormula_eval (P : StarParams) {m G : ℕ} (hm : 0 < m)
    (w : Fin (2 * m) → P.Errors) (gates : Fin G → NormalizedThresholdGate P.n)
    (c : BitInput P.n) (selection : Fin G → Bool) (e : Fin (2 * m)) :
    (selectedPopulationFormula hm selection e).eval (boolPoint (walkAtomPoint P hm w gates c)) =
      ∑ g, if selection g then (delta P (gates g) c (w (leftSlot hm e)) (w (rightSlot hm e))).natAbs else 0 := by
  simp only [selectedPopulationFormula, Formula.eval_sumList, List.map_ofFn, List.sum_ofFn, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro g _
  dsimp only [Function.comp_def]
  by_cases hs : selection g = true
  · have h : (edgeFormula hm e g).eval (boolPoint (walkAtomPoint P hm w gates c)) ^ 2 =
        ((delta P (gates g) c (w (leftSlot hm e)) (w (rightSlot hm e))).natAbs : ℤ) := by
      rw [edgeFormula_eval, ← delta_abs_eq_sq, Int.natCast_natAbs]
    simpa only [selectedSquare, hs, if_true, Formula.eval, Nat.cast_ite, Nat.cast_zero] using h
  · simp [selectedSquare, hs, Formula.eval]

/-- `def:mask` and `lem:print`, paper/paper.tex: selected active occurrence labels retain duplicates in the raw list. -/
def selectedActive (P : StarParams) {m G : ℕ} (hm : 0 < m) (w : Fin (2 * m) → P.Errors)
    (gates : Fin G → NormalizedThresholdGate P.n) (c : BitInput P.n)
    (selection : Fin G → Bool) (e : Fin (2 * m)) : Finset (Fin G) :=
  Finset.univ.filter fun g => selection g = true ∧
    delta P (gates g) c (w (leftSlot hm e)) (w (rightSlot hm e)) ≠ 0

/-- `lem:maskpoly` and `lem:print`, paper/paper.tex: the selected residual squares are the literal active-set indicators. -/
theorem selectedSquare_eval (P : StarParams) {m G : ℕ} (hm : 0 < m)
    (w : Fin (2 * m) → P.Errors) (gates : Fin G → NormalizedThresholdGate P.n)
    (c : BitInput P.n) (selection : Fin G → Bool) (e : Fin (2 * m)) (g : Fin G) :
    (selectedSquare hm selection e g).eval (boolPoint (walkAtomPoint P hm w gates c)) =
      if g ∈ selectedActive P hm w gates c selection e then 1 else 0 := by
  by_cases hs : selection g = true
  · simp only [selectedSquare, hs, if_true, Formula.eval, edgeFormula_eval]
    rw [← delta_abs_eq_sq, ← Int.natCast_natAbs, delta_natAbs_eq_indicator]
    simp [selectedActive, hs]
  · simp [selectedSquare, hs, selectedActive, Formula.eval]

/-- `lem:maskpoly` and `lem:print`, paper/paper.tex: the actual witness-selected edge mask formula. -/
noncomputable def selectedMaskFormula {m G : ℕ} (hm : 0 < m) (selection : Fin G → Bool)
    (structural : Bool) (e : Fin (2 * m)) (tau Xmax : ℕ) : Formula ((4 * m + 1) * G) :=
  Mask.maskFormula structural (selectedSquare hm selection e) tau Xmax

/-- `lem:print`, paper/paper.tex: selected masks keep the stated quadratic-per-active-count degree. -/
theorem selectedMaskFormula_degree {m G : ℕ} (hm : 0 < m) (selection : Fin G → Bool)
    (structural : Bool) (e : Fin (2 * m)) (tau Xmax : ℕ) :
    (selectedMaskFormula hm selection structural e tau Xmax).degree ≤ 2 * Xmax :=
  Mask.maskFormula_degree_le _ _ _ _ (selectedSquare_degree hm selection e)

/-- `lem:maskpoly` and `lem:print`, paper/paper.tex: the selected mask is exact on its complete declared population range. -/
theorem selectedMaskFormula_eval (P : StarParams) {m G : ℕ} (hm : 0 < m)
    (w : Fin (2 * m) → P.Errors) (gates : Fin G → NormalizedThresholdGate P.n)
    (c : BitInput P.n) (selection : Fin G → Bool) (structural : Bool)
    (e : Fin (2 * m)) (tau Xmax : ℕ)
    (hX : (selectedActive P hm w gates c selection e).card ≤ Xmax ∨ structural = false) :
    (selectedMaskFormula hm selection structural e tau Xmax).eval (boolPoint (walkAtomPoint P hm w gates c)) =
      Mask.mask structural tau (selectedActive P hm w gates c selection e).card :=
  Mask.maskFormula_eval_eq_mask _ _ _ _ _ _ (selectedSquare_eval P hm w gates c selection e) hX


/-- `lem:maskpoly` and `lem:print`, paper/paper.tex: the selected mask formula always evaluates to the literal integer mask polynomial, also before the population test. -/
theorem selectedMaskFormula_eval_poly (P : StarParams) {m G : ℕ} (hm : 0 < m)
    (w : Fin (2 * m) → P.Errors) (gates : Fin G → NormalizedThresholdGate P.n)
    (c : BitInput P.n) (selection : Fin G → Bool) (structural : Bool)
    (e : Fin (2 * m)) (tau Xmax : ℕ) :
    (selectedMaskFormula hm selection structural e tau Xmax).eval (boolPoint (walkAtomPoint P hm w gates c)) =
      Mask.maskPolyEval structural tau Xmax (selectedActive P hm w gates c selection e).card := by
  let active := selectedActive P hm w gates c selection e
  have hchoose (a : ℕ) :
      (∑ s ∈ Finset.univ.powersetCard a,
        ∏ i ∈ s, (if i ∈ active then (1 : ℤ) else 0)) = (active.card.choose a : ℤ) := by
    simpa only [MvPolynomial.esymm, map_sum, map_prod, MvPolynomial.eval_X] using
      Mask.eval_esymm_indicator active a
  dsimp only [active] at hchoose
  simp only [selectedMaskFormula, Mask.maskFormula, Formula.eval, Mask.formulaSum_eval,
    Mask.formulaProd_eval, selectedSquare_eval, hchoose, Mask.maskPolyEval]

end NearQuarticWires.StagePrint
