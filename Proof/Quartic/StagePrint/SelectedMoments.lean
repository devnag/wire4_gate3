import Proof.Quartic.StagePrint.SelectedFormulas

set_option autoImplicit false

namespace NearQuarticWires.StagePrint
open NearCubicWires NearCubicWires.WireExponent3_5.Shared
open NearQuarticWires.Cells
open NearCubicGates.Close.Tabulator

/-- `eq:testX` and `def:mask`, paper/paper.tex: the exact cardinality of the witness-selected active labels. -/
theorem selectedActive_card (P : StarParams) {m G : ℕ} (hm : 0 < m)
    (w : Fin (2 * m) → P.Errors) (gates : Fin G → NormalizedThresholdGate P.n)
    (c : BitInput P.n) (selection : Fin G → Bool) (e : Fin (2 * m)) :
    (selectedActive P hm w gates c selection e).card =
      ∑ g, if selection g then (delta P (gates g) c (w (leftSlot hm e)) (w (rightSlot hm e))).natAbs else 0 := by
  rw [selectedActive, Finset.card_filter]
  apply Finset.sum_congr rfl
  intro g _
  by_cases hs : selection g = true <;> simp [hs, delta_natAbs_eq_indicator]

/-- `lem:print`(b), paper/paper.tex: masked moments use the actual selected population while the walk sum retains every circuit occurrence. -/
noncomputable def selectedMomentFormula {m G : ℕ} (hm : 0 < m) (selection : Fin G → Bool)
    (structural : Fin (2 * m) → Bool) (tau Xmax k : ℕ)
    (weight : Fin G → ℤ) (sign : Fin (2 * m) → ℤ) : Formula ((4 * m + 1) * G) :=
  momentWalkFormula (fun e => selectedMaskFormula hm selection (structural e) e tau Xmax)
    (pooledWalkFormula hm weight sign) k

/-- `lem:print`(b), paper/paper.tex: the literal selected-mask moment has the paper's exact degree bound. -/
theorem selectedMomentFormula_degree {m G : ℕ} (hm : 0 < m) (selection : Fin G → Bool)
    (structural : Fin (2 * m) → Bool) (tau Xmax k : ℕ)
    (weight : Fin G → ℤ) (sign : Fin (2 * m) → ℤ) :
    (selectedMomentFormula hm selection structural tau Xmax k weight sign).degree ≤ 4 * m * Xmax + 2 * m * k :=
  momentWalkFormula_degree _ _ _
    (fun e => selectedMaskFormula_degree hm selection (structural e) e tau Xmax)
    (pooledWalkFormula_degree hm weight sign)

/-- `eq:testE`, `eq:testPhi` and `lem:print`(b), paper/paper.tex: every proposed chain, including a failing chain, has the exact integer mask-polynomial moment. -/
theorem selectedMomentFormula_eval_poly (P : StarParams) {m G : ℕ} (hm : 0 < m)
    (w : Fin (2 * m) → P.Errors) (gates : Fin G → NormalizedThresholdGate P.n)
    (c : BitInput P.n) (selection : Fin G → Bool) (structural : Fin (2 * m) → Bool)
    (tau Xmax k : ℕ) (weight : Fin G → ℤ) (sign : Fin (2 * m) → ℤ) :
    (selectedMomentFormula hm selection structural tau Xmax k weight sign).eval
        (boolPoint (walkAtomPoint P hm w gates c)) =
      (∏ e, Mask.maskPolyEval (structural e) tau Xmax
        (∑ g, if selection g then (delta P (gates g) c (w (leftSlot hm e)) (w (rightSlot hm e))).natAbs else 0)) *
      (∑ g, ∑ e, weight g * sign e * delta P (gates g) c
        (w (leftSlot hm e)) (w (rightSlot hm e))) ^ (2 * m * k) := by
  rw [selectedMomentFormula, momentWalkFormula_eval, pooledWalkFormula_eval]
  congr 1
  apply Finset.prod_congr rfl
  intro e _
  rw [selectedMaskFormula_eval_poly, selectedActive_card]


/-- `eq:testX` and `lem:print`(c), paper/paper.tex: the literal structurally restricted population moment at one cell. -/
def selectedPopulationMomentFormula {m G : ℕ} (hm : 0 < m) (selection : Fin G → Bool)
    (e : Fin (2 * m)) (structural : Bool) (k : ℕ) : Formula ((4 * m + 1) * G) :=
  .mul (.const (if structural then 1 else 0)) (.pow (selectedPopulationFormula hm selection e) (2 * k))

/-- `lem:print`(c), paper/paper.tex: the population test has degree at most 4k, independently of the walk-mask degree. -/
theorem selectedPopulationMomentFormula_degree {m G : ℕ} (hm : 0 < m) (selection : Fin G → Bool)
    (e : Fin (2 * m)) (structural : Bool) (k : ℕ) :
    (selectedPopulationMomentFormula hm selection e structural k).degree ≤ 4 * k := by
  have h := selectedPopulationFormula_degree hm selection e
  change 0 + 2 * k * _ ≤ _
  nlinarith

/-- `eq:testX` and `lem:print`(c), paper/paper.tex: population moments preserve the exact original selected occurrences. -/
theorem selectedPopulationMomentFormula_eval (P : StarParams) {m G : ℕ} (hm : 0 < m)
    (w : Fin (2 * m) → P.Errors) (gates : Fin G → NormalizedThresholdGate P.n)
    (c : BitInput P.n) (selection : Fin G → Bool) (e : Fin (2 * m)) (structural : Bool) (k : ℕ) :
    (selectedPopulationMomentFormula hm selection e structural k).eval
        (boolPoint (walkAtomPoint P hm w gates c)) =
      (if structural then 1 else 0) *
        (∑ g, if selection g then (delta P (gates g) c (w (leftSlot hm e)) (w (rightSlot hm e))).natAbs else 0 : ℤ) ^
          (2 * k) := by
  simp only [selectedPopulationMomentFormula, Formula.eval, selectedPopulationFormula_eval,
    Nat.cast_sum, Nat.cast_ite, Nat.cast_zero]

end NearQuarticWires.StagePrint
