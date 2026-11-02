import Proof.Quartic.StagePrint.BuilderPopulation

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StagePrint
open NearCubicWires NearCubicWires.WireExponent3_5.Shared
open NearQuarticWires NearCubicGates.Close.Interfaces
open NearCubicGates.Close.Tabulator

/-- `sec:cells` and `lem:print`, paper/paper.tex: a circuit's integer occurrence weights embedded in the unchanged concatenated physical bank. -/
def circuitWeights (c : Call) (j : Fin 2) (f : Fin (Builder.occurrences c j) → ℤ) :
    Fin (Builder.allGates c).length → ℤ :=
  fun i => if hj : j.val = 0 then
    if h : i.val < c.first.gates.length then
      f ⟨i.val, by
        have hj0 : j = 0 := Fin.ext hj
        simpa [hj0, Builder.occurrences, Builder.gatesOf] using h⟩ else 0
  else
    if h : c.first.gates.length ≤ i.val then
      f ⟨i.val - c.first.gates.length, by
        have hj1 : j = 1 := by apply Fin.ext; have := j.isLt; omega
        have hi := i.isLt
        change i.val < (c.first.gates ++ c.second.gates).length at hi
        simp only [List.length_append] at hi
        simpa [hj1, Builder.occurrences, Builder.gatesOf] using
          (show i.val - c.first.gates.length < c.second.gates.length by omega)⟩ else 0

/-- `sec:cells` and `lem:print`, paper/paper.tex: concatenating occurrence labels changes no weighted gate sum. -/
theorem circuitWeights_sum (c : Call) (j : Fin 2) (f : Fin (Builder.occurrences c j) → ℤ)
    (F : NormalizedThresholdGate c.n → ℤ) :
    (∑ i, circuitWeights c j f i * F (callAtoms c i)) =
      ∑ t : Fin (Builder.occurrences c j), f t * F ((Builder.gatesOf c j)[t.val]) := by
  classical
  have hlen : (Builder.allGates c).length = c.first.gates.length + c.second.gates.length :=
    by simp [Builder.allGates]
  have hj : j = 0 ∨ j = 1 := by have := j.isLt; omega
  rcases hj with rfl | rfl
  · let summand : Fin (c.first.gates.length + c.second.gates.length) → ℤ := fun i =>
      (if h : i.val < c.first.gates.length then f ⟨i.val, h⟩ else 0) *
        F ((c.first.gates ++ c.second.gates)[i.val])
    have he : (∑ i, circuitWeights c 0 f i * F (callAtoms c i)) = ∑ i, summand i := by
      apply Fintype.sum_equiv (finCongr hlen)
      intro i
      change circuitWeights c 0 f i * F (callAtoms c i) = summand (Fin.cast hlen i)
      simp [summand, circuitWeights, callAtoms, Builder.allGates, Fin.cast]
    rw [he, Fin.sum_univ_add]
    simp [summand, Fin.isLt, List.getElem_append_left, List.getElem_append_right,
      Builder.occurrences, Builder.gatesOf]
    rfl
  · let summand : Fin (c.first.gates.length + c.second.gates.length) → ℤ := fun i =>
      (if h : c.first.gates.length ≤ i.val then
        f ⟨i.val - c.first.gates.length, by
          change i.val - c.first.gates.length < c.second.gates.length
          have hi := i.isLt
          omega⟩ else 0) *
        F ((c.first.gates ++ c.second.gates)[i.val])
    have he : (∑ i, circuitWeights c 1 f i * F (callAtoms c i)) = ∑ i, summand i := by
      apply Fintype.sum_equiv (finCongr hlen)
      intro i
      change circuitWeights c 1 f i * F (callAtoms c i) = summand (Fin.cast hlen i)
      simp [summand, circuitWeights, callAtoms, Builder.allGates, Fin.cast]
    rw [he, Fin.sum_univ_add]
    simp [summand, Fin.isLt, List.getElem_append_left, List.getElem_append_right,
      Builder.occurrences, Builder.gatesOf, show ∀ x : Fin c.first.gates.length,
        ¬c.first.gates.length ≤ x.val from fun x => by have := x.isLt; omega]
    rfl

/-- `sec:walks` and `lem:print`, paper/paper.tex: one linear formula for arbitrary integer occurrence weights on a circuit. -/
def callWalkFormula (c : Call) (j : Fin 2) (f : Fin (Builder.occurrences c j) → ℤ)
    (sigma : Cycle.SignPattern 4) : Formula (17 * (Builder.allGates c).length) :=
  Cells.pooledWalkFormula (by norm_num : 0 < 4) (circuitWeights c j f) (fun l => Cycle.signValue (sigma l))

/-- `lem:print`, paper/paper.tex: the weighted circuit walk formula is linear. -/
theorem callWalkFormula_degree (c : Call) (j : Fin 2) (f : Fin (Builder.occurrences c j) → ℤ)
    (sigma : Cycle.SignPattern 4) : (callWalkFormula c j f sigma).degree ≤ 1 :=
  Cells.pooledWalkFormula_degree _ _ _

/-- `sec:walks` and `lem:print`, paper/paper.tex: the formula evaluates to the complete weighted occurrence contributions on the actual star walk. -/
theorem callWalkFormula_eval (c : Call) {p : Cells.Parameters}
    (hs : Cells.ParameterRules (Builder.callInput c) p) (w : List Bool)
    (z : Fin (2 ^ (c.n - p.k))) (walk : Cycle.Walk hs.seedParameters.N 4)
    (j : Fin 2) (f : Fin (Builder.occurrences c j) → ℤ) (sigma : Cycle.SignPattern 4) :
    (callWalkFormula c j f sigma).eval
      (boolPoint (Cells.walkAtomPoint (Builder.star c hs) (by norm_num : 0 < 4) (callPatterns c hs walk)
        (callAtoms c) (Builder.center c hs w z))) =
      ∑ t, f t * Builder.contribution c hs w z j t sigma walk := by
  rw [callWalkFormula, Cells.pooledWalkFormula_eval]
  have hsum : (∑ g, ∑ e, circuitWeights c j f g * Cycle.signValue (sigma e) *
      Cells.delta (Builder.star c hs) (callAtoms c g) (Builder.center c hs w z)
        (callPatterns c hs walk (Cells.leftSlot (by norm_num : 0 < 4) e))
        (callPatterns c hs walk (Cells.rightSlot (by norm_num : 0 < 4) e))) =
      ∑ g, circuitWeights c j f g *
        (∑ e, Cycle.signValue (sigma e) * Cells.delta (Builder.star c hs) (callAtoms c g)
          (Builder.center c hs w z)
          (callPatterns c hs walk (Cells.leftSlot (by norm_num : 0 < 4) e))
          (callPatterns c hs walk (Cells.rightSlot (by norm_num : 0 < 4) e))) := by
    simp only [Finset.mul_sum, mul_assoc]
  rw [hsum]
  let F : NormalizedThresholdGate c.n → ℤ := fun g =>
    ∑ e, Cycle.signValue (sigma e) * Cells.delta (Builder.star c hs) g
      (Builder.center c hs w z)
      (callPatterns c hs walk (Cells.leftSlot (by norm_num : 0 < 4) e))
      (callPatterns c hs walk (Cells.rightSlot (by norm_num : 0 < 4) e))
  change (∑ g, circuitWeights c j f g * F (callAtoms c g)) = _
  rw [circuitWeights_sum c j f F]
  apply Finset.sum_congr rfl
  intro t _
  dsimp [F]
  congr 1

end NearQuarticWires.StagePrint
