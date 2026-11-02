import Proof.Quartic.Cells.Atoms
import Proof.Quartic.Cells.PrintingTable
import Proof.Quartic.Mask.Formula

set_option autoImplicit false

namespace NearQuarticWires.Cells
open NearCubicWires NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.Compiler
open NearCubicGates.Close.Tabulator

/-- `lem:print`, paper/paper.tex: exact Boolean assignment to the shared atom pool. -/
def walkAtomPoint (P : StarParams) {m G : ℕ} (hm : 0 < m) (w : Fin (2 * m) → P.Errors)
    (gates : Fin G → NormalizedThresholdGate P.n) (c : BitInput P.n) : Fin ((4 * m + 1) * G) → Bool :=
  fun i => (walkAtoms gates i).eval ((walkCoords P hm w i).point (P.leftPart c) (P.rightPart c))

/-- `lem:print`, paper/paper.tex: concrete linear residual for one edge and occurrence. -/
def edgeFormula {m G : ℕ} (hm : 0 < m) (e : Fin (2 * m)) (g : Fin G) :
    Formula ((4 * m + 1) * G) := deltaFormula (fun j => atomIndex (cornerRole hm e j) g)

/-- `lem:print`, paper/paper.tex: every concrete residual formula is linear. -/
theorem edgeFormula_degree {m G : ℕ} (hm : 0 < m) (e : Fin (2 * m)) (g : Fin G) :
    (edgeFormula hm e g).degree = 1 := deltaFormula_degree _

/-- `lem:print`, paper/paper.tex: the residual formula equals the actual integer residual at that walk edge. -/
theorem edgeFormula_eval (P : StarParams) {m G : ℕ} (hm : 0 < m) (w : Fin (2 * m) → P.Errors)
    (gates : Fin G → NormalizedThresholdGate P.n) (c : BitInput P.n) (e : Fin (2 * m)) (g : Fin G) :
    (edgeFormula hm e g).eval (boolPoint (walkAtomPoint P hm w gates c)) =
      delta P (gates g) c (w (leftSlot hm e)) (w (rightSlot hm e)) :=
  deltaFormula_eval_star P (gates g) c _ _ _ _ (atomIndex_corner_eval P hm w gates c e g)

/-- `sec:cells` and `lem:maskpoly`, paper/paper.tex:
the actual active occurrence set, with repeated gates still distinct labels. -/
def edgeActive (P : StarParams) {m G : ℕ} (hm : 0 < m) (w : Fin (2 * m) → P.Errors)
    (gates : Fin G → NormalizedThresholdGate P.n) (c : BitInput P.n) (e : Fin (2 * m)) : Finset (Fin G) :=
  Finset.univ.filter fun g => delta P (gates g) c (w (leftSlot hm e)) (w (rightSlot hm e)) ≠ 0

/-- `sec:cells`, paper/paper.tex: active-cardinality is exactly the sum of absolute integer residuals. -/
theorem edgeActive_card (P : StarParams) {m G : ℕ} (hm : 0 < m) (w : Fin (2 * m) → P.Errors)
    (gates : Fin G → NormalizedThresholdGate P.n) (c : BitInput P.n) (e : Fin (2 * m)) :
    (edgeActive P hm w gates c e).card =
      ∑ g, (delta P (gates g) c (w (leftSlot hm e)) (w (rightSlot hm e))).natAbs := by
  simp [edgeActive, Finset.card_filter, delta_natAbs_eq_indicator]

/-- `lem:maskpoly` and `lem:print`, paper/paper.tex:
the exact mask formula specialized to the real shared threshold-atom pool. -/
noncomputable def edgeMaskFormula {m G : ℕ} (hm : 0 < m) (structural : Bool)
    (e : Fin (2 * m)) (τ Xmax : ℕ) : Formula ((4 * m + 1) * G) :=
  NearQuarticWires.Mask.maskFormula structural (fun g : Fin G => .pow (edgeFormula hm e g) 2) τ Xmax

/-- `lem:print`, paper/paper.tex: exact mask degree on every concrete walk edge. -/
theorem edgeMaskFormula_degree {m G : ℕ} (hm : 0 < m) (structural : Bool)
    (e : Fin (2 * m)) (τ Xmax : ℕ) : (edgeMaskFormula (G := G) hm structural e τ Xmax).degree ≤ 2 * Xmax := by
  apply NearQuarticWires.Mask.maskFormula_degree_le
  intro g
  simp only [Formula.degree, edgeFormula_degree, mul_one, le_refl]

/-- `lem:maskpoly` and `lem:print`, paper/paper.tex:
no modular lift is used; the concrete edge formula evaluates to the literal integer mask. -/
theorem edgeMaskFormula_eval (P : StarParams) {m G : ℕ} (hm : 0 < m) (w : Fin (2 * m) → P.Errors)
    (gates : Fin G → NormalizedThresholdGate P.n) (c : BitInput P.n) (structural : Bool)
    (e : Fin (2 * m)) (τ Xmax : ℕ)
    (hX : (edgeActive P hm w gates c e).card ≤ Xmax ∨ structural = false) :
    (edgeMaskFormula hm structural e τ Xmax).eval (boolPoint (walkAtomPoint P hm w gates c)) =
      NearQuarticWires.Mask.mask structural τ (edgeActive P hm w gates c e).card := by
  apply NearQuarticWires.Mask.maskFormula_eval_eq_mask _ _ _ _ _ _ _ hX
  intro g
  have h := residualIndicatorFormula_eval_star P (gates g) c
    (w (leftSlot hm e)) (w (rightSlot hm e)) (fun j => atomIndex (cornerRole hm e j) g)
    (walkAtomPoint P hm w gates c) (atomIndex_corner_eval P hm w gates c e g)
  simpa only [residualIndicatorFormula, edgeFormula, edgeActive, Finset.mem_filter, Finset.mem_univ, true_and] using h

/-- `lem:print`, paper/paper.tex: exact evaluation of the product of all edge masks. -/
theorem walkMaskFormula_eval {V m : ℕ} (masks : Fin (2 * m) → Formula V) (β : Fin V → ℤ) :
    (walkMaskFormula masks).eval β = ∏ e, (masks e).eval β := by
  simp [walkMaskFormula, Formula.eval_prodList, List.map_ofFn, List.prod_ofFn, Function.comp_def]

/-- `lem:print`(b), paper/paper.tex: exact masked even moment over the shared pool. -/
theorem momentWalkFormula_eval {V m : ℕ} (masks : Fin (2 * m) → Formula V)
    (form : Formula V) (k : ℕ) (β : Fin V → ℤ) :
    (momentWalkFormula masks form k).eval β = (∏ e, (masks e).eval β) * form.eval β ^ (2 * m * k) := by
  simp only [momentWalkFormula, Formula.eval, walkMaskFormula_eval]

/-- `lem:residue` and `lem:print`, paper/paper.tex:
exact integer evaluation of the Fermat conjunction. -/
theorem fermatFormula_eval {V d : ℕ} (p : ℕ) (forms : Fin d → Formula V) (rho : Fin d → ℤ)
    (β : Fin V → ℤ) : (fermatFormula p forms rho).eval β =
      ∏ i, (1 - ((forms i).eval β - rho i) ^ (p - 1)) := by
  simp [fermatFormula, Formula.eval_prodList, List.map_ofFn, List.prod_ofFn, Function.comp_def, Formula.eval]

/-- `lem:residue` and `lem:print`, paper/paper.tex:
exact signed, masked amplified residue polynomial, before any modular recovery. -/
theorem residueWalkFormula_eval {V m d : ℕ} (weight : ℤ) (masks : Fin (2 * m) → Formula V)
    (forms : Fin d → Formula V) (rho : Fin d → ℤ) (p e : ℕ) (β : Fin V → ℤ) :
    (residueWalkFormula weight masks forms rho p e).eval β =
      weight * ((∏ a, (masks a).eval β) * NearCubicGates.ResidueCounts.amplifierValue e
        (∏ i, (1 - ((forms i).eval β - rho i) ^ (p - 1)))) := by
  simp only [residueWalkFormula, Formula.eval, walkMaskFormula_eval, Formula.eval_amp, fermatFormula_eval]

/-- `lem:print`(c), paper/paper.tex: the actual quadratic population formula. -/
def edgePopulationFormula {m G : ℕ} (hm : 0 < m) (e : Fin (2 * m)) : Formula ((4 * m + 1) * G) :=
  Formula.sumList (List.ofFn fun g : Fin G => .pow (edgeFormula hm e g) 2)

/-- `lem:print`(c), paper/paper.tex: the concrete population is quadratic in the shared atom pool. -/
theorem edgePopulationFormula_degree {m G : ℕ} (hm : 0 < m) (e : Fin (2 * m)) :
    (edgePopulationFormula (G := G) hm e).degree ≤ 2 := by
  apply Formula.degree_sumList_le
  intro f hf
  obtain ⟨g, rfl⟩ := List.mem_ofFn.mp hf
  simp only [Formula.degree, edgeFormula_degree, mul_one, le_refl]

/-- `lem:print`(c), paper/paper.tex: evaluation equals the real integer occurrence population. -/
theorem edgePopulationFormula_eval (P : StarParams) {m G : ℕ} (hm : 0 < m)
    (w : Fin (2 * m) → P.Errors) (gates : Fin G → NormalizedThresholdGate P.n)
    (c : BitInput P.n) (e : Fin (2 * m)) :
    (edgePopulationFormula hm e).eval (boolPoint (walkAtomPoint P hm w gates c)) =
      ((edgeActive P hm w gates c e).card : ℤ) := by
  rw [edgeActive_card]
  simp only [edgePopulationFormula, Formula.eval_sumList, List.map_ofFn, List.sum_ofFn, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro g _
  change (edgeFormula hm e g).eval _ ^ 2 = _
  rw [edgeFormula_eval, ← delta_abs_eq_sq, Int.natCast_natAbs]

/-- `lem:print`, paper/paper.tex: linear walk sums on the concrete shared pool. -/
def pooledWalkFormula {m G : ℕ} (hm : 0 < m) (weight : Fin G → ℤ) (sign : Fin (2 * m) → ℤ) :
    Formula ((4 * m + 1) * G) :=
  walkFormula weight sign (fun g e j => atomIndex (cornerRole hm e j) g)

/-- `lem:print`, paper/paper.tex: the real sampled walk form is linear. -/
theorem pooledWalkFormula_degree {m G : ℕ} (hm : 0 < m) (weight : Fin G → ℤ)
    (sign : Fin (2 * m) → ℤ) : (pooledWalkFormula hm weight sign).degree ≤ 1 :=
  walkFormula_degree _ _ _

/-- `lem:print`, paper/paper.tex: literal signed occurrence sum, with no rounding or wrap. -/
theorem pooledWalkFormula_eval (P : StarParams) {m G : ℕ} (hm : 0 < m)
    (w : Fin (2 * m) → P.Errors) (gates : Fin G → NormalizedThresholdGate P.n)
    (c : BitInput P.n) (weight : Fin G → ℤ) (sign : Fin (2 * m) → ℤ) :
    (pooledWalkFormula hm weight sign).eval (boolPoint (walkAtomPoint P hm w gates c)) =
      ∑ g, ∑ e, weight g * sign e * delta P (gates g) c (w (leftSlot hm e)) (w (rightSlot hm e)) := by
  rw [pooledWalkFormula, walkFormula_eval]
  apply Finset.sum_congr rfl
  intro g _
  apply Finset.sum_congr rfl
  intro e _
  congr 1
  exact edgeFormula_eval P hm w gates c e g

/-- `lem:print`(b), paper/paper.tex: the concrete exact masked even moment formula. -/
noncomputable def pooledMomentFormula {m G : ℕ} (hm : 0 < m)
    (structural : Fin (2 * m) → Bool) (τ Xmax k : ℕ)
    (weight : Fin G → ℤ) (sign : Fin (2 * m) → ℤ) : Formula ((4 * m + 1) * G) :=
  momentWalkFormula (fun e => edgeMaskFormula hm (structural e) e τ Xmax) (pooledWalkFormula hm weight sign) k

/-- `lem:print`(b), paper/paper.tex: concrete masked moment degree 4m Xmax + 2mk. -/
theorem pooledMomentFormula_degree {m G : ℕ} (hm : 0 < m)
    (structural : Fin (2 * m) → Bool) (τ Xmax k : ℕ)
    (weight : Fin G → ℤ) (sign : Fin (2 * m) → ℤ) :
    (pooledMomentFormula hm structural τ Xmax k weight sign).degree ≤ 4 * m * Xmax + 2 * m * k :=
  momentWalkFormula_degree _ _ _ (fun e => edgeMaskFormula_degree hm (structural e) e τ Xmax)
    (pooledWalkFormula_degree hm weight sign)

/-- `lem:print`(b), paper/paper.tex: exact concrete mask product times the actual even walk moment. -/
theorem pooledMomentFormula_eval (P : StarParams) {m G : ℕ} (hm : 0 < m)
    (w : Fin (2 * m) → P.Errors) (gates : Fin G → NormalizedThresholdGate P.n)
    (c : BitInput P.n) (structural : Fin (2 * m) → Bool) (τ Xmax k : ℕ)
    (weight : Fin G → ℤ) (sign : Fin (2 * m) → ℤ)
    (hX : ∀ e, (edgeActive P hm w gates c e).card ≤ Xmax ∨ structural e = false) :
    (pooledMomentFormula hm structural τ Xmax k weight sign).eval (boolPoint (walkAtomPoint P hm w gates c)) =
      (∏ e, NearQuarticWires.Mask.mask (structural e) τ (edgeActive P hm w gates c e).card) *
      (∑ g, ∑ e, weight g * sign e * delta P (gates g) c (w (leftSlot hm e)) (w (rightSlot hm e))) ^ (2 * m * k) := by
  rw [pooledMomentFormula, momentWalkFormula_eval, pooledWalkFormula_eval]
  congr 1
  apply Finset.prod_congr rfl
  intro e _
  exact edgeMaskFormula_eval P hm w gates c (structural e) e τ Xmax (hX e)

end NearQuarticWires.Cells
