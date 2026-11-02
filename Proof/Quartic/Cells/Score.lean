import Proof.Wire_3_5.StarSelection

set_option autoImplicit false

namespace NearQuarticWires.Cells
open NearCubicWires Finset
open NearCubicWires.WireExponent3_5.Shared

/-- `sec:cells`, paper/paper.tex: the integer four-corner residual of one occurrence. -/
def delta (P : StarParams) (g : NormalizedThresholdGate P.n)
    (c : BitInput P.n) (u v : P.Errors) : ℤ :=
  mixedDifference g.eval c (P.errorVector P.leftBlock u) (P.errorVector P.rightBlock v)

/-- `sec:cells`, paper/paper.tex: the left score, with the center value subtracted. -/
def scoreLeft (P : StarParams) (gates : List (NormalizedThresholdGate P.n))
    (c : BitInput P.n) (u : P.Errors) : ℤ :=
  (gates.map fun g => bitZ (g.eval (xorInput c (P.errorVector P.leftBlock u))) - bitZ (g.eval c)).sum

/-- `sec:cells`, paper/paper.tex: the right score. -/
def scoreRight (P : StarParams) (gates : List (NormalizedThresholdGate P.n))
    (c : BitInput P.n) (v : P.Errors) : ℤ :=
  (gates.map fun g => bitZ (g.eval (xorInput c (P.errorVector P.rightBlock v)))).sum

/-- `sec:cells`, paper/paper.tex: the number of accepting occurrences, counting repetitions. -/
def score (P : StarParams) (gates : List (NormalizedThresholdGate P.n))
    (c : BitInput P.n) (u v : P.Errors) : ℤ :=
  (gates.map fun g => bitZ (g.eval (P.point c u v))).sum

/-- `sec:cells`, paper/paper.tex: the signed mixed residual of the circuit. -/
def residual (P : StarParams) (gates : List (NormalizedThresholdGate P.n))
    (c : BitInput P.n) (u v : P.Errors) : ℤ :=
  (gates.map fun g => delta P g c u v).sum

/-- `sec:cells`, paper/paper.tex: the population, as a natural-number sum of absolute residuals. -/
def population (P : StarParams) (gates : List (NormalizedThresholdGate P.n))
    (c : BitInput P.n) (u v : P.Errors) : ℕ :=
  (gates.map fun g => (delta P g c u v).natAbs).sum

/-- `imp:range`, paper/paper.tex: the actual product-star residual is in {-1,0,1}. -/
theorem delta_range (P : StarParams) (g : NormalizedThresholdGate P.n)
    (c : BitInput P.n) (u v : P.Errors) : delta P g c u v ∈ ({-1, 0, 1} : Finset ℤ) :=
  star_range P g c u v

/-- `imp:range`, paper/paper.tex: absolute residual bound consumed by walk sums. -/
theorem delta_abs_le (P : StarParams) (g : NormalizedThresholdGate P.n)
    (c : BitInput P.n) (u v : P.Errors) : |delta P g c u v| ≤ 1 := by
  have h := delta_range P g c u v
  simp only [Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with h | h | h <;> simp [h]

/-- `sec:cells`, paper/paper.tex: absolute residual equals its integer square. -/
theorem delta_abs_eq_sq (P : StarParams) (g : NormalizedThresholdGate P.n)
    (c : BitInput P.n) (u v : P.Errors) : |delta P g c u v| = delta P g c u v ^ 2 := by
  have h := delta_range P g c u v
  simp only [Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with h | h | h <;> simp [h]

/-- `sec:cells`, paper/paper.tex: each nonzero occurrence contributes exactly one to population. -/
theorem delta_natAbs_eq_indicator (P : StarParams) (g : NormalizedThresholdGate P.n)
    (c : BitInput P.n) (u v : P.Errors) :
    (delta P g c u v).natAbs = if delta P g c u v ≠ 0 then 1 else 0 := by
  have h := delta_range P g c u v
  simp only [Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with h | h | h <;> simp [h]

/-- `lem:identity`, paper/paper.tex: exact score decomposition in the paper's convention. -/
theorem score_identity (P : StarParams) (gates : List (NormalizedThresholdGate P.n))
    (c : BitInput P.n) (u v : P.Errors) :
    score P gates c u v = scoreLeft P gates c u + scoreRight P gates c v + residual P gates c u v := by
  induction gates with
  | nil => simp [score, scoreLeft, scoreRight, residual]
  | cons g gates ih =>
    simp only [score, scoreLeft, scoreRight, residual, List.map_cons, List.sum_cons] at ih ⊢
    unfold delta mixedDifference StarParams.point at ih ⊢
    linear_combination ih

/-- `lem:identity`, paper/paper.tex: scores lie between zero and the occurrence count. -/
theorem score_bounds (P : StarParams) (gates : List (NormalizedThresholdGate P.n))
    (c : BitInput P.n) (u v : P.Errors) : 0 ≤ score P gates c u v ∧ score P gates c u v ≤ gates.length := by
  induction gates with
  | nil => simp [score]
  | cons g gates ih =>
    simp only [score, List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one] at ih ⊢
    have hb : 0 ≤ bitZ (g.eval (P.point c u v)) ∧ bitZ (g.eval (P.point c u v)) ≤ 1 := by
      cases g.eval (P.point c u v) <;> norm_num [bitZ]
    omega

/-- `lem:identity`, paper/paper.tex: the residual is bounded by the occurrence count. -/
theorem residual_abs_le (P : StarParams) (gates : List (NormalizedThresholdGate P.n))
    (c : BitInput P.n) (u v : P.Errors) : |residual P gates c u v| ≤ gates.length := by
  induction gates with
  | nil => simp [residual]
  | cons g gates ih =>
    simp only [residual, List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one] at ih ⊢
    exact (abs_add_le _ _).trans (by have := delta_abs_le P g c u v; omega)

/-- `lem:mixed`, paper/paper.tex: incidence counts retain duplicate occurrences. -/
def incidence {n : ℕ} (gates : List (NormalizedThresholdGate n)) (i : Fin n) : ℕ :=
  (gates.map fun g => if g.weight i ≠ 0 then 1 else 0).sum

end NearQuarticWires.Cells
