import Proof.Wire_3_5.StarPartition

set_option autoImplicit false

namespace NearQuarticWires.Cells
open NearCubicWires Finset
open NearCubicWires.WireExponent3_5.Shared

/-- `imp:partition`, paper/paper.tex: every input has one center and one pair of star choices. -/
def partitionEquiv (P : StarParams) (σ : P.Translation) :
    BitInput P.n ≃ {c // P.IsCenter σ c} × P.Errors × P.Errors := P.decomposition σ

/-- `imp:partition`, paper/paper.tex: the exact counts of partitions, cells and points per cell. -/
theorem partition_cardinalities (P : StarParams) (σ : P.Translation) :
    Fintype.card P.Translation = 2 ^ P.k ∧
      Fintype.card {c // P.IsCenter σ c} = 2 ^ (P.n - P.k) ∧
        Fintype.card (P.Errors × P.Errors) = 2 ^ P.k :=
  ⟨P.card_translation, P.card_centers σ, P.card_cell⟩

/-- `imp:partition`, paper/paper.tex: summing a function on cells and points equals its cube sum. -/
theorem partition_sum (P : StarParams) (σ : P.Translation) {R : Type} [AddCommMonoid R]
    (f : BitInput P.n → R) :
    ∑ x, f x = ∑ c ∈ univ.filter (P.IsCenter σ), ∑ u : P.Errors, ∑ v : P.Errors, f (P.point c u v) :=
  P.sum_eq_sum_cells σ f

/-- `imp:partition`, paper/paper.tex: averaging partitions gives a uniform center independent of patterns. -/
theorem partition_average (P : StarParams) (F : BitInput P.n → P.Errors → P.Errors → ℝ) :
    (∑ σ : P.Translation, ∑ x, F (P.center σ x) (P.leftErrors σ x) (P.rightErrors σ x)) /
      ((Fintype.card P.Translation : ℝ) * 2 ^ P.n) =
    (∑ c, ∑ u : P.Errors, ∑ v : P.Errors, F c u v) /
      (2 ^ P.n * (Fintype.card P.Errors : ℝ) ^ 2) := P.average_translations_inputs F

/-- `imp:partition`, paper/paper.tex: balanced center-bit dimensions, with every block on its side. -/
theorem partition_halves (P : StarParams) :
    P.leftCenterBits + P.rightCenterBits = P.n - P.k ∧
    P.rightCenterBits ≤ P.leftCenterBits ∧ P.leftCenterBits ≤ P.rightCenterBits + 1 ∧
    (∀ j i, P.centerSide (P.blockCoord (P.leftBlock j) i) = true) ∧
    (∀ j i, P.centerSide (P.blockCoord (P.rightBlock j) i) = false) :=
  ⟨P.centerBits_sum, P.centerBits_balanced.1, P.centerBits_balanced.2,
    P.centerSide_leftBlock, P.centerSide_rightBlock⟩

end NearQuarticWires.Cells
