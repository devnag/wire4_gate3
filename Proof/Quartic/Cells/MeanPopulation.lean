import Proof.Quartic.Cells.Mixed
import Proof.Quartic.Cells.Partition

set_option autoImplicit false

namespace NearQuarticWires.Cells
open NearCubicWires Finset
open NearCubicWires.WireExponent3_5.Shared

/-- `lem:meanpop`, paper/paper.tex: total bottom fan-in, without charging top wires. -/
def supportSum {n : ℕ} (gates : List (NormalizedThresholdGate n)) : ℕ :=
  (gates.map fun g => (gateSupport g).card).sum

/-- `lem:meanpop`, paper/paper.tex: the paper's explicit population rate, with constant six. -/
noncomputable def populationRate (P : StarParams) : ℝ :=
  6 * (P.r * Real.sqrt P.r) / (P.n * Real.sqrt P.n)

/-- `lem:meanpop`, paper/paper.tex: mean population in a fixed partition, using its unique cell decomposition. -/
noncomputable def partitionMean (P : StarParams) (gates : List (NormalizedThresholdGate P.n))
    (σ : P.Translation) : ℝ :=
  (∑ x, (population P gates (P.center σ x) (P.leftErrors σ x) (P.rightErrors σ x) : ℝ)) / 2 ^ P.n

/-- `lem:meanpop`, paper/paper.tex: the explicit uniform mean over the centers and points of one partition. -/
noncomputable def cellMean (P : StarParams) (gates : List (NormalizedThresholdGate P.n))
    (σ : P.Translation) : ℝ :=
  (∑ c ∈ univ.filter (P.IsCenter σ), ∑ u : P.Errors, ∑ v : P.Errors,
    (population P gates c u v : ℝ)) / 2 ^ P.n

/-- `lem:meanpop`, paper/paper.tex: the sharper proved constant 4 sqrt(2) is at most six. -/
theorem four_sqrt_two_le_six : 4 * Real.sqrt 2 ≤ 6 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hn := Real.sqrt_nonneg (2 : ℝ)
  nlinarith

/-- `lem:meanpop`, paper/paper.tex: each occurrence's partition-averaged population costs only its support. -/
theorem average_atom_le (P : StarParams) (g : NormalizedThresholdGate P.n) :
    (∑ σ : P.Translation, partitionMean P [g] σ) / Fintype.card P.Translation ≤
      populationRate P * (gateSupport g).card := by
  have h := P.translationAverage_mixed_le g
  have heq : (∑ σ : P.Translation, partitionMean P [g] σ) / Fintype.card P.Translation =
      (∑ σ : P.Translation, ∑ x, if delta P g (P.center σ x) (P.leftErrors σ x) (P.rightErrors σ x) ≠ 0
        then (1 : ℝ) else 0) / ((Fintype.card P.Translation : ℝ) * 2 ^ P.n) := by
    simp only [partitionMean, population, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.add_zero, delta_natAbs_eq_indicator]
    simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    rw [← Finset.sum_div, div_div, mul_comm]
  rw [heq]
  calc _ ≤ 4 * Real.sqrt 2 * (P.r * Real.sqrt P.r) * (gateSupport g).card / (P.n * Real.sqrt P.n) := h
    _ ≤ 6 * (P.r * Real.sqrt P.r) * (gateSupport g).card / (P.n * Real.sqrt P.n) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_right four_sqrt_two_le_six (by positivity)
    _ = _ := by unfold populationRate; ring

/-- `lem:meanpop`, paper/paper.tex: linearity retains multiplicities and sums only bottom fan-in. -/
theorem average_population_le (P : StarParams) (gates : List (NormalizedThresholdGate P.n)) :
    (∑ σ : P.Translation, partitionMean P gates σ) / Fintype.card P.Translation ≤
      populationRate P * supportSum gates := by
  induction gates with
  | nil => simp [partitionMean, population, supportSum]
  | cons g gates ih =>
    have hs : ∀ σ, partitionMean P (g :: gates) σ = partitionMean P [g] σ + partitionMean P gates σ := by
      intro σ
      simp [partitionMean, population, Nat.cast_add, Finset.sum_add_distrib, add_div]
    simp only [hs, Finset.sum_add_distrib, add_div, supportSum, List.map_cons, List.sum_cons,
      Nat.cast_add, mul_add]
    exact add_le_add (average_atom_le P g) ih

/-- `imp:partition` and `lem:meanpop`, paper/paper.tex: the two exact means coincide. -/
theorem partitionMean_eq_cellMean (P : StarParams) (gates : List (NormalizedThresholdGate P.n))
    (σ : P.Translation) : partitionMean P gates σ = cellMean P gates σ := by
  unfold partitionMean cellMean
  congr 1
  rw [P.sum_eq_sum_cells σ]
  apply Finset.sum_congr rfl
  intro c hc
  have hc' := (Finset.mem_filter.mp hc).2
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  rw [P.center_point hc', P.leftErrors_point hc', P.rightErrors_point hc']

/-- `lem:meanpop`, paper/paper.tex: some actual partition has mean at most 6 r^(3/2) W / n^(3/2). -/
theorem mean_population (P : StarParams) (gates : List (NormalizedThresholdGate P.n))
    (W : ℕ) (hW : supportSum gates ≤ W) :
    ∃ σ : P.Translation, cellMean P gates σ ≤
      6 * (P.r * Real.sqrt P.r) * W / (P.n * Real.sqrt P.n) := by
  have h := average_population_le P gates
  have hpos : (0 : ℝ) < Fintype.card P.Translation := by
    have hp := Fintype.card_pos (α := P.Translation)
    exact_mod_cast hp
  rw [div_le_iff₀ hpos] at h
  have hs : (∑ σ : P.Translation, partitionMean P gates σ) ≤
      ∑ _σ : P.Translation, populationRate P * supportSum gates := by
    simpa [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm] using h
  obtain ⟨σ, _, hσ⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hs
  refine ⟨σ, ?_⟩
  rw [← partitionMean_eq_cellMean]
  calc partitionMean P gates σ ≤ populationRate P * supportSum gates := hσ
    _ ≤ populationRate P * W := mul_le_mul_of_nonneg_left (by exact_mod_cast hW) (by unfold populationRate; positivity)
    _ = _ := by unfold populationRate; ring

end NearQuarticWires.Cells
