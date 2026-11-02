import Proof.Quartic.Walks.Localization
import Proof.Gates.Counter.SamplingBernstein

set_option autoImplicit false

namespace NearQuarticWires.Walks

open scoped BigOperators
open NearCubicGates.FiniteAverages NearCubicGates.PublishedSources.Witness
open NearCubicGates.PublicSamplingRates

/-- Paper `lem:localize`, paper/paper.tex: one shared finite uniform draw
per occurrence realizes ALL rational nested cutoffs on the common denominator. -/
def cutoffCoefficient {Occ : Type*} {M : ℕ} (a : ℕ) (draw : Occ → Fin M) (t : Occ) : ℤ :=
  if (draw t).val < a then 1 else 0

/-- Paper `lem:localize`, paper/paper.tex: the literal sampled sum `K_r`
on that shared draw, retaining signed `c_t` and duplicate occurrences. -/
def cutoffSum {Occ : Type*} [Fintype Occ] {M : ℕ} (c : Occ → ℤ)
    (a : ℕ) (draw : Occ → Fin M) : ℤ :=
  ∑ t, cutoffCoefficient a draw t * c t

/-- Paper `lem:localize`, paper/paper.tex: the normalized independent
summands `(xi-pi)c_t/(2m)` to which the EXTERNAL Bernstein input applies. -/
noncomputable def normalizedNoise {Occ : Type*} {M : ℕ} (m : ℕ)
    (c : Occ → ℤ) (a : ℕ) (t : Occ) (draw : Occ → Fin M) : ℝ :=
  ((c t : ℝ) / (2 * m : ℕ)) *
    ((if (draw t).val < a then (1 : ℝ) else 0) - (a : ℝ) / M)

/-- Paper `lem:localize`, paper/paper.tex: every actual normalized walk
coefficient is bounded by one and its square costs at most `|c_t|`. -/
theorem normalized_coefficient_bounds (m : ℕ) (hm : 0 < m) (c : ℤ)
    (hc : |c| ≤ (2 * m : ℕ)) :
    |(c : ℝ) / (2 * m : ℕ)| ≤ 1 ∧ ((c : ℝ) / (2 * m : ℕ)) ^ 2 ≤ |(c : ℝ)| := by
  have hd : (0 : ℝ) < (2 * m : ℕ) := by exact_mod_cast (show 0 < 2 * m by omega)
  have hd1 : (1 : ℝ) ≤ (2 * m : ℕ) := by exact_mod_cast (show 1 ≤ 2 * m by omega)
  have hc' : |(c : ℝ)| ≤ (2 * m : ℕ) := by exact_mod_cast hc
  have hnorm : |(c : ℝ) / (2 * m : ℕ)| ≤ 1 := by
    rw [abs_div, abs_of_pos hd]
    exact (div_le_iff₀ hd).mpr (by simpa using hc')
  have hsmall : |(c : ℝ) / (2 * m : ℕ)| ≤ |(c : ℝ)| := by
    rw [abs_div, abs_of_pos hd]
    exact div_le_self (abs_nonneg _) hd1
  refine ⟨hnorm, ?_⟩
  have hs := sq_abs ((c : ℝ) / (2 * m : ℕ))
  nlinarith [mul_nonneg (abs_nonneg ((c : ℝ) / (2 * m : ℕ)))
    (sub_nonneg.mpr hnorm)]

/-- Paper `lem:localize`, paper/paper.tex: finite rational-cutoff
Bernstein on the ACTUAL signed occurrence array, including its variance proof. -/
theorem cutoff_stage_tail_of_nonempty {Occ : Type} [Fintype Occ] [DecidableEq Occ] [Nonempty Occ]
    (hB : Vershynin18_Theorem2_8_4_FiniteBernstein.{0, 0})
    (T h ell : ℝ) (hT : 0 < T) (m : ℕ) (hm : 0 < m)
    (c : Occ → ℤ) (hc : ∀ t, |c t| ≤ (2 * m : ℕ))
    (hmass : (∑ t, |(c t : ℝ)|) ≤ liveCap T h ell)
    (M a : ℕ) (hM : 0 < M) (ha : a ≤ M) :
    mean (fun draw : Occ → Fin M => indicator
      (fluctuation T h ell ((a : ℝ) / M) ≤ |∑ t, normalizedNoise m c a t draw|)) ≤
        2 * Real.exp (-T) := by
  classical
  letI : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  let pi : ℝ := (a : ℝ) / M
  have hpi0 : 0 ≤ pi := by positivity
  have hpi1 : pi ≤ 1 := by
    dsimp [pi]
    apply (div_le_iff₀ (by exact_mod_cast hM : (0 : ℝ) < M)).mpr
    simp only [one_mul]
    exact_mod_cast ha
  have hind : finiteIndependent (normalizedNoise m c a) :=
    NearCubicGates.Close.Counter.Sampling.WitnessFailure.independent_coordinates
      (fun t (b : Fin M) => ((c t : ℝ) / (2 * m : ℕ)) *
        ((if b.val < a then (1 : ℝ) else 0) - pi))
  have hzero (t : Occ) : mean (normalizedNoise m c a t : (Occ → Fin M) → ℝ) = 0 := by
    unfold normalizedNoise
    rw [mean_smul, NearCubicGates.Close.Counter.Sampling.WitnessFailure.mean_centered_cutoff
      M a hM ha t, mul_zero]
  have hmag (t : Occ) (draw : Occ → Fin M) : |normalizedNoise m c a t draw| ≤ 1 := by
    have hb : |(if (draw t).val < a then (1 : ℝ) else 0) - pi| ≤ 1 := by
      apply abs_le.mpr
      split_ifs <;> constructor <;> linarith
    unfold normalizedNoise
    rw [abs_mul]
    exact (mul_le_of_le_one_left (abs_nonneg _)
      (normalized_coefficient_bounds m hm (c t) (hc t)).1).trans hb
  have hvar (t : Occ) :
      mean (fun draw : Occ → Fin M => (normalizedNoise m c a t draw) ^ 2) ≤ pi * |(c t : ℝ)| := by
    have hid (draw : Occ → Fin M) : (normalizedNoise m c a t draw) ^ 2 =
        ((c t : ℝ) / (2 * m : ℕ)) ^ 2 *
          ((if (draw t).val < a then (1 : ℝ) else 0) - pi) ^ 2 := by
      unfold normalizedNoise
      exact mul_pow _ _ _
    simp_rw [hid]
    rw [mean_smul, NearCubicGates.Close.Counter.Sampling.WitnessFailure.variance_centered_cutoff
      M a hM ha t]
    change ((c t : ℝ) / (2 * m : ℕ)) ^ 2 * (pi * (1 - pi)) ≤ _
    have hb := (normalized_coefficient_bounds m hm (c t) (hc t)).2
    have hp : pi * (1 - pi) ≤ pi := by nlinarith [sq_nonneg pi]
    calc
      _ ≤ ((c t : ℝ) / (2 * m : ℕ)) ^ 2 * pi :=
        mul_le_mul_of_nonneg_left hp (sq_nonneg _)
      _ ≤ pi * |(c t : ℝ)| := by nlinarith [mul_le_mul_of_nonneg_left hb hpi0]
  let V := ∑ t : Occ, mean (fun draw : Occ → Fin M => (normalizedNoise m c a t draw) ^ 2)
  have hV : 0 ≤ V := by
    unfold V mean
    positivity
  have hVU : V ≤ pi * liveCap T h ell := by
    calc
      _ ≤ ∑ t, pi * |(c t : ℝ)| := Finset.sum_le_sum (fun t _ => hvar t)
      _ = pi * ∑ t, |(c t : ℝ)| := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hmass hpi0
  have hU : 0 ≤ pi * liveCap T h ell := hV.trans hVU
  obtain ⟨hs, hscalar⟩ := NearCubicGates.Close.Counter.Sampling.WitnessFailure.scalar_tail
    T h ell pi V hT hU hV hVU
  exact (hB (Occ → Fin M) Occ (normalizedNoise m c a) hind hzero hmag
    (fluctuation T h ell pi) hs).trans hscalar

/-- Paper `lem:localize`, paper/paper.tex: the normalized sum is exactly
the actual sampled walk deviation divided by `2m`. -/
theorem normalized_sum_identity {Occ : Type*} [Fintype Occ]
    (m : ℕ) (hm : 0 < m) (c : Occ → ℤ) (M a : ℕ) (draw : Occ → Fin M) :
    (cutoffSum c a draw : ℝ) - (a : ℝ) / M * (∑ t, c t : ℤ) =
      (2 * m : ℕ) * ∑ t, normalizedNoise m c a t draw := by
  have hd : ((2 * m : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (show 2 * m ≠ 0 by omega)
  simp only [cutoffSum, Int.cast_sum, Int.cast_mul, cutoffCoefficient,
    Int.cast_ite, Int.cast_one, Int.cast_zero, normalizedNoise, Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro t _
  field_simp [hd]

/-- Paper `lem:localize`, paper/paper.tex: the stage Bernstein estimate also
covers an EMPTY occurrence bank, where every normalized walk summand is zero. -/
theorem cutoff_stage_tail {Occ : Type} [Fintype Occ] [DecidableEq Occ]
    (hB : Vershynin18_Theorem2_8_4_FiniteBernstein.{0, 0})
    (T h ell : ℝ) (hT : 0 < T) (m : ℕ) (hm : 0 < m)
    (c : Occ → ℤ) (hc : ∀ t, |c t| ≤ (2 * m : ℕ))
    (hmass : (∑ t, |(c t : ℝ)|) ≤ liveCap T h ell)
    (M a : ℕ) (hM : 0 < M) (ha : a ≤ M) :
    mean (fun draw : Occ → Fin M => indicator
      (fluctuation T h ell ((a : ℝ) / M) ≤ |∑ t, normalizedNoise m c a t draw|)) ≤
        2 * Real.exp (-T) := by
  classical
  rcases isEmpty_or_nonempty Occ with hEmpty | hNonempty
  · letI := hEmpty
    letI : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
    have hs : 0 < fluctuation T h ell ((a : ℝ) / M) := by
      unfold fluctuation
      have hz := Real.sqrt_nonneg (2 * T * ((a : ℝ) / M) * liveCap T h ell)
      linarith
    simp only [Finset.univ_eq_empty, Finset.sum_empty, abs_zero, indicator,
      not_le_of_gt hs, if_false]
    simp only [mean_const]
    positivity
  · letI := hNonempty
    exact cutoff_stage_tail_of_nonempty hB T h ell hT m hm c hc hmass M a hM ha

/-- Paper `lem:localize`, paper/paper.tex: the normalized Bernstein estimate
is exactly the ACTUAL stage-deviation bound `|K-pi*Y| >= 2m*s(pi)`. -/
theorem cutoff_deviation_tail {Occ : Type} [Fintype Occ] [DecidableEq Occ]
    (hB : Vershynin18_Theorem2_8_4_FiniteBernstein.{0, 0})
    (T h ell : ℝ) (hT : 0 < T) (m : ℕ) (hm : 0 < m)
    (c : Occ → ℤ) (hc : ∀ t, |c t| ≤ (2 * m : ℕ))
    (hmass : (∑ t, |(c t : ℝ)|) ≤ liveCap T h ell)
    (M a : ℕ) (hM : 0 < M) (ha : a ≤ M) :
    mean (fun draw : Occ → Fin M => indicator
      ((2 * m : ℕ) * fluctuation T h ell ((a : ℝ) / M) ≤
        |(cutoffSum c a draw : ℝ) - (a : ℝ) / M * (∑ t, c t : ℤ)|)) ≤
        2 * Real.exp (-T) := by
  have hd : (0 : ℝ) < (2 * m : ℕ) := by exact_mod_cast (show 0 < 2 * m by omega)
  have heq (draw : Occ → Fin M) :
      ((2 * m : ℕ) * fluctuation T h ell ((a : ℝ) / M) ≤
        |(cutoffSum c a draw : ℝ) - (a : ℝ) / M * (∑ t, c t : ℤ)|) ↔
      fluctuation T h ell ((a : ℝ) / M) ≤ |∑ t, normalizedNoise m c a t draw| := by
    rw [normalized_sum_identity m hm c M a draw, abs_mul, abs_of_pos hd]
    exact mul_le_mul_iff_right₀ hd
  simp_rw [heq]
  exact cutoff_stage_tail hB T h ell hT m hm c hc hmass M a hM ha

end NearQuarticWires.Walks
