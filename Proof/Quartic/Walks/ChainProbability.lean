import Proof.Quartic.Walks.Sampling

set_option autoImplicit false

namespace NearQuarticWires.Walks

open scoped BigOperators
open NearCubicGates.FiniteAverages NearCubicGates.PublishedSources.Witness
open NearCubicGates.PublicSamplingRates NearCubicGates.NestedRateChain

/-- Paper `lem:localize`, paper/paper.tex: the SAME finite draw realizes the
public nested sample at every stage, at its literal rational cutoff. -/
noncomputable def publicSampledSum {Occ : Type*} [Fintype Occ]
    (T h ell : ℝ) (c : Occ → ℤ)
    (draw : Occ → Fin (denominator T h ell)) (r : ℕ) : ℤ :=
  cutoffSum c (product (initialRatio T h ell) r) draw

/-- Paper `lem:localize`, paper/paper.tex: the COMPLETE localization event
for the actual sampled walk sums. `J` is the zero-based last stage. -/
def LocalizationEvent {Occ : Type*} [Fintype Occ] (T h ell : ℝ)
    (m J : ℕ) (c : Occ → ℤ) (draw : Occ → Fin (denominator T h ell)) : Prop :=
  (∀ r : Fin (J + 1),
    |((NearCubicGates.CountingCore.proposedDigit (chainFactor T h ell)
      (publicSampledSum T h ell c draw) r.val : ℤ) : ℝ)| ≤ (m : ℝ) * h) ∧
  |(finalError T h ell (publicSampledSum T h ell c draw) (∑ t, c t) J : ℝ)| ≤
    172 * m * (product (initialRatio T h ell) J : ℝ) * T * liveCap T h ell / h

/-- Paper `lem:localize`, paper/paper.tex: the finite union estimate used
for all actual stages. It bounds strict failure by the weak Bernstein event. -/
theorem stage_union_bound {Samples Stages : Type*} [Fintype Samples] [Fintype Stages]
    (error threshold : Stages → Samples → ℝ) :
    mean (fun draw => indicator (¬ ∀ r, |error r draw| ≤ threshold r draw)) ≤
      ∑ r, mean (fun draw => indicator (threshold r draw ≤ |error r draw|)) := by
  classical
  calc
    _ ≤ mean (fun draw => ∑ r, indicator (threshold r draw ≤ |error r draw|)) := by
      apply mean_le_mean
      intro draw
      by_cases hall : ∀ r, |error r draw| ≤ threshold r draw
      · have hz : indicator (¬ ∀ r, |error r draw| ≤ threshold r draw) = 0 := by
          exact if_neg (not_not_intro hall)
        rw [hz]
        apply Finset.sum_nonneg
        intro r _
        unfold indicator
        split_ifs <;> norm_num
      · obtain ⟨r, hr⟩ := not_forall.mp hall
        have hweak : threshold r draw ≤ |error r draw| := (lt_of_not_ge hr).le
        have hsingle := Finset.single_le_sum
          (fun s (_ : s ∈ (Finset.univ : Finset Stages)) =>
            show 0 ≤ indicator (threshold s draw ≤ |error s draw|) from by
              unfold indicator; split_ifs <;> norm_num)
          (Finset.mem_univ r)
        have hone : indicator (¬ ∀ r, |error r draw| ≤ threshold r draw) = 1 := if_pos hall
        have hweakone : indicator (threshold r draw ≤ |error r draw|) = 1 := if_pos hweak
        rw [hone]
        rw [hweakone] at hsingle
        exact hsingle
    _ = _ := NearCubicGates.Close.Counter.Sampling.WitnessFailure.mean_sum _

/-- Paper `lem:localize`, paper/paper.tex: the full finite rational nested
sampler fails with probability at most `2*(J+1)*exp(-T)`. This is precisely
the paper's `2*J_paper*exp(-T)`, since `J_paper=J+1`. All independent,
centered, bounded and variance premises were proved for the actual draw;
the ONLY trusted input here is the published finite Bernstein statement. -/
theorem chain_localization_failure_bound {Occ : Type} [Fintype Occ] [DecidableEq Occ]
    (hB : Vershynin18_Theorem2_8_4_FiniteBernstein.{0, 0})
    (T h ell : ℝ) (hT : 0 < T) (hh : 64 * T ≤ h) (m : ℕ) (hm : 0 < m)
    (c : Occ → ℤ) (hc : ∀ t, |c t| ≤ (2 * m : ℕ))
    (hmass : (∑ t, |(c t : ℝ)|) ≤ liveCap T h ell) (J : ℕ)
    (hactive : ∀ r, r < J → rateRatio (initialRatio T h ell) r < 1 / 256)
    (hstopped : 1 / 256 ≤ rateRatio (initialRatio T h ell) J) :
    mean (fun draw : Occ → Fin (denominator T h ell) =>
      indicator (¬ LocalizationEvent T h ell m J c draw)) ≤
        2 * (J + 1 : ℕ) * Real.exp (-T) := by
  classical
  have hM := (denominator_bounds T h ell hT hh).1
  letI : Nonempty (Fin (denominator T h ell)) := ⟨⟨0, hM⟩⟩
  let error (r : Fin (J + 1)) (draw : Occ → Fin (denominator T h ell)) : ℝ :=
    (publicSampledSum T h ell c draw r.val : ℝ) - rate T h ell r.val * (∑ t, c t : ℤ)
  let threshold (r : Fin (J + 1)) (_draw : Occ → Fin (denominator T h ell)) : ℝ :=
    (2 * m : ℕ) * fluctuation T h ell (rate T h ell r.val)
  have htail (r : Fin (J + 1)) :
      mean (fun draw : Occ → Fin (denominator T h ell) =>
        indicator (threshold r draw ≤ |error r draw|)) ≤ 2 * Real.exp (-T) := by
    have ht := cutoff_deviation_tail hB T h ell hT m hm c hc hmass
      (denominator T h ell) (product (initialRatio T h ell) r.val) hM
      (product_fits_denominator T h ell hT hh r.val)
    rw [← rate_is_rational_product T h ell hT hh r.val] at ht
    exact ht
  have hY : |((∑ t, c t : ℤ) : ℝ)| ≤ (2 * m : ℕ) * liveCap T h ell := by
    have hs : |((∑ t, c t : ℤ) : ℝ)| ≤ liveCap T h ell := by
      rw [Int.cast_sum]
      exact (Finset.abs_sum_le_sum_abs _ _).trans hmass
    have hden : (1 : ℝ) ≤ (2 * m : ℕ) := by exact_mod_cast (show 1 ≤ 2 * m by omega)
    have hcap : 0 ≤ liveCap T h ell :=
      (abs_nonneg ((∑ t, c t : ℤ) : ℝ)).trans hs
    nlinarith [mul_le_mul_of_nonneg_right hden hcap]
  have hgood (draw : Occ → Fin (denominator T h ell))
      (hstage : ∀ r, |error r draw| ≤ threshold r draw) :
      LocalizationEvent T h ell m J c draw := by
    have hs (r : ℕ) (hr : r ≤ J) :
        |(publicSampledSum T h ell c draw r : ℝ) - rate T h ell r * (∑ t, c t : ℤ)| ≤
          (2 * m : ℕ) * fluctuation T h ell (rate T h ell r) := hstage ⟨r, by omega⟩
    have hb := localize_on_stage_event T h ell hT hh m (publicSampledSum T h ell c draw)
      (∑ t, c t) J hactive hstopped hY hs
    exact ⟨fun r => hb.1 r.val (by omega), hb.2⟩
  calc
    _ ≤ mean (fun draw => indicator (¬ ∀ r, |error r draw| ≤ threshold r draw)) := by
      apply mean_le_mean
      intro draw
      by_cases hs : ∀ r, |error r draw| ≤ threshold r draw
      · simp [indicator, hs, hgood draw hs]
      · simp only [indicator, hs, not_false_eq_true, if_true]
        split_ifs <;> norm_num
    _ ≤ ∑ r : Fin (J + 1), mean (fun draw =>
        indicator (threshold r draw ≤ |error r draw|)) := stage_union_bound error threshold
    _ ≤ ∑ _r : Fin (J + 1), (2 * Real.exp (-T)) := Finset.sum_le_sum (fun r _ => htail r)
    _ = _ := by simp; ring

end NearQuarticWires.Walks
