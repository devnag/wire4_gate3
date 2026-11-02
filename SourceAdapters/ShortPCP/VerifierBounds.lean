import SourceAdapters.ShortPCP.Verifier

/-!
# P04 item 5: uniform rejection `σ0 ≥ 1/(K1·f^{b1})` for the explicit tuple `(η, κ0, γ, μ) = (2, 4, 0, 1)`

Paper context: proof of `thm:short-pcp-ours`, Step 2, “Base soundness”, and Step 3. A strong single-run
verifier rejects a table at relative distance at least `δ` from its code with probability at least
`δ/(2+K_f)`, where the repaired fixed-tuple bound is `K_f = 16·f^{log₂ c}` (BCGT13,
Lemma 11.10 and Corollary 11.13, ECCC rev. 3, pp.67–68). The fixed tuple has `η = 2`.
Thus `σ0 = 1/(8c_N(2+K_f))`; Step 3 chooses fixed positive integers `K1, b1` with
`1/(K1 f^{b1}) ≤ σ0`. This module makes that choice explicit.

For `(2, 4, 0, 1)`: `c0 = 64`, `a = 520`, `b = 8`, `e1 = log₂(6/5) < e2 = log₂(5/3)`,
`X = a + b/2 + √(b(b+4a))/2 = 524 + √16704/2 ≤ 589 ≤ (6/5)^36`, so `log₂ c = log X / log(6/5) ≤ 36` and
`K_κ ≤ 16κ^36`. With `c_N ≤ K_c·f` this gives `σ0 ≥ 1/(144·K_c·f^37)`: `K1 = 144·K_c`, `b1 = 37`.
The separate `printed_*` lemmas concern the recorded sum-form statement, not the release input.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.ShortPCP

open NearCubicGates.Published.BCGT13

theorem sThree_four : sThree 4 = 2 := by decide
theorem sOne_four : sOne 4 = 1 := by decide
theorem floorHalf_six : floorHalf (4 + 2) = 3 := by decide
theorem ceilHalf_five : ceilHalf (4 + 1) = 3 := by decide

/-- `X = 524 + √16704/2 ≤ 589`. -/
theorem X_le : (520 : ℝ) + 8 / 2 + Real.sqrt (8 * (8 + 4 * 520)) / 2 ≤ 589 := by
  have hs : Real.sqrt (8 * (8 + 4 * 520)) ≤ 130 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  norm_num at hs ⊢
  linarith

/-- **The constant of Theorem 11.1 for `(2, 4, 0, 1)`:** `log₂ c ≤ 36`. -/
theorem logb_constC_le : Real.logb 2 (constC 2 4 0 1) ≤ 36 := by
  have e1 : Real.logb 2 (6 / 5) ≤ Real.logb 2 (5 / 3) :=
    Real.logb_le_logb_of_le (by norm_num) (by norm_num) (by norm_num)
  have e1pos : 0 < Real.logb 2 (6 / 5) := Real.logb_pos (by norm_num) (by norm_num)
  have hX : constC 2 4 0 1 =
      ((520 : ℝ) + 8 / 2 + Real.sqrt (8 * (8 + 4 * 520)) / 2) ^ (1 / Real.logb 2 (6 / 5)) := by
    unfold constC
    simp only [sThree_four, sOne_four, floorHalf_six, ceilHalf_five]
    rw [min_eq_left (by norm_num)]
    norm_num
  set X : ℝ := (520 : ℝ) + 8 / 2 + Real.sqrt (8 * (8 + 4 * 520)) / 2 with hXdef
  have hXpos : 0 < X := by rw [hXdef]; positivity
  rw [hX, Real.logb, Real.log_rpow hXpos, Real.logb, div_le_iff₀ (Real.log_pos (by norm_num))]
  have hl : Real.log X ≤ 36 * Real.log (6 / 5) := by
    have h36 : Real.log ((6 / 5 : ℝ) ^ 36) = 36 * Real.log (6 / 5) := by
      rw [Real.log_pow]; norm_num
    rw [← h36]
    apply Real.log_le_log hXpos
    calc X ≤ 589 := X_le
      _ ≤ (6 / 5 : ℝ) ^ 36 := by norm_num
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl65 : 0 < Real.log (6 / 5) := Real.log_pos (by norm_num)
  rw [one_div_div, div_mul_eq_mul_div, div_le_iff₀ hl65]
  nlinarith

/-- `K_κ ≤ (4/3)(8 + κ^36)` for `κ ≥ 1`, and `K_κ ≥ 0`. -/
theorem printed_soundTerm_le (κ : ℕ) (hκ : 1 ≤ κ) :
    0 ≤ soundTerm 2 4 0 1 κ ∧ soundTerm 2 4 0 1 κ ≤ 4 / 3 * (8 + (κ : ℝ) ^ 36) := by
  have hκr : (1 : ℝ) ≤ κ := by exact_mod_cast hκ
  have hpow : (κ : ℝ) ^ Real.logb 2 (constC 2 4 0 1) ≤ (κ : ℝ) ^ (36 : ℕ) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hκr (by exact_mod_cast logb_constC_le)
  have hnn : 0 ≤ (κ : ℝ) ^ Real.logb 2 (constC 2 4 0 1) := Real.rpow_nonneg (by positivity) _
  unfold soundTerm
  norm_num
  constructor
  · positivity
  · rw [div_le_iff₀ (by norm_num)]
    nlinarith

/-- The minimum in `SubVerifiers.sound`, with `s_R = 1/(1+K)`, `s_H = s_I = 1/(2+K)`, is at least
`δ/(2+K) = 1/(8c_N(2+K))` (proof of `thm:short-pcp-ours`). -/
theorem sigma_ge (K : ℝ) (hK : 0 ≤ K) (cN : ℕ) (hcN : 1 ≤ cN) :
    1 / (8 * cN * (2 + K)) ≤
      min (min (1 / (1 + K) * (1 / (8 * cN))) (1 / (2 + K) * (1 / 8)))
        (min (1 / (2 + K) * (1 / (8 * cN))) (1 / 4)) := by
  have hc : (1 : ℝ) ≤ cN := by exact_mod_cast hcN
  have h2K : 0 < 2 + K := by linarith
  have h1K : 0 < 1 + K := by linarith
  have hδ : 0 < (8 : ℝ) * cN := by positivity
  have heq : 1 / (8 * cN * (2 + K)) = 1 / (2 + K) * (1 / (8 * cN)) := by field_simp
  refine le_min (le_min ?_ ?_) (le_min ?_ ?_)
  · rw [heq]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact one_div_le_one_div_of_le h1K (by linarith)
  · rw [heq]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  · rw [heq]
  · rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith

/-- **Uniform rejection**: with `c_N ≤ K_c·f`, `f ≥ 1`, `K_c ≥ 1`,
`1/(120·K_c·f^37) ≤ σ0`, the rejection guaranteed by `SubVerifiers.sound` for the leaf verifiers at `κ = f`. -/
theorem printed_uniform_rejection (f cN Kc : ℕ) (hf : 1 ≤ f) (hcN : 1 ≤ cN) (hKc : 1 ≤ Kc) (hcNf : cN ≤ Kc * f) :
    1 / ((120 * Kc : ℕ) * (f : ℝ) ^ 37) ≤
      min (min (1 / (1 + soundTerm 2 4 0 1 f) * (1 / (8 * cN))) (1 / (2 + soundTerm 2 4 0 1 f) * (1 / 8)))
        (min (1 / (2 + soundTerm 2 4 0 1 f) * (1 / (8 * cN))) (1 / 4)) := by
  obtain ⟨hK0, hK⟩ := printed_soundTerm_le f hf
  refine le_trans ?_ (sigma_ge _ hK0 cN hcN)
  have hfr : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hc : (1 : ℝ) ≤ cN := by exact_mod_cast hcN
  have hcf : (cN : ℝ) ≤ Kc * f := by exact_mod_cast hcNf
  have hf36 : (1 : ℝ) ≤ (f : ℝ) ^ 36 := one_le_pow₀ hfr
  apply one_div_le_one_div_of_le (by positivity)
  push_cast
  have h1 : 2 + soundTerm 2 4 0 1 f ≤ 15 * (f : ℝ) ^ 36 := by nlinarith
  have h37 : (f : ℝ) ^ 37 = f * f ^ 36 := by ring
  have hpos : 0 ≤ 2 + soundTerm 2 4 0 1 f := by linarith
  calc (8 : ℝ) * cN * (2 + soundTerm 2 4 0 1 f) ≤ 8 * (Kc * f) * (15 * (f : ℝ) ^ 36) := by
        apply mul_le_mul (by linarith) h1 hpos (by positivity)
    _ = 120 * Kc * (f : ℝ) ^ 37 := by rw [h37]; ring

/-- The repaired fixed-tuple term is nonnegative, including at dimension zero. -/
theorem repairedSoundTerm_nonneg (κ : ℕ) : 0 ≤ repairedSoundTerm κ := by
  unfold repairedSoundTerm
  positivity

/-- The repaired bound has `K_κ ≤ 16κ^36` for `κ ≥ 1`. -/
theorem soundTerm_le (κ : ℕ) (hκ : 1 ≤ κ) :
    0 ≤ repairedSoundTerm κ ∧ repairedSoundTerm κ ≤ 16 * (κ : ℝ) ^ 36 := by
  have hκr : (1 : ℝ) ≤ κ := by exact_mod_cast hκ
  have hpow : (κ : ℝ) ^ Real.logb 2 (constC 2 4 0 1) ≤ (κ : ℝ) ^ (36 : ℕ) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hκr (by exact_mod_cast logb_constC_le)
  exact ⟨repairedSoundTerm_nonneg κ, mul_le_mul_of_nonneg_left hpow (by norm_num)⟩

/-- Uniform rejection for the repaired fixed-tuple leaf, with the same exponent 37. -/
theorem uniform_rejection (f cN Kc : ℕ) (hf : 1 ≤ f) (hcN : 1 ≤ cN) (hKc : 1 ≤ Kc)
    (hcNf : cN ≤ Kc * f) :
    1 / ((144 * Kc : ℕ) * (f : ℝ) ^ 37) ≤
      min (min (1 / (1 + repairedSoundTerm f) * (1 / (8 * cN)))
        (1 / (2 + repairedSoundTerm f) * (1 / 8)))
        (min (1 / (2 + repairedSoundTerm f) * (1 / (8 * cN))) (1 / 4)) := by
  obtain ⟨hK0, hK⟩ := soundTerm_le f hf
  refine le_trans ?_ (sigma_ge _ hK0 cN hcN)
  have hfr : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hc : (1 : ℝ) ≤ cN := by exact_mod_cast hcN
  have hcf : (cN : ℝ) ≤ Kc * f := by exact_mod_cast hcNf
  have hf36 : (1 : ℝ) ≤ (f : ℝ) ^ 36 := one_le_pow₀ hfr
  apply one_div_le_one_div_of_le (by positivity)
  push_cast
  have h1 : 2 + repairedSoundTerm f ≤ 18 * (f : ℝ) ^ 36 := by nlinarith
  have h37 : (f : ℝ) ^ 37 = f * f ^ 36 := by ring
  have hpos : 0 ≤ 2 + repairedSoundTerm f := by linarith
  calc (8 : ℝ) * cN * (2 + repairedSoundTerm f) ≤
      8 * (Kc * f) * (18 * (f : ℝ) ^ 36) := by
        apply mul_le_mul (by linarith) h1 hpos (by positivity)
    _ = 144 * Kc * (f : ℝ) ^ 37 := by rw [h37]; ring

/-- The fixed-tuple exponent is nonnegative. -/
theorem logb_constC_nonneg : 0 ≤ Real.logb 2 (constC 2 4 0 1) := by
  have e1 : Real.logb 2 (6 / 5) ≤ Real.logb 2 (5 / 3) :=
    Real.logb_le_logb_of_le (by norm_num) (by norm_num) (by norm_num)
  have e1pos : 0 < Real.logb 2 (6 / 5) := Real.logb_pos (by norm_num) (by norm_num)
  apply Real.logb_nonneg (by norm_num)
  unfold constC
  simp only [sThree_four, sOne_four, floorHalf_six, ceilHalf_five]
  rw [min_eq_left (by norm_num)]
  norm_num
  apply Real.one_le_rpow
  · nlinarith [Real.sqrt_nonneg (16704 : ℝ)]
  · positivity

/-- For positive dimensions, the printed sum term is at most the repaired term. -/
theorem printed_soundTerm_le_repaired (κ : ℕ) (hκ : 1 ≤ κ) :
    soundTerm 2 4 0 1 κ ≤ repairedSoundTerm κ := by
  have hpow : 1 ≤ (κ : ℝ) ^ Real.logb 2 (constC 2 4 0 1) :=
    Real.one_le_rpow (by exact_mod_cast hκ) logb_constC_nonneg
  unfold soundTerm repairedSoundTerm
  norm_num
  nlinarith

/-- Weakening the printed soundness inequality to the repaired denominator also handles `δ ≤ 0`. -/
theorem repaired_soundness_of_printed (κ : ℕ) (hκ : 1 ≤ κ) (offset a δ : ℝ)
    (hoffset : 0 < offset) (hzero : a ≤ 1)
    (hprinted : a ≤ 1 - δ / (offset + soundTerm 2 4 0 1 κ)) :
    a ≤ 1 - δ / (offset + repairedSoundTerm κ) := by
  have hnew := repairedSoundTerm_nonneg κ
  have hold := (printed_soundTerm_le κ hκ).1
  have hle := printed_soundTerm_le_repaired κ hκ
  by_cases hδ : 0 ≤ δ
  · exact hprinted.trans (sub_le_sub_left
      (div_le_div_of_nonneg_left hδ (by linarith) (by linarith)) 1)
  · have : δ / (offset + repairedSoundTerm κ) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
    linarith

end NearCubicGates.Adapters.ShortPCP
