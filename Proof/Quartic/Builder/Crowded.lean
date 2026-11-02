import Proof.Quartic.Builder.Law

/-!
# Event (ii) of the paragraph *Uncertified columns*: crowded points

Paper: proof of `prop:complete`, paper/paper.tex; `lem:filter`(b).

Event (ii) of a column is a point with `mask = 1` and `pop > 16U` (`Crowded`). Under the law of `lem:filter`, a
point with `pop ≥ 16U` keeps `X ≤ τ` with probability at most `e^{-9τ/8}` (`Mask.selection_large_population`); a
union bound over the `N² = 2^k` points of a cell gives `2^k e^{-9τ/8} ≤ 2^{k-τ} ≤ β/16` (`crowdedMass_le`).

A column without event (ii) has `pop ≤ 16U` on every edge of every walk of mask one, the hypothesis of
`lem:localize`; what remains of the paragraph is event (iii), the failure of the conclusion of `lem:localize` on a
column without event (ii) (`StrayBound`, at most `β/8`), and `counterMath4_of_stray` assembles the counter from it.
-/

set_option autoImplicit false

namespace NearQuarticWires.Builder

open Finset MeasureTheory
open NearCubicWires NearCubicWires.WireExponent3_5.Shared
open NearCubicGates.Close.Interfaces

section Crowded

variable (c : Call) {p : Cells.Parameters} (hs : Cells.ParameterRules (callInput c) p)

/-- Event (ii) of the paragraph *Uncertified columns* (`prop:complete`, paper/paper.tex) for column `z`: some point
with `mask = 1` has `pop > 16U`. -/
def Crowded (w : List Bool) (z : Fin (cellCall c hs w).ncol) : Prop :=
  ∃ q, (cellCall c hs w).pointMask z q = 1 ∧ 16 * p.U < population c hs w z q

/-- The fraction of columns with event (ii). -/
noncomputable def crowdedFraction (w : List Bool) : ℝ := columnFraction (cellCall c hs w) (Crowded c hs w)

/-- The fraction of columns with event (iii) and without event (ii): the conclusion of `lem:localize` fails on some
walk of mask one, although `pop ≤ 16U` at every point of mask one. -/
noncomputable def strayFraction (w : List Bool) : ℝ :=
  columnFraction (cellCall c hs w) fun z => ¬ Localized c hs w z ∧ ¬ Crowded c hs w z

/-- A column where the conclusion of `lem:localize` fails has event (ii), or event (iii) without event (ii). -/
theorem unlocalizedFraction_le_split (w : List Bool) :
    unlocalizedFraction c hs w ≤ crowdedFraction c hs w + strayFraction c hs w := by
  classical
  unfold unlocalizedFraction crowdedFraction strayFraction columnFraction
  rw [← add_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun z _ => ?_
  by_cases hL : Localized c hs w z
  · have : ind (¬ Localized c hs w z) = 0 := by unfold ind; rw [if_neg (not_not.mpr hL)]
    rw [this]
    exact add_nonneg (ind_nonneg _) (ind_nonneg _)
  · rw [ind_of _ hL]
    by_cases hC : Crowded c hs w z
    · have h1 : ind (Crowded c hs w z) = 1 := ind_of _ hC
      linarith [ind_nonneg ((fun z => ¬ Localized c hs w z ∧ ¬ Crowded c hs w z) z)]
    · have h1 : ind ((fun z => ¬ Localized c hs w z ∧ ¬ Crowded c hs w z) z) = 1 := ind_of _ ⟨hL, hC⟩
      linarith [ind_nonneg (Crowded c hs w z)]

/-- `lem:filter`(b) at one point (paper/paper.tex): if `pop ≥ 16U`, then
`Pr_𝒮[X ≤ τ] ≤ e^{-9τ/8}`. -/
theorem crowded_point (x : BitInput c.n) (a b : (star c hs).Errors)
    (hpop : 16 * p.U ≤ Cells.population (star c hs) (allGates c) x a b) :
    (Mask.selectionLaw (Fin (allGates c).length) (selectionRate c hs)).real
      {s | Mask.sampledPopulation (activeAt c hs x a b) s ≤ p.tau} ≤ Real.exp (-9 * (p.tau : ℝ) / 8) := by
  apply Mask.selection_large_population
  have hU : (0 : ℝ) < p.U := by exact_mod_cast U_pos hs
  have hcard : 16 * (p.U : ℝ) ≤ ((activeAt c hs x a b).card : ℝ) := by
    rw [activeAt_card]
    exact_mod_cast hpop
  change 4 * (p.tau : ℝ) ≤ ((activeAt c hs x a b).card : ℝ) * ((p.tau : ℝ) / (4 * (p.U : ℝ)))
  calc 4 * (p.tau : ℝ) = (16 * (p.U : ℝ)) * ((p.tau : ℝ) / (4 * (p.U : ℝ))) := by field_simp; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard (by positivity)

include hs in
/-- The tail arithmetic of event (ii) (`prop:complete`, paper/paper.tex): `N² e^{-9τ/8} ≤ 2^k 2^{-τ} ≤ β/16`, as
`τ = k + ⌈lg(16/β)⌉`. -/
theorem crowded_tail_le :
    (hs.seedParameters.N : ℝ) ^ 2 * Real.exp (-9 * (p.tau : ℝ) / 8) ≤ (c.radius : ℝ) / 16 := by
  have hβ : (0 : ℝ) < c.radius := by exact_mod_cast Cells.ParameterRules.beta_pos hs
  have hN2 : (hs.seedParameters.N : ℝ) ^ 2 = 2 ^ p.k := by
    have h := Cells.ParameterRules.N_square hs
    rw [← Cells.ParameterRules.seed_N hs] at h
    exact_mod_cast h
  rw [hN2]
  -- `e^{-9τ/8} ≤ 2^{-τ}`
  have he : (2 : ℝ) ≤ Real.exp (9 / 8) := by
    have := Real.add_one_le_exp (9 / 8 : ℝ)
    linarith
  have hexp : Real.exp (-9 * (p.tau : ℝ) / 8) = 1 / Real.exp (9 / 8) ^ p.tau := by
    rw [← Real.exp_nat_mul, one_div, ← Real.exp_neg]
    congr 1
    ring
  have h2τ : (2 : ℝ) ^ p.tau ≤ Real.exp (9 / 8) ^ p.tau := pow_le_pow_left₀ (by norm_num) he _
  -- `2^τ = 2^k 2^{⌈lg(16/β)⌉}` and `2^{⌈lg(16/β)⌉} ≥ 16/β`
  set L := Cells.ParameterArithmetic.ceilLog 2 (16 / c.radius)
  have hτ : p.tau = p.k + L := hs.tau_eq
  have hL : 16 / (c.radius : ℝ) ≤ 2 ^ L := by
    have := Cells.ParameterArithmetic.le_pow_ceilLog (by norm_num : 1 < 2) (16 / c.radius)
    have h' : ((16 / c.radius : ℚ) : ℝ) ≤ (((2 ^ L : ℕ) : ℚ) : ℝ) := (Rat.cast_le (K := ℝ)).mpr this
    calc (16 / (c.radius : ℝ)) = ((16 / c.radius : ℚ) : ℝ) := by push_cast; ring
      _ ≤ _ := h'
      _ = 2 ^ L := by push_cast; ring
  rw [hexp]
  have hpos : (0 : ℝ) < Real.exp (9 / 8) ^ p.tau := by positivity
  rw [mul_one_div, div_le_iff₀ hpos]
  calc (2 : ℝ) ^ p.k = (c.radius : ℝ) / 16 * (2 ^ p.k * (16 / (c.radius : ℝ))) := by field_simp
    _ ≤ (c.radius : ℝ) / 16 * (2 ^ p.k * 2 ^ L) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hL (by positivity)) (by positivity)
    _ = (c.radius : ℝ) / 16 * 2 ^ p.tau := by rw [hτ, pow_add]
    _ ≤ (c.radius : ℝ) / 16 * Real.exp (9 / 8) ^ p.tau := mul_le_mul_of_nonneg_left h2τ (by positivity)

/-- **Event (ii) of the paragraph *Uncertified columns*** (paper/paper.tex): for a witness law whose
words all name the partition `σ` and whose selection marginal is the law of `lem:filter`, the expected fraction of
columns with a point `mask = 1`, `pop > 16U` is at most `β/16`. -/
theorem crowdedMass_le {Ω : Type} [Fintype Ω] (P : Ω → ℝ) (hP : ∀ ω, 0 ≤ P ω) (word : Ω → List Bool)
    (sel : Ω → Fin (allGates c).length → Bool) (hsel : ∀ ω, selection c (p := p) (word ω) = sel ω)
    (σ : (star c hs).Translation) (hpart : ∀ ω, translation c hs (word ω) = σ)
    (hmarg : ∀ s, ∑ ω, P ω * ind (sel ω = s) = selectionWeight c hs s) :
    ∑ ω, P ω * crowdedFraction c hs (word ω) ≤ (c.radius : ℝ) / 16 := by
  classical
  set N := hs.seedParameters.N
  let bad : Fin (2 ^ (c.n - p.k)) → Sampler.Cell N → (Fin (allGates c).length → Bool) → Prop :=
    fun z q s => 16 * p.U < Cells.population (star c hs) (allGates c) (centerOf c hs σ z)
        (pattern c hs q.1) (pattern c hs q.2) ∧
      Mask.sampledPopulation (activeAt c hs (centerOf c hs σ z) (pattern c hs q.1) (pattern c hs q.2)) s ≤
        p.tau
  have hunion : ∀ ω, crowdedFraction c hs (word ω) ≤
      (∑ z : Fin (2 ^ (c.n - p.k)), ∑ q : Sampler.Cell N, ind (bad z q (sel ω))) / ((2 ^ (c.n - p.k) : ℕ) : ℝ) := by
    intro ω
    unfold crowdedFraction columnFraction
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    refine Finset.sum_le_sum fun z _ => ?_
    by_cases hw : Crowded c hs (word ω) z
    · obtain ⟨q, hq1, hq2⟩ := hw
      rw [ind_of _ ⟨q, hq1, hq2⟩]
      have hb : bad z q (sel ω) := by
        have hX : ((cellCall c hs (word ω)).column z).X q ≤ p.tau := by
          unfold Algorithm.CellCall.pointMask Mask.mask at hq1
          by_contra h
          rw [if_neg (fun h' => h h'.2)] at hq1
          exact absurd hq1 (by norm_num)
        rw [X_eq_sampledPopulation, hsel ω] at hX
        change 16 * p.U < Cells.population (star c hs) (allGates c) (center c hs (word ω) z) _ _ at hq2
        change Mask.sampledPopulation (activeAt c hs (center c hs (word ω) z) _ _) _ ≤ p.tau at hX
        unfold center at hq2 hX
        rw [hpart ω] at hq2 hX
        exact ⟨hq2, hX⟩
      calc (1 : ℝ) = ind (bad z q (sel ω)) := (ind_of _ hb).symm
        _ ≤ ∑ q', ind (bad z q' (sel ω)) :=
          Finset.single_le_sum (f := fun q' => ind (bad z q' (sel ω))) (fun q' _ => ind_nonneg _)
            (Finset.mem_univ q)
    · have : ind (Crowded c hs (word ω) z) = 0 := by unfold ind; rw [if_neg hw]
      rw [this]
      exact Finset.sum_nonneg fun q _ => ind_nonneg _
  have hpoint : ∀ z q, ∑ s, selectionWeight c hs s * ind (bad z q s) ≤ Real.exp (-9 * (p.tau : ℝ) / 8) := by
    intro z q
    by_cases hm : 16 * p.U < Cells.population (star c hs) (allGates c) (centerOf c hs σ z)
        (pattern c hs q.1) (pattern c hs q.2)
    · have hsum : ∑ s, selectionWeight c hs s * ind (bad z q s) =
          (Mask.selectionLaw (Fin (allGates c).length) (selectionRate c hs)).real
            (↑(univ.filter fun s => bad z q s)) := by
        rw [← sum_measureReal_singleton, Finset.sum_filter]
        refine Finset.sum_congr rfl fun s _ => ?_
        unfold selectionWeight ind
        split_ifs <;> simp
      rw [hsum]
      refine le_trans (measureReal_mono ?_ (measure_ne_top _ _))
        (crowded_point c hs (centerOf c hs σ z) (pattern c hs q.1) (pattern c hs q.2) hm.le)
      intro s hs'
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hs'
      exact hs'.2
    · have h0 : ∀ s, ind (bad z q s) = 0 := fun s => by unfold ind; rw [if_neg (fun h => hm h.1)]
      simp only [h0, mul_zero, Finset.sum_const_zero]
      positivity
  have hcol : (0 : ℝ) < ((2 ^ (c.n - p.k) : ℕ) : ℝ) := by exact_mod_cast Nat.two_pow_pos _
  calc ∑ ω, P ω * crowdedFraction c hs (word ω)
      ≤ ∑ ω, P ω * ((∑ z : Fin (2 ^ (c.n - p.k)), ∑ q : Sampler.Cell N, ind (bad z q (sel ω))) /
          ((2 ^ (c.n - p.k) : ℕ) : ℝ)) :=
        Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (hunion ω) (hP ω)
    _ = (∑ z : Fin (2 ^ (c.n - p.k)), ∑ q : Sampler.Cell N, ∑ s, selectionWeight c hs s * ind (bad z q s)) /
          ((2 ^ (c.n - p.k) : ℕ) : ℝ) := by
        have e1 : ∀ ω, P ω * ((∑ z : Fin (2 ^ (c.n - p.k)), ∑ q : Sampler.Cell N, ind (bad z q (sel ω))) /
            ((2 ^ (c.n - p.k) : ℕ) : ℝ)) =
            (P ω * ∑ z : Fin (2 ^ (c.n - p.k)), ∑ q : Sampler.Cell N, ind (bad z q (sel ω))) /
            ((2 ^ (c.n - p.k) : ℕ) : ℝ) := fun ω => by ring
        rw [Finset.sum_congr rfl (fun ω _ => e1 ω), ← Finset.sum_div]
        congr 1
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun q _ => ?_
        exact expect_selection c hs P sel hmarg (fun s => ind (bad z q s))
    _ ≤ (∑ _z : Fin (2 ^ (c.n - p.k)), ∑ _q : Sampler.Cell N, Real.exp (-9 * (p.tau : ℝ) / 8)) /
          ((2 ^ (c.n - p.k) : ℕ) : ℝ) := by
        apply div_le_div_of_nonneg_right _ hcol.le
        exact Finset.sum_le_sum fun z _ => Finset.sum_le_sum fun q _ => hpoint z q
    _ = (N : ℝ) ^ 2 * Real.exp (-9 * (p.tau : ℝ) / 8) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Fintype.card_prod,
          Sampler.Cell, NearCubicWires.WireExponent3_5.Shared.Cell]
        field_simp
        push_cast
        ring
    _ ≤ (c.radius : ℝ) / 16 := crowded_tail_le c hs

/-- **Event (iii) of the paragraph *Uncertified columns*** (paper/paper.tex), the part of the proof
of `prop:complete` that rests on `lem:localize`: there is a law `Q` of the vectors `ξ` such that, for the partition
of `lem:meanpop` and `𝒮` independent of `ξ` with the law of `lem:filter`, the expected fraction of columns without
event (ii) where the conclusion of `lem:localize` fails on some walk of mask one is at most `β/8`
(`2^{mk} 4^m · 2 · 2J e^{-T} ≤ β/8`). -/
def StrayBound : Prop :=
  ∃ Q : (Fin p.J → Fin (allGates c).length → Bool) → ℝ, (∀ ξ, 0 ≤ Q ξ) ∧ ∑ ξ, Q ξ = 1 ∧
    ∑ s, ∑ ξ, selectionWeight c hs s * Q ξ *
      strayFraction c hs (witnessWord c (goodIndex c hs) s ξ) ≤ (c.radius : ℝ) / 8

/-- The localization bound from event (iii): event (ii) is proved (`crowdedMass_le`). -/
theorem localizationBound_of_stray (h : StrayBound c hs) : LocalizationBound c hs := by
  classical
  obtain ⟨Q, hQ0, hQ1, hstray⟩ := h
  refine ⟨Q, hQ0, hQ1, ?_⟩
  let Ω := (Fin (allGates c).length → Bool) × (Fin p.J → Fin (allGates c).length → Bool)
  let P : Ω → ℝ := fun ω => selectionWeight c hs ω.1 * Q ω.2
  let word : Ω → List Bool := fun ω => witnessWord c (goodIndex c hs) ω.1 ω.2
  have hP0 : ∀ ω, 0 ≤ P ω := fun ω => mul_nonneg (selectionWeight_nonneg c hs _) (hQ0 _)
  have hmarg : ∀ s, ∑ ω : Ω, P ω * ind (ω.1 = s) = selectionWeight c hs s := by
    intro s
    rw [Fintype.sum_prod_type, Finset.sum_eq_single s]
    · show ∑ x, selectionWeight c hs s * Q x * ind ((s, x).1 = s) = selectionWeight c hs s
      rw [Finset.sum_congr rfl (fun x _ => by rw [ind_of ((s, x).1 = s) rfl, mul_one]), ← Finset.mul_sum, hQ1,
        mul_one]
    · intro s' _ hs'
      refine Finset.sum_eq_zero fun ξ _ => ?_
      have : ind ((s', ξ).1 = s) = 0 := by unfold ind; rw [if_neg hs']
      rw [this, mul_zero]
    · simp
  have hcrowd := crowdedMass_le c hs P hP0 word Prod.fst (fun ω => selection_witnessWord c _ _ _)
    (goodTranslation c hs) (fun ω => translation_goodIndex c hs _ _) hmarg
  rw [Fintype.sum_prod_type] at hcrowd
  have hsplit : ∀ s ξ, selectionWeight c hs s * Q ξ *
      unlocalizedFraction c hs (witnessWord c (goodIndex c hs) s ξ) ≤
      selectionWeight c hs s * Q ξ * crowdedFraction c hs (witnessWord c (goodIndex c hs) s ξ) +
      selectionWeight c hs s * Q ξ * strayFraction c hs (witnessWord c (goodIndex c hs) s ξ) := by
    intro s ξ
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left (unlocalizedFraction_le_split c hs _)
      (mul_nonneg (selectionWeight_nonneg c hs s) (hQ0 ξ))
  calc ∑ s, ∑ ξ, selectionWeight c hs s * Q ξ * unlocalizedFraction c hs (witnessWord c (goodIndex c hs) s ξ)
      ≤ ∑ s, ∑ ξ, (selectionWeight c hs s * Q ξ * crowdedFraction c hs (witnessWord c (goodIndex c hs) s ξ) +
        selectionWeight c hs s * Q ξ * strayFraction c hs (witnessWord c (goodIndex c hs) s ξ)) :=
        Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun ξ _ => hsplit s ξ
    _ = (∑ s, ∑ ξ, selectionWeight c hs s * Q ξ * crowdedFraction c hs (witnessWord c (goodIndex c hs) s ξ)) +
        ∑ s, ∑ ξ, selectionWeight c hs s * Q ξ * strayFraction c hs (witnessWord c (goodIndex c hs) s ξ) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun s _ => Finset.sum_add_distrib
    _ ≤ (c.radius : ℝ) / 16 + (c.radius : ℝ) / 8 := add_le_add hcrowd hstray
    _ = 3 * (c.radius : ℝ) / 16 := by ring

end Crowded

/-- **`thm:counter`(i),(ii) for `Builder.value`, with every part of `prop:complete` proved except event (iii)**:
the hypotheses are the cap of `lem:asymptotics` and, for every call meeting the hypotheses of `prop:complete`, the
bound on event (iii) (`lem:localize` for some law of the vectors `ξ`). -/
noncomputable def counterMath4_of_stray {B1 B2 : ℕ} (hcap : QuarticCap B1 B2)
    (hstray : ∀ (c : Call) (p : Cells.Parameters) (hs : Cells.ParameterRules (callInput c) p), Shaped c →
      CompletenessConditions c p → StrayBound c hs) :
    CounterMath4 B1 B2 :=
  counterMath4_of_localization hcap fun c p hs hc hcond => localizationBound_of_stray c hs (hstray c p hs hc hcond)

end NearQuarticWires.Builder
