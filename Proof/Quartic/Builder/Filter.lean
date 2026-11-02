import Proof.Quartic.Builder.Bounds
import Proof.Quartic.Mask.Concrete
import Proof.Quartic.Mask.Sampling
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# `lem:filter`(a) for the cell call, averaged over a witness law

Paper: proof of `prop:complete`, paragraph *Masked mass*, paper/paper.tex; `lem:filter`(a).

When the witness words of a law all name the same partition and the selection `𝒮` they carry has the law of
`lem:filter` (each occurrence label independently with rate `π_0 = τ/(4U)`, `Mask.selectionLaw`), the expected mass
`E Pr_{z,u,v}[pop ≤ U, X > τ]` is at most `(e/4)^{τ+1}` (`Mask.selection_small_population` at every point), and
`(e/4)^{τ+1} ≤ 3β/64` because `2^τ ≥ (16/β)²` (`filterMass_le`).
-/

set_option autoImplicit false

namespace NearQuarticWires.Builder

open Finset MeasureTheory
open NearCubicWires NearCubicWires.WireExponent3_5.Shared
open NearCubicGates.Close.Interfaces

section Filter

variable (c : Call) {p : Cells.Parameters} (hs : Cells.ParameterRules (callInput c) p)

/-- `sec:masks`, paper/paper.tex: the rate `π_0 = τ/(4U)` of the selection `𝒮`. -/
noncomputable def selectionRate : unitInterval := Mask.filterRate p.tau p.U (U_pos hs) (tau_le_U hs)

/-- The probability of one selection under the law of `lem:filter` (independent bits of rate `π_0`). -/
noncomputable def selectionWeight (s : Fin (allGates c).length → Bool) : ℝ :=
  (Mask.selectionLaw (Fin (allGates c).length) (selectionRate c hs)).real {s}

/-- The occurrence labels with nonzero mixed residual at a point (`lem:filter`). -/
def activeAt (x : BitInput c.n) (a b : (star c hs).Errors) : Finset (Fin (allGates c).length) :=
  univ.filter fun i => Cells.delta (star c hs) ((allGates c)[(i : ℕ)]'i.isLt) x a b ≠ 0

/-- The population is the number of active labels. -/
theorem activeAt_card (x : BitInput c.n) (a b : (star c hs).Errors) :
    (activeAt c hs x a b).card = Cells.population (star c hs) (allGates c) x a b := by
  rw [Cells.population_eq_sum_fin]
  simp only [Cells.delta_natAbs_eq_indicator, activeAt, Finset.card_filter]
  rfl

/-- `def:mask`: `X = Σ_{(j,i) ∈ 𝒮} |Δ_{j,i}|` is the number of selected active labels. -/
theorem X_eq_sampledPopulation (w : List Bool) (z : Fin (cellCall c hs w).ncol)
    (q : Sampler.Cell (cellCall c hs w).seed.N) :
    ((cellCall c hs w).column z).X q =
      Mask.sampledPopulation (activeAt c hs (center c hs w z) (pattern c hs q.1) (pattern c hs q.2))
        (selection c (p := p) w) := by
  classical
  unfold Mask.sampledPopulation activeAt
  rw [Finset.filter_filter, Finset.card_filter]
  change (∑ i : Fin (allGates c).length, if selection c (p := p) w i then
    (Cells.delta (star c hs) ((allGates c)[(i : ℕ)]'i.isLt) (center c hs w z) (pattern c hs q.1)
      (pattern c hs q.2)).natAbs else 0) = _
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Cells.delta_natAbs_eq_indicator]
  by_cases hsel : selection c (p := p) w i = true <;> by_cases hd : Cells.delta (star c hs)
    ((allGates c)[(i : ℕ)]'i.isLt) (center c hs w z) (pattern c hs q.1) (pattern c hs q.2) = 0 <;>
    simp [hsel, hd]

/-- `lem:filter`(a) at one point (paper/paper.tex): if `pop ≤ U`, then
`Pr_𝒮[X > τ] ≤ (e/4)^{τ+1}`. -/
theorem filter_point (x : BitInput c.n) (a b : (star c hs).Errors)
    (hpop : Cells.population (star c hs) (allGates c) x a b ≤ p.U) :
    (Mask.selectionLaw (Fin (allGates c).length) (selectionRate c hs)).real
      {s | p.tau < Mask.sampledPopulation (activeAt c hs x a b) s} ≤ (Real.exp 1 / 4) ^ (p.tau + 1) := by
  apply Mask.selection_small_population
  have hU : (0 : ℝ) < p.U := by exact_mod_cast U_pos hs
  have hcard : ((activeAt c hs x a b).card : ℝ) ≤ p.U := by
    rw [activeAt_card]
    exact_mod_cast hpop
  change ((activeAt c hs x a b).card : ℝ) * ((p.tau : ℝ) / (4 * (p.U : ℝ))) ≤ _
  calc ((activeAt c hs x a b).card : ℝ) * ((p.tau : ℝ) / (4 * (p.U : ℝ))) ≤
      (p.U : ℝ) * ((p.tau : ℝ) / (4 * (p.U : ℝ))) := mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = (p.tau : ℝ) / 4 := by field_simp

include hs in
/-- The tail arithmetic of the paragraph *Masked mass* (`prop:complete`, paper/paper.tex): with `2^k ≥ 16/β`,
`τ = k + ⌈lg(16/β)⌉` gives `2^τ ≥ (16/β)²`, hence `(e/4)^τ ≤ 2^{-τ/2} ≤ β/16` and `(e/4)^{τ+1} ≤ 3β/64`. -/
theorem filter_tail_le (hk : (16 : ℚ) / c.radius ≤ 2 ^ p.k) :
    (Real.exp 1 / 4) ^ (p.tau + 1) ≤ 3 * (c.radius : ℝ) / 64 := by
  have hβ : (0 : ℝ) < c.radius := by exact_mod_cast Cells.ParameterRules.beta_pos hs
  have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have he0 : 0 < Real.exp 1 := Real.exp_pos 1
  set q := Real.exp 1 / 4 with hq
  have hq0 : 0 ≤ q := by positivity
  have hq34 : q ≤ 3 / 4 := by rw [hq]; linarith
  have hq2 : q ^ 2 ≤ 1 / 2 := by
    rw [hq, div_pow]
    have : Real.exp 1 ^ 2 < 8 := by nlinarith
    linarith
  -- `2^τ ≥ (16/β)²`
  have hτ : (16 / (c.radius : ℝ)) ^ 2 ≤ 2 ^ p.tau := by
    rw [hs.tau_eq, pow_add, sq]
    have h1 : (16 / (c.radius : ℝ)) ≤ 2 ^ p.k := by
      have := (Rat.cast_le (K := ℝ)).mpr hk
      push_cast at this
      exact this
    have h2 : (16 / (c.radius : ℝ)) ≤ 2 ^ Cells.ParameterArithmetic.ceilLog 2 (16 / c.radius) := by
      have := Cells.ParameterArithmetic.le_pow_ceilLog (by norm_num : 1 < 2) (16 / c.radius)
      have h' : ((16 / c.radius : ℚ) : ℝ) ≤
          (((2 ^ Cells.ParameterArithmetic.ceilLog 2 (16 / c.radius) : ℕ) : ℚ) : ℝ) :=
        (Rat.cast_le (K := ℝ)).mpr this
      calc (16 / (c.radius : ℝ)) = ((16 / c.radius : ℚ) : ℝ) := by push_cast; ring
        _ ≤ _ := h'
        _ = 2 ^ Cells.ParameterArithmetic.ceilLog 2 (16 / c.radius) := by push_cast; ring
    have h0 : 0 ≤ 16 / (c.radius : ℝ) := by positivity
    exact mul_le_mul h1 h2 h0 (by positivity)
  -- `q^τ ≤ β/16`, from `(q^τ)² = (q²)^τ ≤ 2^{-τ} ≤ (β/16)²`
  have hqτ : q ^ p.tau ≤ (c.radius : ℝ) / 16 := by
    have hsq : (q ^ p.tau) ^ 2 ≤ ((c.radius : ℝ) / 16) ^ 2 := by
      rw [← pow_mul, mul_comm, pow_mul]
      calc (q ^ 2) ^ p.tau ≤ (1 / 2 : ℝ) ^ p.tau := pow_le_pow_left₀ (by positivity) hq2 _
        _ = 1 / 2 ^ p.tau := by rw [one_div_pow]
        _ ≤ 1 / (16 / (c.radius : ℝ)) ^ 2 := by
            apply one_div_le_one_div_of_le (by positivity) hτ
        _ = ((c.radius : ℝ) / 16) ^ 2 := by field_simp
    have h0 : 0 ≤ q ^ p.tau := by positivity
    have h1 : 0 ≤ (c.radius : ℝ) / 16 := by positivity
    nlinarith [sq_nonneg (q ^ p.tau - (c.radius : ℝ) / 16), sq_nonneg (q ^ p.tau + (c.radius : ℝ) / 16)]
  calc q ^ (p.tau + 1) = q ^ p.tau * q := pow_succ q p.tau
    _ ≤ ((c.radius : ℝ) / 16) * (3 / 4) := mul_le_mul hqτ hq34 hq0 (by positivity)
    _ = 3 * (c.radius : ℝ) / 64 := by ring

/-- The average over all cells of the partition `σ`, with columns `Fin n_col` and cell points `Fin N × Fin N`. -/
noncomputable def cellAverage (f : Fin (2 ^ (c.n - p.k)) → Fin hs.seedParameters.N → Fin hs.seedParameters.N → ℝ) :
    ℝ :=
  (∑ z, ∑ u, ∑ v, f z u v) / (((2 ^ (c.n - p.k) : ℕ) : ℝ) * (hs.seedParameters.N : ℝ) ^ 2)

/-- The point mass of `{pop ≤ U, X > τ}` at a column of the partition `σ` and a selection `s`. -/
noncomputable def lightFilteredAt (σ : (star c hs).Translation) (s : Fin (allGates c).length → Bool)
    (z : Fin (2 ^ (c.n - p.k))) (u v : Fin hs.seedParameters.N) : ℝ :=
  ind (Cells.population (star c hs) (allGates c) (centerOf c hs σ z) (pattern c hs u) (pattern c hs v) ≤ p.U
    ∧ p.tau < Mask.sampledPopulation
      (activeAt c hs (centerOf c hs σ z) (pattern c hs u) (pattern c hs v)) s)

theorem lightFilteredMass_eq (w : List Bool) :
    lightFilteredMass c hs w = cellAverage c hs (lightFilteredAt c hs (translation c hs w) (selection c (p := p) w)) := by
  unfold lightFilteredMass pointAverage cellAverage lightFilteredAt
  congr 1
  refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
  dsimp only
  rw [X_eq_sampledPopulation]
  rfl

/-- **`E Pr_{z,u,v}[pop ≤ U, X > τ] ≤ 3β/64`** (paper/paper.tex), for a witness law whose words
all name the partition `σ` and whose selection marginal is the law of `lem:filter`. -/
theorem filterMass_le {Ω : Type} [Fintype Ω] (P : Ω → ℝ) (word : Ω → List Bool)
    (sel : Ω → Fin (allGates c).length → Bool) (hsel : ∀ ω, selection c (p := p) (word ω) = sel ω)
    (σ : (star c hs).Translation) (hpart : ∀ ω, translation c hs (word ω) = σ)
    (hmarg : ∀ s, ∑ ω, P ω * ind (sel ω = s) = selectionWeight c hs s)
    (hk : (16 : ℚ) / c.radius ≤ 2 ^ p.k) :
    ∑ ω, P ω * lightFilteredMass c hs (word ω) ≤ 3 * (c.radius : ℝ) / 64 := by
  classical
  simp only [lightFilteredMass_eq, hsel, hpart]
  -- exchange the expectation and the average
  have hswap : ∑ ω, P ω * cellAverage c hs (lightFilteredAt c hs σ (sel ω)) =
      cellAverage c hs (fun z u v => ∑ ω, P ω * lightFilteredAt c hs σ (sel ω) z u v) := by
    unfold cellAverage
    simp only [Finset.mul_sum, ← mul_div_assoc, ← Finset.sum_div]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.sum_comm]
  rw [hswap]
  -- at each point, the expectation is a probability under the selection law
  have hpoint : ∀ z u v, ∑ ω, P ω * lightFilteredAt c hs σ (sel ω) z u v ≤ 3 * (c.radius : ℝ) / 64 := by
    intro z u v
    have hgroup : ∑ ω, P ω * lightFilteredAt c hs σ (sel ω) z u v =
        ∑ s, selectionWeight c hs s * lightFilteredAt c hs σ s z u v := by
      have : ∀ ω, P ω * lightFilteredAt c hs σ (sel ω) z u v =
          ∑ s, P ω * ind (sel ω = s) * lightFilteredAt c hs σ s z u v := by
        intro ω
        rw [Finset.sum_eq_single (sel ω)]
        · rw [ind_of _ rfl, mul_one]
        · intro s _ hs'
          have : ind (sel ω = s) = 0 := by unfold ind; rw [if_neg (Ne.symm hs')]
          rw [this, mul_zero, zero_mul]
        · simp
      simp only [this]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [← Finset.sum_mul, hmarg]
    rw [hgroup]
    set x := (centerOf c hs σ z)
    by_cases hpop : Cells.population (star c hs) (allGates c) x (pattern c hs u) (pattern c hs v) ≤ p.U
    · have hsum : ∑ s, selectionWeight c hs s * lightFilteredAt c hs σ s z u v =
          (Mask.selectionLaw (Fin (allGates c).length) (selectionRate c hs)).real
            (↑(univ.filter fun s => p.tau < Mask.sampledPopulation
              (activeAt c hs x (pattern c hs u) (pattern c hs v)) s)) := by
        rw [← sum_measureReal_singleton, Finset.sum_filter]
        refine Finset.sum_congr rfl fun s _ => ?_
        unfold lightFilteredAt selectionWeight ind
        by_cases ht : p.tau < Mask.sampledPopulation (activeAt c hs x (pattern c hs u) (pattern c hs v)) s
        · rw [if_pos ⟨hpop, ht⟩, if_pos ht, mul_one]
        · rw [if_neg (fun h => ht h.2), if_neg ht, mul_zero]
      rw [hsum]
      have hset : (↑(univ.filter fun s => p.tau < Mask.sampledPopulation
          (activeAt c hs x (pattern c hs u) (pattern c hs v)) s) : Set (Fin (allGates c).length → Bool)) =
          {s | p.tau < Mask.sampledPopulation (activeAt c hs x (pattern c hs u) (pattern c hs v)) s} := by
        ext s
        simp
      rw [hset]
      exact (filter_point c hs x _ _ hpop).trans (filter_tail_le c hs hk)
    · have h0 : ∀ s, lightFilteredAt c hs σ s z u v = 0 := by
        intro s
        unfold lightFilteredAt ind
        rw [if_neg (fun h => hpop h.1)]
      simp only [h0, mul_zero, Finset.sum_const_zero]
      have : (0 : ℝ) < c.radius := by exact_mod_cast Cells.ParameterRules.beta_pos hs
      positivity
  -- the average of values at most `3β/64`
  unfold cellAverage
  have hden : (0 : ℝ) < ((2 ^ (c.n - p.k) : ℕ) : ℝ) * (hs.seedParameters.N : ℝ) ^ 2 := by
    have h1 : (0 : ℝ) < ((2 ^ (c.n - p.k) : ℕ) : ℝ) := by exact_mod_cast Nat.two_pow_pos _
    have h2 : (0 : ℝ) < (hs.seedParameters.N : ℝ) := by
      have := Cells.ParameterRules.N_ge_two hs
      rw [← Cells.ParameterRules.seed_N hs] at this
      exact_mod_cast (show 0 < hs.seedParameters.N by omega)
    positivity
  rw [div_le_iff₀ hden]
  calc (∑ z, ∑ u, ∑ v, ∑ ω, P ω * lightFilteredAt c hs σ (sel ω) z u v) ≤
      ∑ _z : Fin (2 ^ (c.n - p.k)), ∑ _u : Fin hs.seedParameters.N, ∑ _v : Fin hs.seedParameters.N,
        3 * (c.radius : ℝ) / 64 :=
        Finset.sum_le_sum fun z _ => Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => hpoint z u v
    _ = 3 * (c.radius : ℝ) / 64 * (((2 ^ (c.n - p.k) : ℕ) : ℝ) * (hs.seedParameters.N : ℝ) ^ 2) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

/-- Averaging a function of the selection over a law whose selection marginal is `selectionWeight`. -/
theorem expect_selection {Ω : Type} [Fintype Ω] (P : Ω → ℝ) (sel : Ω → Fin (allGates c).length → Bool)
    (hmarg : ∀ s, ∑ ω, P ω * ind (sel ω = s) = selectionWeight c hs s) (g : (Fin (allGates c).length → Bool) → ℝ) :
    ∑ ω, P ω * g (sel ω) = ∑ s, selectionWeight c hs s * g s := by
  classical
  have : ∀ ω, P ω * g (sel ω) = ∑ s, P ω * ind (sel ω = s) * g s := by
    intro ω
    rw [Finset.sum_eq_single (sel ω)]
    · rw [ind_of _ rfl, mul_one]
    · intro s _ hs'
      have : ind (sel ω = s) = 0 := by unfold ind; rw [if_neg (Ne.symm hs')]
      rw [this, mul_zero, zero_mul]
    · simp
  simp only [this]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← Finset.sum_mul, hmarg]

/-- `lem:filter`(c) at one point (paper/paper.tex): if `smask(u,v) = 1`, then
`Pr_𝒮[X ≥ X_max/2] ≤ 2^{-X_max/2}`, since `pop < (r/2) d^*` (`lem:smaskpop`) and `π_0 (r/2) d^* ≤ X_max/12`. -/
theorem structural_point (x : BitInput c.n) (a b : (star c hs).Errors)
    (hmask : Mask.structuralMask ((star c hs).flipSet (star c hs).leftBlock)
      ((star c hs).flipSet (star c hs).rightBlock)
      (Mask.heavyCoordinates (Cells.incidence (allGates c)) p.dstar) a b = true) :
    (Mask.selectionLaw (Fin (allGates c).length) (selectionRate c hs)).real
      {s | (p.Xmax : ℝ) / 2 ≤ (Mask.sampledPopulation (activeAt c hs x a b) s : ℝ)} ≤
        (2 : ℝ) ^ (-(p.Xmax : ℝ) / 2) := by
  apply Mask.selection_structural_population
  have hdpos : 0 < p.dstar := by
    rw [hs.dstar_eq]
    apply Nat.div_pos _ (by have := r_pos hs; have := tau_pos hs; positivity)
    have hX := three_r_tau_le_Xmax hs
    have hU := U_pos hs
    calc 3 * p.r * p.tau ≤ p.Xmax := hX
      _ ≤ 2 * p.Xmax * p.U := by nlinarith
  have hpop := Mask.star_structural_population_lt (star c hs) (allGates c) p.dstar hdpos x a b hmask
  have hr2 : 2 * (p.r / 2) = p.r := by
    obtain ⟨m, hm⟩ := (Cells.ParameterRules.r_even_large hs).1
    omega
  refine Mask.structural_mean_le _ p.tau p.U p.Xmax (p.r / 2) p.dstar (U_pos hs) (tau_le_U hs) ?_ ?_
  · rw [activeAt_card]
    exact hpop.le
  · rw [hr2, hs.dstar_eq]
    calc 3 * p.r * p.tau * (2 * p.Xmax * p.U / (3 * p.r * p.tau)) ≤ 2 * p.Xmax * p.U := Nat.mul_div_le _ _

/-- The tail arithmetic of event (i) (`prop:complete`, paper/paper.tex): with `X_max ≥ 2k + 2 lg(64/β)`,
`N² · 2^{-X_max/2} = 2^k 2^{-X_max/2} ≤ β/64`. -/
theorem wide_tail_le (hX : (2 : ℚ) ^ (2 * p.k) * (64 / c.radius) ^ 2 ≤ 2 ^ p.Xmax) :
    (hs.seedParameters.N : ℝ) ^ 2 * (2 : ℝ) ^ (-(p.Xmax : ℝ) / 2) ≤ (c.radius : ℝ) / 64 := by
  have hβ : (0 : ℝ) < c.radius := by exact_mod_cast Cells.ParameterRules.beta_pos hs
  have hN2 : (hs.seedParameters.N : ℝ) ^ 2 = 2 ^ p.k := by
    have h := Cells.ParameterRules.N_square hs
    rw [← Cells.ParameterRules.seed_N hs] at h
    exact_mod_cast h
  rw [hN2]
  set y := (2 : ℝ) ^ (-(p.Xmax : ℝ) / 2) with hy
  have hy0 : 0 < y := by positivity
  have hysq : y ^ 2 * 2 ^ p.Xmax = 1 := by
    rw [hy, ← Real.rpow_natCast ((2 : ℝ) ^ (-(p.Xmax : ℝ) / 2)) 2, ← Real.rpow_mul (by norm_num),
      ← Real.rpow_natCast (2 : ℝ) p.Xmax, ← Real.rpow_add (by norm_num)]
    push_cast
    ring_nf
    simp
  have hXr : (2 : ℝ) ^ (2 * p.k) * (64 / (c.radius : ℝ)) ^ 2 ≤ 2 ^ p.Xmax := by
    have h := (Rat.cast_le (K := ℝ)).mpr hX
    push_cast at h
    exact h
  -- `(2^k y)² ≤ (β/64)²`
  have hsq : ((2 : ℝ) ^ p.k * y) ^ 2 ≤ ((c.radius : ℝ) / 64) ^ 2 := by
    have h2X : (0 : ℝ) < 2 ^ p.Xmax := by positivity
    have e1 : ((2 : ℝ) ^ p.k * y) ^ 2 = (2 : ℝ) ^ (2 * p.k) / 2 ^ p.Xmax := by
      rw [eq_div_iff h2X.ne', mul_pow, ← pow_mul, mul_comm p.k 2, mul_assoc, hysq, mul_one]
    rw [e1, div_le_iff₀ h2X]
    have e2 : ((c.radius : ℝ) / 64) ^ 2 * (64 / (c.radius : ℝ)) ^ 2 = 1 := by
      field_simp
    calc (2 : ℝ) ^ (2 * p.k) = (2 : ℝ) ^ (2 * p.k) * (((c.radius : ℝ) / 64) ^ 2 * (64 / (c.radius : ℝ)) ^ 2) := by
          rw [e2, mul_one]
      _ = ((c.radius : ℝ) / 64) ^ 2 * ((2 : ℝ) ^ (2 * p.k) * (64 / (c.radius : ℝ)) ^ 2) := by ring
      _ ≤ ((c.radius : ℝ) / 64) ^ 2 * 2 ^ p.Xmax := mul_le_mul_of_nonneg_left hXr (by positivity)
  have h0 : 0 ≤ (2 : ℝ) ^ p.k * y := by positivity
  have h1 : 0 ≤ (c.radius : ℝ) / 64 := by positivity
  nlinarith [sq_nonneg ((2 : ℝ) ^ p.k * y - (c.radius : ℝ) / 64),
    sq_nonneg ((2 : ℝ) ^ p.k * y + (c.radius : ℝ) / 64)]

/-- **Event (i) of the paragraph *Uncertified columns*** (paper/paper.tex): for a witness law whose
words all name the partition `σ` and whose selection marginal is the law of `lem:filter`, the expected fraction of
columns with a point `smask = 1`, `X ≥ X_max/2` is at most `β/64` (a union bound over the `N²` points of the cell
and `lem:filter`(c)). -/
theorem wideMass_le {Ω : Type} [Fintype Ω] (P : Ω → ℝ) (hP : ∀ ω, 0 ≤ P ω) (word : Ω → List Bool)
    (sel : Ω → Fin (allGates c).length → Bool) (hsel : ∀ ω, selection c (p := p) (word ω) = sel ω)
    (σ : (star c hs).Translation) (hpart : ∀ ω, translation c hs (word ω) = σ)
    (hmarg : ∀ s, ∑ ω, P ω * ind (sel ω = s) = selectionWeight c hs s)
    (hX : (2 : ℚ) ^ (2 * p.k) * (64 / c.radius) ^ 2 ≤ 2 ^ p.Xmax) :
    ∑ ω, P ω * wideFraction c hs (word ω) ≤ (c.radius : ℝ) / 64 := by
  classical
  set N := hs.seedParameters.N
  -- the bad event at a point, as a function of the selection
  let bad : Fin (2 ^ (c.n - p.k)) → Sampler.Cell N → (Fin (allGates c).length → Bool) → Prop :=
    fun z q s => Mask.structuralMask ((star c hs).flipSet (star c hs).leftBlock)
      ((star c hs).flipSet (star c hs).rightBlock)
      (Mask.heavyCoordinates (Cells.incidence (allGates c)) p.dstar) (pattern c hs q.1) (pattern c hs q.2) = true ∧
      p.Xmax < 2 * Mask.sampledPopulation
        (activeAt c hs (centerOf c hs σ z) (pattern c hs q.1) (pattern c hs q.2)) s
  -- union bound over the points of the cell
  have hunion : ∀ ω, wideFraction c hs (word ω) ≤
      (∑ z : Fin (2 ^ (c.n - p.k)), ∑ q : Sampler.Cell N, ind (bad z q (sel ω))) / ((2 ^ (c.n - p.k) : ℕ) : ℝ) := by
    intro ω
    unfold wideFraction columnFraction
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    refine Finset.sum_le_sum fun z _ => ?_
    by_cases hw : Wide c hs (word ω) z
    · obtain ⟨q, hq1, hq2⟩ := hw
      rw [ind_of _ ⟨q, hq1, hq2⟩]
      have hb : bad z q (sel ω) := by
        refine ⟨hq1, ?_⟩
        have := X_eq_sampledPopulation c hs (word ω) z q
        rw [this, hsel ω] at hq2
        change p.Xmax < 2 * Mask.sampledPopulation (activeAt c hs (center c hs (word ω) z) _ _) _ at hq2
        unfold center at hq2
        rw [hpart ω] at hq2
        exact hq2
      calc (1 : ℝ) = ind (bad z q (sel ω)) := (ind_of _ hb).symm
        _ ≤ ∑ q', ind (bad z q' (sel ω)) :=
          Finset.single_le_sum (f := fun q' => ind (bad z q' (sel ω))) (fun q' _ => ind_nonneg _)
            (Finset.mem_univ q)
    · have : ind (Wide c hs (word ω) z) = 0 := by unfold ind; rw [if_neg hw]
      rw [this]
      exact Finset.sum_nonneg fun q _ => ind_nonneg _
  -- each point: the selection-law probability of the bad event
  have hpoint : ∀ z q, ∑ s, selectionWeight c hs s * ind (bad z q s) ≤ (2 : ℝ) ^ (-(p.Xmax : ℝ) / 2) := by
    intro z q
    by_cases hm : Mask.structuralMask ((star c hs).flipSet (star c hs).leftBlock)
        ((star c hs).flipSet (star c hs).rightBlock)
        (Mask.heavyCoordinates (Cells.incidence (allGates c)) p.dstar) (pattern c hs q.1) (pattern c hs q.2) = true
    · have hsum : ∑ s, selectionWeight c hs s * ind (bad z q s) =
          (Mask.selectionLaw (Fin (allGates c).length) (selectionRate c hs)).real
            (↑(univ.filter fun s => bad z q s)) := by
        rw [← sum_measureReal_singleton, Finset.sum_filter]
        refine Finset.sum_congr rfl fun s _ => ?_
        unfold selectionWeight ind
        split_ifs <;> simp
      rw [hsum]
      refine le_trans (measureReal_mono ?_ (measure_ne_top _ _))
        (structural_point c hs (centerOf c hs σ z) (pattern c hs q.1) (pattern c hs q.2) hm)
      intro s hs'
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hs'
      show (p.Xmax : ℝ) / 2 ≤ (Mask.sampledPopulation
        (activeAt c hs (centerOf c hs σ z) (pattern c hs q.1) (pattern c hs q.2)) s : ℝ)
      have := hs'.2
      have h' : (p.Xmax : ℝ) < 2 * (Mask.sampledPopulation
          (activeAt c hs (centerOf c hs σ z) (pattern c hs q.1) (pattern c hs q.2)) s : ℝ) := by
        exact_mod_cast this
      linarith
    · have h0 : ∀ s, ind (bad z q s) = 0 := fun s => by unfold ind; rw [if_neg (fun h => hm h.1)]
      simp only [h0, mul_zero, Finset.sum_const_zero]
      positivity
  -- assemble
  have hcol : (0 : ℝ) < ((2 ^ (c.n - p.k) : ℕ) : ℝ) := by exact_mod_cast Nat.two_pow_pos _
  calc ∑ ω, P ω * wideFraction c hs (word ω)
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
    _ ≤ (∑ _z : Fin (2 ^ (c.n - p.k)), ∑ _q : Sampler.Cell N, (2 : ℝ) ^ (-(p.Xmax : ℝ) / 2)) /
          ((2 ^ (c.n - p.k) : ℕ) : ℝ) := by
        apply div_le_div_of_nonneg_right _ hcol.le
        exact Finset.sum_le_sum fun z _ => Finset.sum_le_sum fun q _ => hpoint z q
    _ = (N : ℝ) ^ 2 * (2 : ℝ) ^ (-(p.Xmax : ℝ) / 2) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Fintype.card_prod,
          Sampler.Cell, NearCubicWires.WireExponent3_5.Shared.Cell]
        field_simp
        push_cast
        ring
    _ ≤ (c.radius : ℝ) / 64 := wide_tail_le c hs hX

end Filter

end NearQuarticWires.Builder
