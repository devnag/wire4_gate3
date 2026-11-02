import Proof.Quartic.Builder.Paragraphs
import Proof.Quartic.Mask.StarMass
import Proof.Quartic.Cells.MeanPopulation
import Proof.Quartic.Cells.ParametersReal

/-!
# The deterministic event bounds of the paragraph *Masked mass*

Paper: proof of `prop:complete`, paper/paper.tex; `lem:smaskmass`;
`lem:meanpop`.

* `structuralMass_le`: `Pr_{u,v}[smask = 0] ≤ (W/(d^*(b+1)))² ≤ β/48`, from `Mask.structural_mask_mass` and the
  rules `d^* = ⌊2 X_max U/(3rτ)⌋`, `U ≥ 96 r^{3/2} W/(β n^{3/2})`, `b + 1 > n/(2r)`, `X_max ≥ 3τ√(nr)`.
* `populationMass_le`: for the partition index of `lem:meanpop` (`goodTranslation`),
  `Pr_{z,u,v}[pop > U] ≤ E pop / U ≤ 6 r^{3/2} W/(n^{3/2} U) ≤ β/16`, from `Cells.mean_population` and Markov's
  inequality.
-/

set_option autoImplicit false

namespace NearQuarticWires.Builder

open Finset
open NearCubicWires NearCubicWires.WireExponent3_5.Shared
open NearCubicGates.Close.Interfaces

/-! ### Wire counts -/

/-- The total fan-in of the occurrences of a call is at most its wire count `W` (`def:class`). -/
theorem supportSum_allGates_le (c : Call) : Cells.supportSum (allGates c) ≤ Transfer.callWires c := by
  unfold Cells.supportSum allGates Transfer.callWires Transfer.wires
  rw [List.map_append, List.sum_append]
  have h : ∀ l : List (NormalizedThresholdGate c.n),
      (l.map fun g => (gateSupport g).card).sum ≤ (l.map fun g => Transfer.fanIn g + 1).sum := by
    intro l
    induction l with
    | nil => simp
    | cons g l ih =>
      simp only [List.map_cons, List.sum_cons]
      have : (gateSupport g).card = Transfer.fanIn g := rfl
      omega
  exact Nat.add_le_add (h _) (h _)

/-- `lem:mixed`: summing the coordinate incidences `d_l` counts every occurrence once per coordinate of
its support. -/
theorem incidence_sum_eq {n : ℕ} (gates : List (NormalizedThresholdGate n)) :
    ∑ i, Cells.incidence gates i = Cells.supportSum gates := by
  induction gates with
  | nil => simp [Cells.incidence, Cells.supportSum]
  | cons g gates ih =>
    simp only [Cells.incidence, Cells.supportSum, List.map_cons, List.sum_cons] at ih ⊢
    rw [Finset.sum_add_distrib, ih]
    congr 1
    unfold gateSupport
    rw [Finset.card_filter]

/-! ### Parameter facts -/

section Params

variable {x : Cells.ParameterInput} {p : Cells.Parameters} (hs : Cells.ParameterRules x p)
include hs

theorem tau_pos : 0 < p.tau := by
  have hN := Cells.ParameterRules.N_ge_two hs
  rw [hs.N_eq] at hN
  rw [hs.tau_eq]
  by_contra h
  have hk : p.k = 0 := by omega
  rw [hk] at hN
  simp at hN

theorem tau_le_U : p.tau ≤ p.U := ((Cells.ParameterRules.U_le_iff hs p.U).mp le_rfl).1

theorem U_pos : 0 < p.U := lt_of_lt_of_le (tau_pos hs) (tau_le_U hs)

theorem r_pos : 0 < p.r := by have := (Cells.ParameterRules.r_even_large hs).2; omega

/-- `sec:params` item 3: `X_max² ≥ 9τ²nr`. -/
theorem Xmax_sq : 9 * p.tau ^ 2 * x.n * p.r ≤ p.Xmax ^ 2 :=
  (Cells.ParameterRules.Xmax_le_iff hs p.Xmax).mp le_rfl

/-- `sec:masks`: `X_max ≥ 3rτ` (as `n ≥ r`). -/
theorem three_r_tau_le_Xmax : 3 * p.r * p.tau ≤ p.Xmax := by
  have h := Xmax_sq hs
  have hr : p.r ≤ x.n := by have := hs.r_bound; omega
  have h2 : (3 * p.r * p.tau) ^ 2 ≤ p.Xmax ^ 2 := by
    calc (3 * p.r * p.tau) ^ 2 = 9 * p.tau ^ 2 * p.r * p.r := by ring
      _ ≤ 9 * p.tau ^ 2 * x.n * p.r := by
          apply Nat.mul_le_mul_right
          exact Nat.mul_le_mul_left _ hr
      _ ≤ _ := h
  exact (Nat.pow_le_pow_iff_left (by norm_num)).mp h2

/-- `sec:params` item 3: `U ≥ 96 r^{3/2} W / (β n^{3/2})`. -/
theorem U_lower : (96 : ℝ) * (p.r : ℝ) ^ ((3 : ℝ) / 2) * x.W / ((x.beta : ℝ) * (x.n : ℝ) ^ ((3 : ℝ) / 2)) ≤ p.U :=
  ((Cells.ParameterRules.U_real_le_iff hs p.U).mp le_rfl).2

/-- `sec:masks`: `d^* ≥ X_max U / (3rτ)`, written `X_max U ≤ 3rτ d^*`. -/
theorem dstar_lower : p.Xmax * p.U ≤ 3 * p.r * p.tau * p.dstar := by
  rw [hs.dstar_eq]
  have hr := r_pos hs
  have ht := tau_pos hs
  have hU := U_pos hs
  have hX := three_r_tau_le_Xmax hs
  set D := 3 * p.r * p.tau with hD
  have hDpos : 0 < D := by positivity
  have hmod := Nat.div_add_mod (2 * p.Xmax * p.U) D
  have hlt := Nat.mod_lt (2 * p.Xmax * p.U) hDpos
  have hXU : D ≤ p.Xmax * p.U := by
    calc D ≤ p.Xmax := hX
      _ = p.Xmax * 1 := (mul_one _).symm
      _ ≤ p.Xmax * p.U := Nat.mul_le_mul_left _ hU
  have : 2 * p.Xmax * p.U = 2 * (p.Xmax * p.U) := by ring
  nlinarith

end Params

/-- The arithmetic of the paragraph *Masked mass* (`prop:complete`, paper/paper.tex):
from `X_max U ≤ 3rτ d^*`, `n ≤ 2r(b+1)`, `96 r √r W ≤ U β n √n` and `3τ√n√r ≤ X_max`,
`48 W ≤ β d^* (b+1)`. -/
theorem masked_arith (W β d B X U r τ n : ℝ) (hβ : 0 ≤ β) (hd : 0 ≤ d) (hr : 0 < r) (hτ : 0 < τ)
    (hU : 0 ≤ U) (hn : 0 ≤ n)
    (A1 : X * U ≤ 3 * r * τ * d) (A2 : n ≤ 2 * r * B)
    (A3 : 96 * r * Real.sqrt r * W ≤ U * β * (n * Real.sqrt n))
    (A4 : 3 * τ * Real.sqrt n * Real.sqrt r ≤ X) :
    48 * W ≤ β * d * B := by
  have hsr : Real.sqrt r * Real.sqrt r = r := Real.mul_self_sqrt hr.le
  have hsr0 : 0 ≤ Real.sqrt r := Real.sqrt_nonneg r
  have hsn0 : 0 ≤ Real.sqrt n := Real.sqrt_nonneg n
  -- `6 r² τ · β d B ≥ β (X U) n ≥ 3 τ √r (U β n √n) ≥ 288 τ r² W`
  have e1 : β * (X * U) * n ≤ β * (3 * r * τ * d) * (2 * r * B) := by
    have h1 : β * (X * U) ≤ β * (3 * r * τ * d) := mul_le_mul_of_nonneg_left A1 hβ
    have h0 : 0 ≤ β * (3 * r * τ * d) := by positivity
    calc β * (X * U) * n ≤ β * (3 * r * τ * d) * n := mul_le_mul_of_nonneg_right h1 hn
      _ ≤ β * (3 * r * τ * d) * (2 * r * B) := mul_le_mul_of_nonneg_left A2 h0
  have e2 : 3 * τ * Real.sqrt r * (U * β * (n * Real.sqrt n)) ≤ β * (X * U) * n := by
    have h := mul_le_mul_of_nonneg_right A4 (show 0 ≤ β * U * n by positivity)
    nlinarith
  have e3 : 3 * τ * Real.sqrt r * (96 * r * Real.sqrt r * W) ≤ 3 * τ * Real.sqrt r * (U * β * (n * Real.sqrt n)) :=
    mul_le_mul_of_nonneg_left A3 (by positivity)
  have e4 : 3 * τ * Real.sqrt r * (96 * r * Real.sqrt r * W) = 6 * r ^ 2 * τ * (48 * W) := by
    have : 3 * τ * Real.sqrt r * (96 * r * Real.sqrt r * W) = 288 * τ * r * (Real.sqrt r * Real.sqrt r) * W := by
      ring
    rw [this, hsr]
    ring
  have e5 : β * (3 * r * τ * d) * (2 * r * B) = 6 * r ^ 2 * τ * (β * d * B) := by ring
  have hpos : 0 < 6 * r ^ 2 * τ := by positivity
  have := e3.trans (e2.trans e1)
  rw [e4, e5] at this
  exact le_of_mul_le_mul_left this hpos

/-! ### `Pr[smask = 0] ≤ β/48` -/

section Structural

variable (c : Call) {p : Cells.Parameters} (hs : Cells.ParameterRules (callInput c) p) (w : List Bool)

/-- A sum over the row and column indices of a cell is a sum over pairs of patterns. -/
theorem sum_cell_eq (f : (star c hs).Errors → (star c hs).Errors → ℝ) :
    (∑ u : Fin hs.seedParameters.N, ∑ v : Fin hs.seedParameters.N, f (pattern c hs u) (pattern c hs v)) =
      ∑ uv : (star c hs).Errors × (star c hs).Errors, f uv.1 uv.2 := by
  rw [Fintype.sum_prod_type]
  rw [← Equiv.sum_comp (patternEquiv c hs)]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [← Equiv.sum_comp (patternEquiv c hs)]
  rfl

theorem card_errors_eq : (Fintype.card (star c hs).Errors : ℝ) = hs.seedParameters.N := by
  have h := Cells.ParameterRules.errors_card hs
  rw [← Cells.ParameterRules.seed_N hs] at h
  exact_mod_cast h

/-- `lem:smaskmass`: the structural mass of the cell call is the fraction of discarded pattern pairs. -/
theorem structuralMass_eq : structuralMass c hs w =
    ((univ.filter fun uv : (star c hs).Errors × (star c hs).Errors =>
      Mask.structuralMask ((star c hs).flipSet (star c hs).leftBlock) ((star c hs).flipSet (star c hs).rightBlock)
        (Mask.heavyCoordinates (Cells.incidence (allGates c)) p.dstar) uv.1 uv.2 = false).card : ℝ) /
      (Fintype.card (star c hs).Errors : ℝ) ^ 2 := by
  classical
  unfold structuralMass pointAverage
  have hcol : ((cellCall c hs w).ncol : ℝ) ≠ 0 := by
    have : 0 < (cellCall c hs w).ncol := Nat.two_pow_pos _
    positivity
  have hinner : ∀ z : Fin (cellCall c hs w).ncol,
      (∑ u, ∑ v, ind (((cellCall c hs w).column z).structural (u, v) = false)) =
      ((univ.filter fun uv : (star c hs).Errors × (star c hs).Errors =>
        Mask.structuralMask ((star c hs).flipSet (star c hs).leftBlock)
          ((star c hs).flipSet (star c hs).rightBlock)
          (Mask.heavyCoordinates (Cells.incidence (allGates c)) p.dstar) uv.1 uv.2 = false).card : ℝ) := by
    intro z
    have h := sum_cell_eq c hs (fun a b => ind (Mask.structuralMask ((star c hs).flipSet (star c hs).leftBlock)
      ((star c hs).flipSet (star c hs).rightBlock)
      (Mask.heavyCoordinates (Cells.incidence (allGates c)) p.dstar) a b = false))
    refine h.trans ?_
    rw [Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl fun uv _ => ?_
    unfold ind
    congr 1
  simp only [hinner, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [card_errors_eq c hs]
  exact mul_div_mul_left _ _ hcol

/-- **`Pr_{u,v}[smask = 0] ≤ β/48`** (paper/paper.tex): `lem:smaskmass` with
`W/(d^*(b+1)) ≤ τβ√(nr)/(16 X_max) ≤ β/48`. -/
theorem structuralMass_le : structuralMass c hs w ≤ (c.radius : ℝ) / 48 := by
  classical
  have hr := r_pos hs
  have ht := tau_pos hs
  have hU := U_pos hs
  have hdpos : 0 < p.dstar := by
    rw [hs.dstar_eq]
    apply Nat.div_pos _ (by positivity)
    have hX := three_r_tau_le_Xmax hs
    calc 3 * p.r * p.tau ≤ p.Xmax := hX
      _ ≤ 2 * p.Xmax * p.U := by nlinarith
  have hWsum : ∑ i, Cells.incidence (allGates c) i ≤ Transfer.callWires c := by
    rw [incidence_sum_eq]
    exact supportSum_allGates_le c
  have hmass := Mask.structural_mask_mass (star c hs) (Cells.incidence (allGates c)) p.dstar
    (Transfer.callWires c) hdpos hWsum
  rw [structuralMass_eq c hs w]
  refine hmass.trans ?_
  -- the parameter arithmetic
  have hβ : (0 : ℝ) < c.radius := by exact_mod_cast Cells.ParameterRules.beta_pos hs
  have hβ1 : (c.radius : ℝ) ≤ 1 / 16 := by
    have h : c.radius ≤ 1 / 16 := hs.input_valid.2.2.2.2.2.1
    have h' := (Rat.cast_le (K := ℝ)).mpr h
    push_cast at h'
    exact h'
  have hb : (star c hs).b = p.b := Cells.ParameterRules.star_b hs
  have hB : (0 : ℝ) < ((star c hs).b : ℝ) + 1 := by positivity
  have hd : (0 : ℝ) < p.dstar := by exact_mod_cast hdpos
  have hn : (0 : ℝ) < c.n := by exact_mod_cast Cells.ParameterRules.n_pos hs
  -- `A1`–`A4`
  have A1 : (p.Xmax : ℝ) * p.U ≤ 3 * p.r * p.tau * p.dstar := by exact_mod_cast dstar_lower hs
  have A2 : (c.n : ℝ) ≤ 2 * p.r * (((star c hs).b : ℝ) + 1) := by
    have h := (star c hs).n_add_r_lt
    have h' : ((star c hs).n : ℝ) + (star c hs).r < 2 * (((star c hs).b : ℝ) + 1) * (star c hs).r := by
      exact_mod_cast h
    have hn' : ((star c hs).n : ℝ) = c.n := rfl
    have hr' : ((star c hs).r : ℝ) = p.r := rfl
    rw [hn', hr'] at h'
    have : (0 : ℝ) ≤ p.r := Nat.cast_nonneg _
    nlinarith
  have hr32 : ∀ y : ℝ, 0 ≤ y → y ^ ((3 : ℝ) / 2) = y * Real.sqrt y := by
    intro y hy
    rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' hy (by norm_num)]
    norm_num
  have A3 : 96 * (p.r : ℝ) * Real.sqrt p.r * Transfer.callWires c ≤
      p.U * (c.radius : ℝ) * (c.n * Real.sqrt c.n) := by
    have h : (96 : ℝ) * (p.r : ℝ) ^ ((3 : ℝ) / 2) * (Transfer.callWires c : ℝ) /
        ((c.radius : ℝ) * (c.n : ℝ) ^ ((3 : ℝ) / 2)) ≤ p.U := U_lower hs
    rw [hr32 _ (Nat.cast_nonneg _), hr32 _ (Nat.cast_nonneg _)] at h
    have hden : (0 : ℝ) < (c.radius : ℝ) * ((c.n : ℝ) * Real.sqrt c.n) := by
      have := Real.sqrt_pos.mpr hn
      positivity
    rw [div_le_iff₀ hden] at h
    linarith
  have A4 : 3 * (p.tau : ℝ) * Real.sqrt c.n * Real.sqrt p.r ≤ p.Xmax := by
    have h := Xmax_sq hs
    have h' : (9 : ℝ) * p.tau ^ 2 * c.n * p.r ≤ (p.Xmax : ℝ) ^ 2 := by exact_mod_cast h
    have hl : (3 * (p.tau : ℝ) * Real.sqrt c.n * Real.sqrt p.r) ^ 2 = 9 * p.tau ^ 2 * c.n * p.r := by
      rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _), Real.sq_sqrt (Nat.cast_nonneg _)]
      ring
    rw [← hl] at h'
    have hL0 : 0 ≤ 3 * (p.tau : ℝ) * Real.sqrt c.n * Real.sqrt p.r := by positivity
    have hX0 : (0 : ℝ) ≤ p.Xmax := Nat.cast_nonneg _
    by_contra hlt
    push Not at hlt
    nlinarith
  have key := masked_arith (Transfer.callWires c) (c.radius : ℝ) p.dstar (((star c hs).b : ℝ) + 1) p.Xmax p.U
    p.r p.tau c.n hβ.le hd.le (by exact_mod_cast hr) (by exact_mod_cast ht) (Nat.cast_nonneg _) hn.le
    A1 A2 A3 A4
  -- `(W/(d(b+1)))² ≤ W/(d(b+1)) ≤ β/48`
  have hq : (Transfer.callWires c : ℝ) / ((p.dstar : ℝ) * (((star c hs).b : ℝ) + 1)) ≤ (c.radius : ℝ) / 48 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hq0 : 0 ≤ (Transfer.callWires c : ℝ) / ((p.dstar : ℝ) * (((star c hs).b : ℝ) + 1)) := by positivity
  have hq1 : (Transfer.callWires c : ℝ) / ((p.dstar : ℝ) * (((star c hs).b : ℝ) + 1)) ≤ 1 := by
    linarith
  calc ((Transfer.callWires c : ℝ) / ((p.dstar : ℝ) * (((star c hs).b : ℝ) + 1))) ^ 2
      ≤ (Transfer.callWires c : ℝ) / ((p.dstar : ℝ) * (((star c hs).b : ℝ) + 1)) := by
        rw [sq]
        exact mul_le_of_le_one_left hq0 hq1
    _ ≤ _ := hq

end Structural

/-! ### `Pr[pop > U] ≤ β/16` -/

section Population

variable (c : Call) {p : Cells.Parameters} (hs : Cells.ParameterRules (callInput c) p)

/-- The partition index of `lem:meanpop` (paper/paper.tex): a partition whose mean population is at
most `6 r^{3/2} W / n^{3/2}`. -/
noncomputable def goodTranslation : (star c hs).Translation :=
  Classical.choose (Cells.mean_population (star c hs) (allGates c) (Transfer.callWires c) (supportSum_allGates_le c))

theorem goodTranslation_spec :
    Cells.cellMean (star c hs) (allGates c) (goodTranslation c hs) ≤
      6 * ((star c hs).r * Real.sqrt (star c hs).r) * Transfer.callWires c /
        ((star c hs).n * Real.sqrt (star c hs).n) :=
  Classical.choose_spec
    (Cells.mean_population (star c hs) (allGates c) (Transfer.callWires c) (supportSum_allGates_le c))

variable (w : List Bool)

/-- Columns and cell points of the partition named by the witness enumerate the centers and pattern pairs. -/
theorem sum_columns_eq (f : BitInput c.n → (star c hs).Errors → (star c hs).Errors → ℝ) :
    (∑ z : Fin (2 ^ (c.n - p.k)), ∑ u : Fin hs.seedParameters.N, ∑ v : Fin hs.seedParameters.N,
      f (center c hs w z) (pattern c hs u) (pattern c hs v)) =
    ∑ x ∈ univ.filter ((star c hs).IsCenter (translation c hs w)), ∑ a : (star c hs).Errors,
      ∑ b : (star c hs).Errors, f x a b := by
  classical
  rw [Finset.sum_subtype (univ.filter ((star c hs).IsCenter (translation c hs w)))
    (p := (star c hs).IsCenter (translation c hs w)) (by simp)]
  rw [← Equiv.sum_comp (centerEquiv c hs (translation c hs w))]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [← Equiv.sum_comp (patternEquiv c hs)]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [← Equiv.sum_comp (patternEquiv c hs)]
  rfl

/-- **`Pr_{z,u,v}[pop > U] ≤ β/16`** (paper/paper.tex) for a witness naming the partition of
`lem:meanpop`: Markov's inequality gives `Pr[pop > U] ≤ E pop / U ≤ 6 r^{3/2} W/(n^{3/2} U)`, and
`U ≥ 96 r^{3/2} W/(β n^{3/2})`. -/
theorem populationMass_le (hw : translation c hs w = goodTranslation c hs) :
    populationMass c hs w ≤ (c.radius : ℝ) / 16 := by
  classical
  have hUpos : (0 : ℝ) < p.U := by exact_mod_cast U_pos hs
  -- Markov
  have hmarkov : populationMass c hs w ≤
      pointAverage (cellCall c hs w) (fun z q => (population c hs w z q : ℝ) / p.U) := by
    unfold populationMass pointAverage
    apply div_le_div_of_nonneg_right _ (by positivity)
    refine Finset.sum_le_sum fun z _ => Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => ?_
    unfold ind
    dsimp only
    split_ifs with h
    · rw [le_div_iff₀ hUpos, one_mul]
      exact_mod_cast h.le
    · positivity
  refine hmarkov.trans ?_
  -- the average population is the cell mean of the partition
  have havg : pointAverage (cellCall c hs w) (fun z q => (population c hs w z q : ℝ) / p.U) =
      Cells.cellMean (star c hs) (allGates c) (translation c hs w) / p.U := by
    unfold pointAverage Cells.cellMean
    have hsum := sum_columns_eq c hs w
      (fun x a b => (Cells.population (star c hs) (allGates c) x a b : ℝ) / p.U)
    change (∑ z : Fin (2 ^ (c.n - p.k)), ∑ u : Fin hs.seedParameters.N, ∑ v : Fin hs.seedParameters.N,
      (Cells.population (star c hs) (allGates c) (center c hs w z) (pattern c hs u) (pattern c hs v) : ℝ) / p.U) /
        (((2 ^ (c.n - p.k) : ℕ) : ℝ) * (hs.seedParameters.N : ℝ) ^ 2) = _
    rw [hsum, mul_comm (((2 ^ (c.n - p.k) : ℕ) : ℝ)), ← cube_card c hs]
    simp only [← Finset.sum_div]
    rw [div_div, div_div, mul_comm (p.U : ℝ)]
    rfl
  rw [havg, hw]
  have hmean := goodTranslation_spec c hs
  -- arithmetic
  have hr32 : ∀ y : ℝ, 0 ≤ y → y ^ ((3 : ℝ) / 2) = y * Real.sqrt y := by
    intro y hy
    rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' hy (by norm_num)]
    norm_num
  have hn : (0 : ℝ) < c.n := by exact_mod_cast Cells.ParameterRules.n_pos hs
  have hβ : (0 : ℝ) < c.radius := by exact_mod_cast Cells.ParameterRules.beta_pos hs
  have A3 : 96 * (p.r : ℝ) * Real.sqrt p.r * Transfer.callWires c ≤
      p.U * (c.radius : ℝ) * (c.n * Real.sqrt c.n) := by
    have h : (96 : ℝ) * (p.r : ℝ) ^ ((3 : ℝ) / 2) * (Transfer.callWires c : ℝ) /
        ((c.radius : ℝ) * (c.n : ℝ) ^ ((3 : ℝ) / 2)) ≤ p.U := U_lower hs
    rw [hr32 _ (Nat.cast_nonneg _), hr32 _ (Nat.cast_nonneg _)] at h
    have hden : (0 : ℝ) < (c.radius : ℝ) * ((c.n : ℝ) * Real.sqrt c.n) := by
      have := Real.sqrt_pos.mpr hn
      positivity
    rw [div_le_iff₀ hden] at h
    linarith
  have hsn : (0 : ℝ) < (c.n : ℝ) * Real.sqrt c.n := by
    have := Real.sqrt_pos.mpr hn
    positivity
  change Cells.cellMean (star c hs) (allGates c) (goodTranslation c hs) ≤
    6 * ((p.r : ℝ) * Real.sqrt p.r) * Transfer.callWires c / ((c.n : ℝ) * Real.sqrt c.n) at hmean
  rw [div_le_div_iff₀ hUpos (by norm_num)]
  rw [le_div_iff₀ hsn] at hmean
  nlinarith

end Population

/-! ### The random events -/

/-- **The random part of the proof of `prop:complete`** (paper/paper.tex): a probability
distribution on witness words of length at most `L`, all naming the partition of `lem:meanpop`, under which
* `filter`: `E Pr_{z,u,v}[pop ≤ U, X > τ] ≤ (e/4)^{τ+1} ≤ 3β/64` (`lem:filter`(a));
* `wide`: the expected fraction of columns with a point `smask = 1`, `X ≥ X_max/2` is at most `2^k 2^{-X_max/2} ≤ β/64`
  (`lem:filter`(c));
* `unlocalized`: the expected fraction of columns where the conclusion of `lem:localize` fails on some walk of
  mask one is at most `β/16 + β/8` (`lem:filter`(b) and `lem:localize`).
The selection `𝒮` enters through `X` and the vectors `ξ` through the digits and the final error. -/
structure RandomBounds (c : Call) {p : Cells.Parameters} (hs : Cells.ParameterRules (callInput c) p) (L : ℕ) where
  Ω : Type
  [fintype : Fintype Ω]
  word : Ω → List Bool
  length_le : ∀ ω, (word ω).length ≤ L
  partition : ∀ ω, translation c hs (word ω) = goodTranslation c hs
  P : Ω → ℝ
  nonneg : ∀ ω, 0 ≤ P ω
  total : ∑ ω, P ω = 1
  filter : ∑ ω, P ω * lightFilteredMass c hs (word ω) ≤ 3 * (c.radius : ℝ) / 64
  wide : ∑ ω, P ω * wideFraction c hs (word ω) ≤ (c.radius : ℝ) / 64
  unlocalized : ∑ ω, P ω * unlocalizedFraction c hs (word ω) ≤ 3 * (c.radius : ℝ) / 16

attribute [instance] RandomBounds.fintype

/-- An expectation of a quantity bounded by a constant is bounded by the constant. -/
theorem expectation_le_const {Ω : Type} [Fintype Ω] (P f : Ω → ℝ) (hP : ∀ ω, 0 ≤ P ω) (h1 : ∑ ω, P ω = 1)
    (b : ℝ) (hf : ∀ ω, f ω ≤ b) : ∑ ω, P ω * f ω ≤ b := by
  calc ∑ ω, P ω * f ω ≤ ∑ ω, P ω * b := Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (hf ω) (hP ω)
    _ = b := by rw [← Finset.sum_mul, h1, one_mul]

/-- The event bounds of the proof of `prop:complete` from its random part: the structural and population events
are deterministic (`structuralMass_le`, `populationMass_le`). -/
noncomputable def eventBounds_of_random (c : Call) {p : Cells.Parameters} (hs : Cells.ParameterRules (callInput c) p)
    (L : ℕ) (R : RandomBounds c hs L) : EventBounds c hs L where
  Ω := R.Ω
  word := R.word
  length_le := R.length_le
  P := R.P
  nonneg := R.nonneg
  total := R.total
  structural := expectation_le_const R.P _ R.nonneg R.total _ fun ω => structuralMass_le c hs (R.word ω)
  population := expectation_le_const R.P _ R.nonneg R.total _ fun ω =>
    populationMass_le c hs (R.word ω) (R.partition ω)
  filter := R.filter
  wide := R.wide
  unlocalized := R.unlocalized

/-- **The probabilistic part of `prop:complete` from its random part**: `ParagraphBounds L` holds as soon as every
call meeting the hypotheses of `prop:complete` has a witness law with the three random bounds. -/
theorem paragraphBounds_of_random (L : ℕ → ℕ)
    (hR : ∀ (c : Call) (p : Cells.Parameters) (hs : Cells.ParameterRules (callInput c) p), Shaped c →
      CompletenessConditions c p → Nonempty (RandomBounds c hs (L c.n))) :
    ParagraphBounds L :=
  paragraphBounds_of_events L fun c p hs hc hcond => by
    obtain ⟨R⟩ := hR c p hs hc hcond
    exact ⟨eventBounds_of_random c hs (L c.n) R⟩

end NearQuarticWires.Builder
