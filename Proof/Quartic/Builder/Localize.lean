import Proof.Quartic.Builder.Chain

/-!
# The hypotheses of `lem:localize` on a walk of the cell call

Paper: `lem:localize`, paper/paper.tex; `sec:walks`.

For a column of the cell call, a walk, a pattern and a circuit `j`:
* `Y_{j,σ} = Σ_t c_{j,t}` (`walkSum_eq_sum_contribution`);
* the digits depend only on the multipliers below and the values up to their index
  (`proposedDigit_congr`);
* a walk of mask one has mask one on every edge (`pointMask_of_walkMask`);
* the population of one circuit is at most the population of the call (`population_le_all`);
* with `pop ≤ 16U` on every edge, `|c_t| ≤ 2m` and `Σ_t |c_t| ≤ ℓ_0 = 32mU` (`contribution_bounds`),
  the hypotheses of `Walks.chain_localization_failure_bound`.
-/

set_option autoImplicit false

namespace NearQuarticWires.Builder

open Finset
open NearCubicWires NearCubicWires.WireExponent3_5.Shared
open NearCubicGates.Close.Interfaces

/-- `sec:walks`: a digit `E_r = K_{r+1} - a_r K_r` reads only the multipliers below `r` and the values up
to `r`. -/
theorem proposedDigit_congr (rate rate' value value' : ℕ → ℤ) (r : ℕ)
    (hrate : ∀ i, i < r → rate i = rate' i) (hval : ∀ i, i ≤ r → value i = value' i) :
    NearCubicGates.CountingCore.proposedDigit rate value r =
      NearCubicGates.CountingCore.proposedDigit rate' value' r := by
  cases r with
  | zero => simp [NearCubicGates.CountingCore.proposedDigit, hval 0 le_rfl]
  | succ r =>
    simp only [NearCubicGates.CountingCore.proposedDigit]
    rw [hval (r + 1) le_rfl, hval r (by omega), hrate r (by omega)]

/-- The residual of a circuit is the sum of the mixed residuals of its occurrences, indexed by position. -/
theorem residual_eq_sum_fin (P : StarParams) (gates : List (NormalizedThresholdGate P.n)) (x : BitInput P.n)
    (a b : P.Errors) :
    Cells.residual P gates x a b = ∑ t : Fin gates.length, Cells.delta P gates[t] x a b :=
  (Fin.sum_univ_fun_getElem gates (fun g => Cells.delta P g x a b)).symm

/-- The population of a list of occurrences is at most the population of a longer list. -/
theorem population_le_append_left (P : StarParams) (g₁ g₂ : List (NormalizedThresholdGate P.n)) (x : BitInput P.n)
    (a b : P.Errors) : Cells.population P g₁ x a b ≤ Cells.population P (g₁ ++ g₂) x a b := by
  unfold Cells.population
  rw [List.map_append, List.sum_append]
  exact Nat.le_add_right _ _

theorem population_le_append_right (P : StarParams) (g₁ g₂ : List (NormalizedThresholdGate P.n))
    (x : BitInput P.n) (a b : P.Errors) : Cells.population P g₂ x a b ≤ Cells.population P (g₁ ++ g₂) x a b := by
  unfold Cells.population
  rw [List.map_append, List.sum_append]
  exact Nat.le_add_left _ _

section Walk

variable (c : Call) {p : Cells.Parameters} (hs : Cells.ParameterRules (callInput c) p) (w : List Bool)

/-- The population of the occurrences of one circuit is at most the population of all occurrences of the call. -/
theorem population_gatesOf_le (j : Fin 2) (x : BitInput c.n) (a b : (star c hs).Errors) :
    Cells.population (star c hs) (gatesOf c j) x a b ≤ Cells.population (star c hs) (allGates c) x a b := by
  fin_cases j
  · exact population_le_append_left (star c hs) c.first.gates c.second.gates x a b
  · exact population_le_append_right (star c hs) c.first.gates c.second.gates x a b

/-- `sec:walks`: `Y_{j,σ}(z, w) = Σ_t c_{j,t}(z, w, σ)`. -/
theorem walkSum_eq_sum_contribution (z : Fin (cellCall c hs w).ncol) (j : Fin 2)
    (σ : Cycle.SignPattern Algorithm.traceOrder) (walk : Cycle.Walk hs.seedParameters.N Algorithm.traceOrder) :
    ((cellCall c hs w).column z).Y Algorithm.traceOrder_pos j σ walk =
      ∑ t : Fin (occurrences c j), contribution c hs w z j t σ walk := by
  unfold Walks.WalkData.Y Cycle.walkSum contribution
  change ∑ l, Cycle.signValue (σ l) * Cells.residual (star c hs) (gatesOf c j) (center c hs w z)
      (pattern c hs (Cycle.edge Algorithm.traceOrder_pos walk l).1)
      (pattern c hs (Cycle.edge Algorithm.traceOrder_pos walk l).2) = _
  simp only [residual_eq_sum_fin, Finset.mul_sum]
  rw [Finset.sum_comm]
  rfl

/-- A walk of mask one has mask one on every edge (`lem:cycle`: `mask_w = Π_l mask(e_l)`). -/
theorem pointMask_of_walkMask (z : Fin (cellCall c hs w).ncol)
    (walk : Cycle.Walk hs.seedParameters.N Algorithm.traceOrder) (hw : (cellCall c hs w).walkMask z walk = 1)
    (l : Fin (2 * Algorithm.traceOrder)) :
    (cellCall c hs w).pointMask z (Cycle.edge Algorithm.traceOrder_pos walk l) = 1 := by
  classical
  unfold Algorithm.CellCall.walkMask Walks.walkMaskInt at hw
  unfold Algorithm.CellCall.pointMask
  rcases Mask.mask_zero_or_one (((cellCall c hs w).column z).structural (Cycle.edge Algorithm.traceOrder_pos walk l))
    ((cellCall c hs w).column z).tau
    (((cellCall c hs w).column z).X (Cycle.edge Algorithm.traceOrder_pos walk l)) with h | h
  · exfalso
    rw [Finset.prod_eq_zero (Finset.mem_univ l) h] at hw
    exact absurd hw (by norm_num)
  · exact h

/-- **The hypotheses of `lem:localize` on a walk** (paper/paper.tex): if every edge of the walk has
`pop ≤ 16U`, then every contribution has `|c_t| ≤ 2m` and the total `Σ_t |c_t| ≤ ℓ_0 = 32mU`. -/
theorem contribution_bounds (z : Fin (cellCall c hs w).ncol) (j : Fin 2)
    (σ : Cycle.SignPattern Algorithm.traceOrder) (walk : Cycle.Walk hs.seedParameters.N Algorithm.traceOrder)
    (hpop : ∀ l, population c hs w z (Cycle.edge Algorithm.traceOrder_pos walk l) ≤ 16 * p.U) :
    (∀ t, |contribution c hs w z j t σ walk| ≤ (2 * Algorithm.traceOrder : ℕ)) ∧
      (∑ t, |contribution c hs w z j t σ walk|) ≤ (32 * Algorithm.traceOrder * p.U : ℕ) := by
  have hsigma : ∀ l, |Cycle.signValue (σ l)| ≤ 1 := fun l => (Cycle.abs_signValue (σ l)).le
  let delta : Fin (occurrences c j) → Fin (2 * Algorithm.traceOrder) → ℤ := fun t l =>
    Cells.delta (star c hs) ((gatesOf c j)[(t : ℕ)]'t.isLt) (center c hs w z)
      (pattern c hs (Cycle.edge Algorithm.traceOrder_pos walk l).1)
      (pattern c hs (Cycle.edge Algorithm.traceOrder_pos walk l).2)
  have hc : ∀ t, contribution c hs w z j t σ walk =
      Walks.contribution (fun l => Cycle.signValue (σ l)) delta t := fun t => rfl
  refine ⟨fun t => ?_, ?_⟩
  · rw [hc]
    exact Walks.contribution_abs_le _ delta hsigma (fun t l => Cells.delta_abs_le _ _ _ _ _) t
  · simp only [hc]
    apply Walks.contribution_mass_le_ell0 _ delta hsigma
    intro l
    have hfin := Cells.population_cast_eq_sum_abs (star c hs) (gatesOf c j) (center c hs w z)
      (pattern c hs (Cycle.edge Algorithm.traceOrder_pos walk l).1)
      (pattern c hs (Cycle.edge Algorithm.traceOrder_pos walk l).2)
    have hle := population_gatesOf_le c hs j (center c hs w z)
      (pattern c hs (Cycle.edge Algorithm.traceOrder_pos walk l).1)
      (pattern c hs (Cycle.edge Algorithm.traceOrder_pos walk l).2)
    have h16 := hpop l
    have hsum : (∑ t : Fin (occurrences c j), |delta t l|) = (Cells.population (star c hs) (gatesOf c j)
        (center c hs w z) (pattern c hs (Cycle.edge Algorithm.traceOrder_pos walk l).1)
        (pattern c hs (Cycle.edge Algorithm.traceOrder_pos walk l).2) : ℤ) := hfin.symm
    rw [hsum]
    have : (Cells.population (star c hs) (gatesOf c j) (center c hs w z)
        (pattern c hs (Cycle.edge Algorithm.traceOrder_pos walk l).1)
        (pattern c hs (Cycle.edge Algorithm.traceOrder_pos walk l).2)) ≤ 16 * p.U :=
      hle.trans h16
    exact_mod_cast this

end Walk

end NearQuarticWires.Builder
