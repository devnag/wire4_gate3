import Proof.Quartic.Builder.CellCall

/-!
# The cell-level facts of `prop:sound` for the constructed cell call

Paper: `imp:partition`, paper/paper.tex; `lem:identity`; `sec:cycle`;
`sec:params`.

For the cell call built from a call, its selected parameters and a witness (`Builder.cellCall`), this file proves
the hypotheses of `Algorithm.CellCall.prop_sound_of_parameters` other than `lem:fourier`:
* `usesParameters`: the cell call uses the parameters `Cells.toAlgorithmParameters` (field by field);
* `two_le_N`, `N_le_Q`: `2 ≤ N ≤ Q`;
* `residual_le` (`lem:identity`, `|R_j| ≤ G_j`) and `residual_zero` (`R_j = 0` for a circuit outside `𝒥`);
* `partitionAverage` (`imp:partition`): the acceptance probability of the call is the average over the columns of
  the per-column acceptance `V(z)`.
-/

set_option autoImplicit false

namespace NearQuarticWires.Builder

open Finset
open NearCubicWires NearCubicWires.WireExponent3_5.Shared
open NearCubicGates.Close.Interfaces

/-- The shape of a normalized call that the cell construction reads (`sec:counting`, paper/paper.tex, with the circuit representation of `Transfer.Counter4`): both circuits are `SYM∘THR` circuits with unit top
coefficients and one coefficient per occurrence, and the second circuit of a single or parity call is empty. -/
structure Shaped (c : Call) : Prop where
  first_unit : Transfer.UnitTop c.first
  second_unit : Transfer.UnitTop c.second
  first_length : c.first.gates.length = c.first.coeffs.length
  second_length : c.second.gates.length = c.second.coeffs.length
  second_empty : c.kind ≠ .pair → c.second = NCircuit.empty c.n

/-- Every normalized call has the shape read by the cell construction. -/
theorem Shaped.of_admitted {B1 B2 : ℕ} {c : Call} (h : Transfer.Admitted4 B1 B2 c) : Shaped c where
  first_unit := h.2.2.2.1
  second_unit := h.2.2.2.2.1
  first_length := h.2.1.1
  second_length := h.2.2.1.1
  second_empty := h.2.2.2.2.2.1

section Facts

variable (c : Call) {p : Cells.Parameters} (hs : Cells.ParameterRules (callInput c) p) (w : List Bool)

/-- The constructed cell call uses the parameters of `sec:params` (`Algorithm.CellCall.UsesParameters`): its
sampler `N`, `Q`, `S`, `η`, its `I = 2|Θ|`, `𝒫`, `e`, and the column constants `h_E`, `Λ`, `A` and circuit set are
those of `Cells.toAlgorithmParameters`. -/
theorem usesParameters : (cellCall c hs w).UsesParameters (algorithmParameters c hs) where
  N_eq := Cells.ParameterRules.seed_N hs
  Q_eq := Cells.ParameterRules.seed_Q hs
  S_eq := Cells.ParameterRules.seed_length hs
  eta_eq := rfl
  I_eq := by
    show 2 * (p.omega1 * p.omega2) = 2 * (Sampler.omega 4 c.first.gates.length *
      Sampler.omega 4 c.second.gates.length)
    rw [hs.omega1_eq, hs.omega2_eq, hs.m_eq]
    rfl
  primes_eq := rfl
  e_eq := rfl
  hE_eq := fun _ => rfl
  Lambda_eq := fun _ => rfl
  A_eq := fun _ => rfl
  circuits_eq := fun _ => rfl

/-- `sec:params`: the cell side `N = 2^{k/2}` is at least `2`. -/
theorem two_le_N : 2 ≤ (cellCall c hs w).seed.N := by
  show 2 ≤ hs.seedParameters.N
  rw [Cells.ParameterRules.seed_N hs]
  exact Cells.ParameterRules.N_ge_two hs

/-- `sec:params` item 4: the number of samples `Q` is at least `N`. -/
theorem N_le_Q : (cellCall c hs w).seed.N ≤ (cellCall c hs w).seed.Q := by
  show hs.seedParameters.N ≤ hs.seedParameters.Q
  rw [Cells.ParameterRules.seed_N hs, Cells.ParameterRules.seed_Q hs]
  exact Cells.ParameterRules.N_le_Q hs

/-- `lem:identity`, paper/paper.tex: `|R_j| ≤ G_j` at every point of every column. -/
theorem residual_le : ∀ z j q, |((cellCall c hs w).column z).residual j q| ≤ (cellCall c hs w).G j := by
  intro z j q
  exact Cells.residual_abs_le _ _ _ _ _

/-- `sec:cycle`, paper/paper.tex: a circuit outside `𝒥` (the second circuit of a single or parity call,
which is empty) has residual `0`. -/
theorem residual_zero (hc : Shaped c) :
    ∀ z j, j ∉ ((cellCall c hs w).column z).circuits → ∀ q, ((cellCall c hs w).column z).residual j q = 0 := by
  intro z j hj q
  change j ∉ circuitSet c at hj
  unfold circuitSet at hj
  by_cases hpair : c.kind = .pair
  · simp only [hpair, decide_true, if_true, Finset.mem_insert, Finset.mem_singleton] at hj
    omega
  · have hj1 : j = 1 := by
      simp only [hpair, decide_false, Bool.false_eq_true, if_false, Finset.mem_singleton] at hj
      omega
    subst hj1
    change Cells.residual (star c hs) (gatesOf c 1) _ _ _ = 0
    have hg : gatesOf c 1 = [] := by
      show c.second.gates = []
      rw [hc.second_empty hpair]
      rfl
    rw [hg]
    rfl

/-- The cube has `2^n = N² · n_col` points: `N² = 2^k` points per cell and `n_col = 2^{n-k}` cells. -/
theorem cube_card : ((2 : ℝ) ^ c.n) = ((hs.seedParameters.N : ℝ)) ^ 2 * ((2 ^ (c.n - p.k) : ℕ) : ℝ) := by
  have hN : hs.seedParameters.N ^ 2 = 2 ^ p.k := by
    rw [Cells.ParameterRules.seed_N hs]
    exact Cells.ParameterRules.N_square hs
  have hk : p.k ≤ c.n := (Cells.ParameterRules.k_lt_n hs).le
  have h : (2 : ℕ) ^ c.n = hs.seedParameters.N ^ 2 * 2 ^ (c.n - p.k) := by
    rw [hN, ← pow_add, Nat.add_sub_cancel' hk]
  exact_mod_cast h

/-- `imp:partition`, paper/paper.tex, as used in `prop:sound`: for the partition
named by the witness, a uniform column and a uniform point of its cell give a uniform input, so the acceptance
probability of the call is `n_col^{-1} Σ_z V(z)`. -/
theorem partitionAverage : (cellCall c hs w).PartitionAverage c.prob := by
  classical
  unfold Algorithm.CellCall.PartitionAverage Algorithm.CellCall.columnAcceptance
  set P := star c hs with hP
  set σ := translation c hs w with hσ
  let f : BitInput c.n → ℝ := fun x => (Algorithm.CellCall.bitInt (c.predicate x) : ℝ)
  -- the probability as an average over the cube
  have hprob : ((c.prob : ℚ) : ℝ) = (∑ x, f x) / 2 ^ c.n := by
    unfold Call.prob
    push_cast
    congr 1
    rw [Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [f, Algorithm.CellCall.bitInt]
    split_ifs <;> simp_all
  -- the cube sum, regrouped by columns and cell points
  have hcells : (∑ x, f x) = ∑ z : Fin (2 ^ (c.n - p.k)), ∑ u : Fin hs.seedParameters.N,
      ∑ v : Fin hs.seedParameters.N, f (P.point (center c hs w z) (pattern c hs u) (pattern c hs v)) := by
    refine (Cells.partition_sum P σ f).trans ?_
    rw [Finset.sum_subtype (univ.filter (P.IsCenter σ)) (p := P.IsCenter σ) (by simp)]
    rw [← Equiv.sum_comp (centerEquiv c hs σ)]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [← Equiv.sum_comp (patternEquiv c hs)]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [← Equiv.sum_comp (patternEquiv c hs)]
    rfl
  rw [hprob, hcells, cube_card c hs, ← Finset.sum_div, div_div]
  rfl

end Facts

end NearQuarticWires.Builder
