import Proof.Quartic.Builder.Sound
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Completeness of the counting algorithm on a call

Paper: `prop:complete`, paper/paper.tex; `lem:asymptotics`; the proof of
`thm:counter`.

* `CompletenessConditions c p` are the hypotheses of `prop:complete` beyond the parameter requirements: the side
  conditions `k ≥ lg(16/β)` and `X_max ≥ 2k + 2 lg(64/β)` and the window condition `eq:window`.
* `WitnessLaw c hs L` is the probabilistic part of the proof of `prop:complete`: a probability distribution on
  witness words of length at most `L` under which the expected masked mass is at most `β/7` (paragraph *Masked
  mass*) and the expected uncertified fraction is at most `β/4` (paragraph *Uncertified columns*).
* `complete_of_law`: from a witness law, `prop:complete` (`Algorithm.CellCall.prop_complete`) gives a witness with
  `κ̂ ≤ 7β/16 + 2^{-n}`; every other hypothesis of `prop:complete` is supplied by the cell construction.
-/

set_option autoImplicit false

namespace NearQuarticWires.Builder

open Finset
open NearCubicWires NearCubicWires.WireExponent3_5.Shared
open NearCubicGates.Close.Interfaces

/-- The hypotheses of `prop:complete` beyond the parameter requirements (paper/paper.tex), with the
logarithms written as exact power comparisons:
* `k ≥ lg(16/β)`, i.e. `16/β ≤ 2^k`;
* `X_max ≥ 2k + 2 lg(64/β)`, i.e. `2^{2k} (64/β)² ≤ 2^{X_max}`;
* the window condition `eq:window`: `487 m T ℓ̄ / h < L_w - 1`, with `ℓ̄ = max{ℓ_0, h²/(256T)}`. -/
structure CompletenessConditions (c : Call) (p : Cells.Parameters) : Prop where
  k_large : (16 : ℚ) / c.radius ≤ 2 ^ p.k
  Xmax_large : (2 : ℚ) ^ (2 * p.k) * (64 / c.radius) ^ 2 ≤ 2 ^ p.Xmax
  window : 487 * (p.m : ℚ) * p.T * NearCubicGates.Close.Counter.ellBar p.ell0 p.h p.T / p.h < (p.Lw : ℚ) - 1

/-- **The probabilistic part of the proof of `prop:complete`** (paper/paper.tex) for the call `c`
with the selected parameters: a probability distribution `P` on a finite set of witness words, each of length at
most `L`, under which
* the expected masked mass `Pr_{z,u,v}[mask = 0]` of the cell call is at most `β/7` (paragraph *Masked mass*: `lem:smaskmass`, `lem:meanpop` with Markov's inequality, `lem:filter`(a)), and
* the expected uncertified fraction `(n_col - n_c)/n_col` is at most `β/4` (paragraph *Uncertified columns*: `lem:filter`(b,c), `lem:localize`, `lem:moments`, `eq:window`). -/
structure WitnessLaw (c : Call) {p : Cells.Parameters} (hs : Cells.ParameterRules (callInput c) p) (L : ℕ) where
  Ω : Type
  [fintype : Fintype Ω]
  word : Ω → List Bool
  length_le : ∀ ω, (word ω).length ≤ L
  P : Ω → ℝ
  nonneg : ∀ ω, 0 ≤ P ω
  total : ∑ ω, P ω = 1
  maskedMass_le : ∑ ω, P ω * (cellCall c hs (word ω)).maskedMass ≤ (c.radius : ℝ) / 7
  uncertified_le : ∑ ω, P ω * (cellCall c hs (word ω)).uncertifiedFraction ≤ (c.radius : ℝ) / 4

attribute [instance] WitnessLaw.fintype

section Complete

variable (c : Call) {p : Cells.Parameters} (hs : Cells.ParameterRules (callInput c) p)

/-- The sampler budget of `sec:params` item 4 holds for the cell call of every witness. -/
theorem samplerBudget (w : List Bool) : (cellCall c hs w).SamplerBudget :=
  let U := usesParameters c hs w
  (cellCall c hs w).samplerBudget_of_parameters (algorithmParameters c hs) U.N_eq U.Q_eq U.eta_eq U.I_eq
    (two_le_N c hs w) (N_le_Q c hs w)

/-- The reconstruction hypotheses of step (1) of `prop:sound` hold for the cell call of every witness. -/
theorem reconstructionHypotheses (hc : Shaped c) (w : List Bool) :
    (cellCall c hs w).ReconstructionHypotheses :=
  ((cellCall c hs w).reconstructionFacts_of_parameters (algorithmParameters c hs) (usesParameters c hs w)
    (residual_le c hs w) (residual_zero c hs w hc)).toHypotheses

/-- **`prop:complete` for a call** (paper/paper.tex): given the probabilistic part (`WitnessLaw`),
some witness word of length at most `L` gives `κ̂ ≤ 7β/16 + 2^{-n}`. -/
theorem complete_of_law (hc : Shaped c) (L : ℕ) (law : WitnessLaw c hs L) :
    ∃ w : List Bool, w.length ≤ L ∧ (cellCall c hs w).run.2 ≤ 7 * c.radius / 16 + 1 / 2 ^ c.n := by
  have hβ : 0 ≤ c.radius := (Cells.ParameterRules.beta_pos hs).le
  have hMF : 1 ≤ p.MF := Cells.ParameterRules.MF_pos hs
  obtain ⟨ω, hω⟩ := Algorithm.CellCall.prop_complete (fun ω => cellCall c hs (law.word ω)) law.P law.nonneg
    law.total c.n (fun _ => rfl) c.radius hβ (fun ω => fourierRows c hs (law.word ω) hc)
    (fun ω => samplerBudget c hs (law.word ω)) (fun ω => reconstructionHypotheses c hs hc (law.word ω))
    (fun _ => hMF) (fun _ => hs.eta_eq) (fun _ => show 0 < 2 ^ (c.n - p.k) from Nat.two_pow_pos _)
    law.maskedMass_le law.uncertified_le
  exact ⟨law.word ω, law.length_le ω, hω⟩

end Complete

/-! ### The cap and the counter's completeness -/

/-- For every exponent `B`, eventually `16 n^B ≤ 9 · 2^n`; hence `2^{-n} ≤ 9β/16` once `β ≥ n^{-B}`. -/
theorem eventually_pow_le_two_pow (B : ℕ) : ∃ onset : ℕ, ∀ n, onset ≤ n → 16 * (n : ℝ) ^ B ≤ 9 * 2 ^ n := by
  have ht := tendsto_pow_const_div_const_pow_of_one_lt B (r := (2 : ℝ)) (by norm_num)
  have hev := ht.eventually (gt_mem_nhds (show (0 : ℝ) < 9 / 16 by norm_num))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
  refine ⟨N, fun n hn => ?_⟩
  have h := hN n hn
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  rw [div_lt_iff₀ h2] at h
  linarith

/-- The witness length bound: an admitted call has a witness of `k + (J + 1)(G_1 + G_2) ≤ n + (n + 2) · 2n⁴`
bits (`sec:algorithm`, paper/paper.tex; `k ≤ n`, `J ≤ μ_n + 1 ≤ n + 1`, `G_1 + G_2 ≤ W ≤ 2n⁴`). -/
def witnessLength (n : ℕ) : ℕ := n + (n + 2) * (2 * n ^ 4)

theorem witnessLength_poly : ∃ C k : ℕ, ∀ n, witnessLength n ≤ C * (n + 1) ^ k := by
  refine ⟨5, 5, fun n => ?_⟩
  unfold witnessLength
  have h1 : n ≤ (n + 1) ^ 5 := by
    calc n ≤ n + 1 := Nat.le_succ n
      _ = (n + 1) ^ 1 := (pow_one _).symm
      _ ≤ (n + 1) ^ 5 := Nat.pow_le_pow_right (Nat.succ_pos n) (by norm_num)
  have h2 : n ^ 4 ≤ (n + 1) ^ 4 := Nat.pow_le_pow_left (Nat.le_succ n) 4
  have h3 : (n + 2) * (2 * n ^ 4) ≤ 4 * (n + 1) ^ 5 := by
    calc (n + 2) * (2 * n ^ 4) ≤ (2 * (n + 1)) * (2 * (n + 1) ^ 4) := Nat.mul_le_mul (by omega) (by omega)
      _ = 4 * (n + 1) ^ 5 := by ring
  omega

/-- **`lem:asymptotics` and the cap of `thm:counter`** (paper/paper.tex): there are `a > 0` and an
onset such that every normalized call with `n` past the onset, `W > 0` and `W ≤ a β 𝒜₄(n)` has its parameters
selected by the exact rules, and these satisfy the side conditions and the window condition of `prop:complete`. -/
def QuarticCap (B1 B2 : ℕ) : Prop :=
  ∃ a : ℝ, 0 < a ∧ ∃ onset : ℕ, ∀ c : Call, onset ≤ c.n → Transfer.Admitted4 B1 B2 c →
    Transfer.callWires c ≠ 0 → (Transfer.callWires c : ℝ) ≤ a * (c.radius : ℝ) * Transfer.A4 c.n →
    ∃ p : Cells.Parameters, Cells.prepare (callInput c) = some p ∧ CompletenessConditions c p

/-- **The probabilistic part of `prop:complete` for every call meeting its hypotheses**: a witness law with
witnesses of length at most `L n`. -/
def ParagraphBounds (L : ℕ → ℕ) : Prop :=
  ∀ (c : Call) (p : Cells.Parameters) (hs : Cells.ParameterRules (callInput c) p), Shaped c →
    CompletenessConditions c p → Nonempty (WitnessLaw c hs (L c.n))

/-- **Completeness under the quartic cap** (`thm:counter`(ii), paper/paper.tex): for
large `n`, every normalized call with `W ≤ a β 𝒜₄(n)` has a witness of length at most `witnessLength n` with
`κ̂ ≤ β`. The hypotheses are the cap (`QuarticCap`) and the probabilistic part of `prop:complete`
(`ParagraphBounds`). -/
theorem value_complete {B1 B2 : ℕ} (hcap : QuarticCap B1 B2) (hlaw : ParagraphBounds witnessLength) :
    ∃ a : ℝ, 0 < a ∧ ∃ onset : ℕ, ∀ c : Call, onset ≤ c.n → Transfer.Admitted4 B1 B2 c →
      (Transfer.callWires c : ℝ) ≤ a * (c.radius : ℝ) * Transfer.A4 c.n →
      ∃ w : List Bool, w.length ≤ witnessLength c.n ∧ (value c w).2 ≤ c.radius := by
  obtain ⟨a, ha, onset₁, hcap⟩ := hcap
  obtain ⟨onset₂, hpow⟩ := eventually_pow_le_two_pow B1
  refine ⟨a, ha, max onset₁ onset₂, fun c hn hadm hW => ?_⟩
  have hc : Shaped c := Shaped.of_admitted hadm
  have hβ : 0 < c.radius := by
    have h1 : 1 ≤ c.radius * (c.n : ℚ) ^ B1 := hadm.2.2.2.2.2.2.2.2.2.1
    by_contra h
    push Not at h
    have : c.radius * (c.n : ℚ) ^ B1 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h (by positivity)
    linarith
  by_cases hW0 : Transfer.callWires c = 0
  · -- `W = 0`: exact evaluation, radius `0`
    refine ⟨[], Nat.zero_le _, ?_⟩
    have hn4 : ¬ c.n < 4 := by have := hadm.1; omega
    unfold value
    simp only [if_pos hc, if_neg hn4, if_pos hW0, closedValue_eq c hc hW0]
    exact hβ.le
  · obtain ⟨p, hp, hcond⟩ := hcap c (le_of_max_le_left hn) hadm hW0 hW
    have hs := Cells.prepare_spec _ p hp
    obtain ⟨law⟩ := hlaw c p hs hc hcond
    obtain ⟨w, hwlen, hw⟩ := complete_of_law c hs hc (witnessLength c.n) law
    refine ⟨w, hwlen, ?_⟩
    rw [value_eq_run c hc hW0 hp w]
    -- `2^{-n} ≤ 9β/16` from `β ≥ n^{-B₁}`
    have hnB : 16 * (c.n : ℝ) ^ B1 ≤ 9 * 2 ^ c.n := hpow c.n (le_of_max_le_right hn)
    have h1 : (1 : ℝ) ≤ (c.radius : ℝ) * (c.n : ℝ) ^ B1 := by
      exact_mod_cast hadm.2.2.2.2.2.2.2.2.2.1
    have hround : (1 : ℝ) / 2 ^ c.n ≤ 9 * (c.radius : ℝ) / 16 := by
      have h2 : (0 : ℝ) < 2 ^ c.n := by positivity
      rw [div_le_iff₀ h2]
      have hβr : (0 : ℝ) ≤ c.radius := by exact_mod_cast hβ.le
      nlinarith
    have hwr : ((cellCall c hs w).run.2 : ℝ) ≤ 7 * (c.radius : ℝ) / 16 + 1 / 2 ^ c.n := by
      have h := (Rat.cast_le (K := ℝ)).mpr hw
      push_cast at h
      exact h
    have : ((cellCall c hs w).run.2 : ℝ) ≤ c.radius := by linarith
    exact_mod_cast this

end NearQuarticWires.Builder
