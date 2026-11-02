import Proof.Quartic.Builder.Crowded

/-!
# Event (iii) of the paragraph *Uncertified columns* from `lem:localize`

Paper: proof of `prop:complete`, paper/paper.tex; `lem:localize`.

`LocalizeLaw Q` is `lem:localize` for the cell call under a law `Q` of the vectors `ξ`, conditional on the
selection `𝒮`: for every column, walk, pattern with `κ_σ ≠ 0` and circuit of `𝒥`, the probability that the walk has
mask one, the column has no crowded point, and the conclusion of `lem:localize` fails, is at most `2J e^{-T}`.
`strayBound_of_localize` takes the union bound over the `2` circuits, `4^m` patterns and `N^{2m} = 2^{mk}` walks of a
column and the rule for `T` (`2^T β ≥ 2^{mk+2m+5} J_max`): `2^{mk} 4^m · 2 · 2J e^{-T} ≤ β/8`.
-/

set_option autoImplicit false

namespace NearQuarticWires.Builder

open Finset
open NearCubicWires NearCubicWires.WireExponent3_5.Shared
open NearCubicGates.Close.Interfaces

section Stray

variable (c : Call) {p : Cells.Parameters} (hs : Cells.ParameterRules (callInput c) p)

/-- The conclusion of `lem:localize` (paper/paper.tex) for one walk, pattern and circuit of a column:
`|E_r| ≤ mh` for every digit and `|φ| ≤ 172 m A T ℓ̄ / h`. -/
def LocalizedAt (w : List Bool) (z : Fin (cellCall c hs w).ncol) (walk : Cycle.Walk hs.seedParameters.N Algorithm.traceOrder)
    (σ : Cycle.SignPattern Algorithm.traceOrder) (j : Fin 2) : Prop :=
  (∀ r, (((cellCall c hs w).column z).E j σ walk r).natAbs ≤ 4 * p.h) ∧
    ((((cellCall c hs w).column z).phi Algorithm.traceOrder_pos j σ walk).natAbs : ℝ) ≤ finalRadius (p := p)

/-- **`lem:localize` for the cell call** (paper/paper.tex) under a law `Q` of the vectors `ξ`,
conditional on the selection `𝒮`: for every column `z`, walk `w`, pattern `σ` with `κ_σ ≠ 0` and circuit `j ∈ 𝒥`,
the probability over `ξ` that `mask_w(z) = 1`, that no point of mask one of the column has `pop > 16U` (so that
`pop(z, e_l) ≤ 16U` on the walk), and that the conclusion of `lem:localize` fails, is at most `2J e^{-T}`. -/
def LocalizeLaw (Q : (Fin p.J → Fin (allGates c).length → Bool) → ℝ) : Prop :=
  ∀ (s : Fin (allGates c).length → Bool) (z : Fin (2 ^ (c.n - p.k)))
    (walk : Cycle.Walk hs.seedParameters.N Algorithm.traceOrder) (σ : Cycle.SignPattern Algorithm.traceOrder)
    (j : Fin 2), Cycle.kappa Algorithm.traceOrder σ ≠ 0 → j ∈ circuitSet c →
    ∑ ξ, Q ξ * ind ((cellCall c hs (witnessWord c (goodIndex c hs) s ξ)).walkMask z walk = 1 ∧
      ¬ Crowded c hs (witnessWord c (goodIndex c hs) s ξ) z ∧
      ¬ LocalizedAt c hs (witnessWord c (goodIndex c hs) s ξ) z walk σ j) ≤
      2 * p.J * Real.exp (-(p.T : ℝ))

include hs in
/-- The tail arithmetic of event (iii) (`prop:complete`, paper/paper.tex):
`2 · 4^m · N^{2m} · 2J e^{-T} ≤ 2^{mk+2m+2} J_max 2^{-T} ≤ β/8`. -/
theorem stray_tail_le :
    2 * 2 ^ 8 * (hs.seedParameters.N : ℝ) ^ 8 * (2 * p.J * Real.exp (-(p.T : ℝ))) ≤ (c.radius : ℝ) / 8 := by
  have hβ : (0 : ℝ) < c.radius := by exact_mod_cast Cells.ParameterRules.beta_pos hs
  have hN8 : (hs.seedParameters.N : ℝ) ^ 8 = 2 ^ (4 * p.k) := by
    have h := Cells.ParameterRules.N_square hs
    rw [← Cells.ParameterRules.seed_N hs] at h
    have h' : ((hs.seedParameters.N : ℝ)) ^ 2 = 2 ^ p.k := by exact_mod_cast h
    rw [show (8 : ℕ) = 2 * 4 by norm_num, pow_mul, h', ← pow_mul, mul_comm]
  -- the rule for `T`
  have hT : ((2 ^ (p.m * p.k + 2 * p.m + 5) * p.Jmax : ℕ) : ℚ) ≤ 2 ^ p.T * c.radius := by
    have h := (Cells.ParameterRules.T_le_iff hs p.T).mp le_rfl
    exact h.2
  have hTr : (2 : ℝ) ^ (4 * p.k + 13) * p.Jmax ≤ 2 ^ p.T * c.radius := by
    have h := (Rat.cast_le (K := ℝ)).mpr hT
    rw [hs.m_eq] at h
    push_cast at h
    rw [show 4 * p.k + 2 * 4 + 5 = 4 * p.k + 13 by ring] at h
    exact h
  have hJ : (p.J : ℝ) ≤ p.Jmax := by exact_mod_cast hs.J_bound
  -- `e^{-T} ≤ 2^{-T}`
  have he : Real.exp (-(p.T : ℝ)) ≤ 1 / 2 ^ p.T := by
    rw [Real.exp_neg, ← one_div]
    apply one_div_le_one_div_of_le (by positivity)
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ)
      linarith
    calc (2 : ℝ) ^ p.T ≤ Real.exp 1 ^ p.T := pow_le_pow_left₀ (by norm_num) h2 _
      _ = Real.exp (p.T : ℝ) := by rw [← Real.exp_nat_mul, mul_one]
  rw [hN8]
  have h2T : (0 : ℝ) < 2 ^ p.T := by positivity
  calc 2 * 2 ^ 8 * (2 : ℝ) ^ (4 * p.k) * (2 * p.J * Real.exp (-(p.T : ℝ)))
      ≤ 2 * 2 ^ 8 * (2 : ℝ) ^ (4 * p.k) * (2 * p.Jmax * (1 / 2 ^ p.T)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul (mul_le_mul_of_nonneg_left hJ (by norm_num)) he (by positivity) (by positivity)
    _ = (2 : ℝ) ^ (4 * p.k + 13) * p.Jmax / 2 ^ p.T / 8 := by
        rw [pow_add]
        ring
    _ ≤ (2 ^ p.T * (c.radius : ℝ)) / 2 ^ p.T / 8 := by
        apply div_le_div_of_nonneg_right _ (by norm_num)
        exact div_le_div_of_nonneg_right hTr h2T.le
    _ = (c.radius : ℝ) / 8 := by field_simp

/-- **Event (iii) from `lem:localize`** (paper/paper.tex): under `LocalizeLaw Q`, the expected
fraction of columns without event (ii) where the conclusion of `lem:localize` fails is at most `β/8`. -/
theorem strayBound_of_localize (Q : (Fin p.J → Fin (allGates c).length → Bool) → ℝ) (hQ0 : ∀ ξ, 0 ≤ Q ξ)
    (hQ1 : ∑ ξ, Q ξ = 1) (hL : LocalizeLaw c hs Q) : StrayBound c hs := by
  classical
  refine ⟨Q, hQ0, hQ1, ?_⟩
  set N := hs.seedParameters.N
  let word := fun (s : Fin (allGates c).length → Bool) (ξ : Fin p.J → Fin (allGates c).length → Bool) =>
    witnessWord c (goodIndex c hs) s ξ
  -- the per-tuple event
  let ev := fun (s : Fin (allGates c).length → Bool) (ξ : Fin p.J → Fin (allGates c).length → Bool)
      (z : Fin (2 ^ (c.n - p.k))) (t : Fin 2 × Cycle.SignPattern Algorithm.traceOrder ×
        Cycle.Walk N Algorithm.traceOrder) =>
    (Cycle.kappa Algorithm.traceOrder t.2.1 ≠ 0 ∧ t.1 ∈ circuitSet c) ∧
      ((cellCall c hs (word s ξ)).walkMask z t.2.2 = 1 ∧ ¬ Crowded c hs (word s ξ) z ∧
        ¬ LocalizedAt c hs (word s ξ) z t.2.2 t.2.1 t.1)
  set K := 2 * p.J * Real.exp (-(p.T : ℝ)) with hK
  have hK0 : 0 ≤ K := by positivity
  -- union bound over the tuples
  have hunion : ∀ s ξ, strayFraction c hs (word s ξ) ≤
      (∑ z : Fin (2 ^ (c.n - p.k)), ∑ t, ind (ev s ξ z t)) / ((2 ^ (c.n - p.k) : ℕ) : ℝ) := by
    intro s ξ
    unfold strayFraction columnFraction
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    refine Finset.sum_le_sum fun z _ => ?_
    by_cases hz : ¬ Localized c hs (word s ξ) z ∧ ¬ Crowded c hs (word s ξ) z
    · have h1 : ind ((fun z => ¬ Localized c hs (word s ξ) z ∧ ¬ Crowded c hs (word s ξ) z) z) = 1 :=
        ind_of _ hz
      rw [h1]
      obtain ⟨hL', hC⟩ := hz
      unfold Localized at hL'
      push Not at hL'
      obtain ⟨j, hj, σ, hσ, walk, hw, hfail⟩ := hL'
      have hev : ev s ξ z (j, σ, walk) := by
        refine ⟨⟨hσ, hj⟩, hw, hC, ?_⟩
        intro hloc
        obtain ⟨h1, h2⟩ := hloc
        by_cases hr : ∀ r, (((cellCall c hs (word s ξ)).column z).E j σ walk r).natAbs ≤ 4 * p.h
        · exact absurd h2 (not_le.mpr (hfail hr))
        · exact hr h1
      calc (1 : ℝ) = ind (ev s ξ z (j, σ, walk)) := (ind_of _ hev).symm
        _ ≤ ∑ t, ind (ev s ξ z t) :=
          Finset.single_le_sum (f := fun t => ind (ev s ξ z t)) (fun t _ => ind_nonneg _) (Finset.mem_univ _)
    · have h0 : ind ((fun z => ¬ Localized c hs (word s ξ) z ∧ ¬ Crowded c hs (word s ξ) z) z) = 0 := by
        unfold ind
        rw [if_neg hz]
      rw [h0]
      exact Finset.sum_nonneg fun t _ => ind_nonneg _
  -- the probability of each tuple
  have htuple : ∀ s z t, ∑ ξ, Q ξ * ind (ev s ξ z t) ≤ K := by
    intro s z t
    by_cases ht : Cycle.kappa Algorithm.traceOrder t.2.1 ≠ 0 ∧ t.1 ∈ circuitSet c
    · have h := hL s z t.2.2 t.2.1 t.1 ht.1 ht.2
      refine le_trans (le_of_eq (Finset.sum_congr rfl fun ξ _ => ?_)) h
      have hiff : ev s ξ z t ↔ ((cellCall c hs (word s ξ)).walkMask z t.2.2 = 1 ∧
          ¬ Crowded c hs (word s ξ) z ∧ ¬ LocalizedAt c hs (word s ξ) z t.2.2 t.2.1 t.1) := and_iff_right ht
      rw [propext hiff]
    · have h0 : ∀ ξ, ind (ev s ξ z t) = 0 := fun ξ => by unfold ind; rw [if_neg (fun h => ht h.1)]
      simp only [h0, mul_zero, Finset.sum_const_zero]
      exact hK0
  have hcol : (0 : ℝ) < ((2 ^ (c.n - p.k) : ℕ) : ℝ) := by exact_mod_cast Nat.two_pow_pos _
  have hcard : (Fintype.card (Fin 2 × Cycle.SignPattern Algorithm.traceOrder × Cycle.Walk N Algorithm.traceOrder) : ℝ) =
      2 * 2 ^ 8 * (N : ℝ) ^ 8 := by
    simp [Cycle.SignPattern, Cycle.Walk, Algorithm.traceOrder, Fintype.card_prod]
    ring
  -- assemble: for each `s`, the expectation over `ξ`
  have hs_bound : ∀ s, ∑ ξ, Q ξ * strayFraction c hs (word s ξ) ≤ 2 * 2 ^ 8 * (N : ℝ) ^ 8 * K := by
    intro s
    calc ∑ ξ, Q ξ * strayFraction c hs (word s ξ)
        ≤ ∑ ξ, Q ξ * ((∑ z : Fin (2 ^ (c.n - p.k)), ∑ t, ind (ev s ξ z t)) / ((2 ^ (c.n - p.k) : ℕ) : ℝ)) :=
          Finset.sum_le_sum fun ξ _ => mul_le_mul_of_nonneg_left (hunion s ξ) (hQ0 ξ)
      _ = (∑ z : Fin (2 ^ (c.n - p.k)), ∑ t, ∑ ξ, Q ξ * ind (ev s ξ z t)) / ((2 ^ (c.n - p.k) : ℕ) : ℝ) := by
          have e1 : ∀ ξ, Q ξ * ((∑ z : Fin (2 ^ (c.n - p.k)), ∑ t, ind (ev s ξ z t)) /
              ((2 ^ (c.n - p.k) : ℕ) : ℝ)) =
              (Q ξ * ∑ z : Fin (2 ^ (c.n - p.k)), ∑ t, ind (ev s ξ z t)) / ((2 ^ (c.n - p.k) : ℕ) : ℝ) :=
            fun ξ => by ring
          rw [Finset.sum_congr rfl (fun ξ _ => e1 ξ), ← Finset.sum_div]
          congr 1
          simp only [Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun z _ => ?_
          rw [Finset.sum_comm]
      _ ≤ (∑ _z : Fin (2 ^ (c.n - p.k)), ∑ _t : Fin 2 × Cycle.SignPattern Algorithm.traceOrder ×
            Cycle.Walk N Algorithm.traceOrder, K) / ((2 ^ (c.n - p.k) : ℕ) : ℝ) := by
          apply div_le_div_of_nonneg_right _ hcol.le
          exact Finset.sum_le_sum fun z _ => Finset.sum_le_sum fun t _ => htuple s z t
      _ = 2 * 2 ^ 8 * (N : ℝ) ^ 8 * K := by
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_fin]
          rw [hcard]
          field_simp
  calc ∑ s, ∑ ξ, selectionWeight c hs s * Q ξ * strayFraction c hs (word s ξ)
      = ∑ s, selectionWeight c hs s * ∑ ξ, Q ξ * strayFraction c hs (word s ξ) := by
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun ξ _ => by ring
    _ ≤ ∑ s, selectionWeight c hs s * (2 * 2 ^ 8 * (N : ℝ) ^ 8 * K) :=
        Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hs_bound s) (selectionWeight_nonneg c hs s)
    _ = 2 * 2 ^ 8 * (N : ℝ) ^ 8 * K := by rw [← Finset.sum_mul, sum_selectionWeight, one_mul]
    _ ≤ (c.radius : ℝ) / 8 := stray_tail_le c hs

end Stray

/-- **`thm:counter`(i),(ii) for `Builder.value`, with every part of `prop:complete` proved except `lem:localize`
itself**: the hypotheses are the cap of `lem:asymptotics` and, for every call meeting the hypotheses of
`prop:complete`, a law `Q` of the vectors `ξ` satisfying `lem:localize` for the cell call (`LocalizeLaw`). -/
noncomputable def counterMath4_of_localize {B1 B2 : ℕ} (hcap : QuarticCap B1 B2)
    (hloc : ∀ (c : Call) (p : Cells.Parameters) (hs : Cells.ParameterRules (callInput c) p), Shaped c →
      CompletenessConditions c p → ∃ Q : (Fin p.J → Fin (allGates c).length → Bool) → ℝ,
        (∀ ξ, 0 ≤ Q ξ) ∧ ∑ ξ, Q ξ = 1 ∧ LocalizeLaw c hs Q) :
    CounterMath4 B1 B2 :=
  counterMath4_of_stray hcap fun c p hs hc hcond => by
    obtain ⟨Q, hQ0, hQ1, hL⟩ := hloc c p hs hc hcond
    exact strayBound_of_localize c hs Q hQ0 hQ1 hL

end NearQuarticWires.Builder
