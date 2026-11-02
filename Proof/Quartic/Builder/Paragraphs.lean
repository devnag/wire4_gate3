import Proof.Quartic.Builder.Certify

/-!
# The two paragraph bounds of `prop:complete`, from the probabilities of the bad events

Paper: proof of `prop:complete`, paper/paper.tex.

The paragraph *Masked mass* bounds `Pr_{z,u,v}[mask = 0]` by
`Pr[smask = 0] + Pr[pop > U] + Pr[pop ≤ U, X > τ]`; the paragraph *Uncertified columns* shows that a column is
certified unless (i) some point with `smask = 1` has `X ≥ X_max/2`, or (ii)/(iii) the conclusion of `lem:localize`
fails on some walk with `mask_w = 1`. This file proves both decompositions for the cell call of a call and every
witness word (`maskedMass_le_events`, `uncertifiedFraction_le_events`), averages them over a witness law, and adds
the paper's numbers: `β/48 + β/16 + 3β/64 ≤ β/7` and `β/64 + 3β/16 ≤ β/4` (`witnessLaw_of_eventBounds`).

The probabilities of the individual events are the fields of `EventBounds`:
* `structural`: `Pr_{u,v}[smask = 0] ≤ β/48` (`lem:smaskmass`);
* `population`: `Pr_{z,u,v}[pop > U] ≤ β/16` (`lem:meanpop` and Markov's inequality);
* `filter`: `E Pr_{z,u,v}[pop ≤ U, X > τ] ≤ (e/4)^{τ+1} ≤ 3β/64` (`lem:filter`(a));
* `wide`: the expected fraction of columns with event (i) is at most `β/64` (`lem:filter`(c));
* `unlocalized`: the expected fraction of columns with event (ii) or (iii) is at most `β/16 + β/8`
  (`lem:filter`(b), `lem:localize`).
-/

set_option autoImplicit false

namespace NearQuarticWires.Builder

open Finset
open NearCubicGates.Close.Interfaces

/-- The indicator of a proposition, as a real number. -/
noncomputable def ind (P : Prop) : ℝ := by
  classical
  exact if P then 1 else 0

theorem ind_nonneg (P : Prop) : 0 ≤ ind P := by
  unfold ind
  split_ifs <;> norm_num

theorem ind_le_one (P : Prop) : ind P ≤ 1 := by
  unfold ind
  split_ifs <;> norm_num

theorem ind_of (P : Prop) (h : P) : ind P = 1 := by
  unfold ind
  rw [if_pos h]

/-! ### Averages over the points of all cells -/

section Average

variable (C : Algorithm.CellCall)

/-- The average `E_{z,u,v} f(z,u,v)` over a uniform column and a uniform point of its cell. -/
noncomputable def pointAverage (f : Fin C.ncol → Sampler.Cell C.seed.N → ℝ) : ℝ :=
  (∑ z, ∑ u, ∑ v, f z (u, v)) / (C.ncol * (C.seed.N : ℝ) ^ 2)

/-- The masked mass is the average of `1 - mask` over the points of all cells. -/
theorem maskedMass_eq_average (hN : 0 < C.seed.N) :
    C.maskedMass = pointAverage C (fun z q => 1 - C.realMask z q) := by
  unfold Algorithm.CellCall.maskedMass Algorithm.CellCall.columnMaskMean pointAverage
  have hN2 : (0 : ℝ) < (C.seed.N : ℝ) ^ 2 := by
    have : (0 : ℝ) < C.seed.N := by exact_mod_cast hN
    positivity
  rw [mul_comm (C.ncol : ℝ), ← div_div]
  congr 1
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [eq_div_iff hN2.ne', sub_mul, div_mul_cancel₀ _ hN2.ne', one_mul]
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one]
  ring

/-- Averages are monotone and additive: a pointwise bound `g ≤ f₁ + f₂ + f₃` gives the same bound on averages. -/
theorem pointAverage_le_add (g f₁ f₂ f₃ : Fin C.ncol → Sampler.Cell C.seed.N → ℝ)
    (h : ∀ z q, g z q ≤ f₁ z q + f₂ z q + f₃ z q) :
    pointAverage C g ≤ pointAverage C f₁ + pointAverage C f₂ + pointAverage C f₃ := by
  unfold pointAverage
  rw [← add_div, ← add_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun z _ => ?_
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun u _ => ?_
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun v _ => h z (u, v)

/-- The fraction `n_col^{-1} #{z : A z}` of columns with a property. -/
noncomputable def columnFraction (A : Fin C.ncol → Prop) : ℝ := (∑ z, ind (A z)) / C.ncol

/-- A column that is not certified has property `A` or property `B`: the uncertified fraction is at most the sum
of the two fractions. -/
theorem uncertifiedFraction_le (A B : Fin C.ncol → Prop) (h : ∀ z, ¬ C.Certified z → A z ∨ B z) :
    C.uncertifiedFraction ≤ columnFraction C A + columnFraction C B := by
  classical
  unfold Algorithm.CellCall.uncertifiedFraction columnFraction
  rw [← add_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have hcount : ((C.ncol : ℝ) - C.certifiedColumns.card) = ∑ z, ind (¬ C.Certified z) := by
    have hsplit := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin C.ncol)))
      (p := C.Certified)
    rw [Finset.card_univ, Fintype.card_fin] at hsplit
    have hc : C.certifiedColumns = Finset.univ.filter C.Certified := rfl
    have hsum : (∑ z, ind (¬ C.Certified z)) = ((Finset.univ.filter fun z => ¬ C.Certified z).card : ℝ) := by
      rw [Finset.card_filter]
      push_cast
      refine Finset.sum_congr rfl fun z _ => ?_
      unfold ind
      congr 1
    rw [hsum, hc]
    have : ((Finset.univ.filter C.Certified).card : ℝ) + (Finset.univ.filter fun z => ¬ C.Certified z).card =
        C.ncol := by exact_mod_cast hsplit
    linarith
  rw [hcount, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun z _ => ?_
  by_cases hz : C.Certified z
  · have h0 : ind (¬ C.Certified z) = 0 := by unfold ind; rw [if_neg (not_not.mpr hz)]
    rw [h0]
    exact add_nonneg (ind_nonneg _) (ind_nonneg _)
  · rw [ind_of _ hz]
    rcases h z hz with hA | hB
    · rw [ind_of _ hA]; linarith [ind_nonneg (B z)]
    · rw [ind_of _ hB]; linarith [ind_nonneg (A z)]

end Average

/-! ### The bad events of the cell call -/

section Events

variable (c : Call) {p : Cells.Parameters} (hs : Cells.ParameterRules (callInput c) p) (w : List Bool)

/-- `sec:cells`, paper/paper.tex: the population `pop(z,u,v) = Σ_{j ∈ 𝒥} Σ_i |Δ_{j,i}(z,u,v)|`. -/
noncomputable def population (z : Fin (cellCall c hs w).ncol) (q : Sampler.Cell (cellCall c hs w).seed.N) : ℕ :=
  Cells.population (star c hs) (allGates c) (center c hs w z) (pattern c hs q.1) (pattern c hs q.2)

/-- `Pr_{u,v}[smask(u,v) = 0]`, as an average over all cells (`prop:complete`, paper/paper.tex). -/
noncomputable def structuralMass : ℝ :=
  pointAverage (cellCall c hs w) fun z q => ind (((cellCall c hs w).column z).structural q = false)

/-- `Pr_{z,u,v}[pop > U]` (`prop:complete`, paper/paper.tex). -/
noncomputable def populationMass : ℝ :=
  pointAverage (cellCall c hs w) fun z q => ind (p.U < population c hs w z q)

/-- `Pr_{z,u,v}[pop ≤ U, X > τ]` for the selection of the witness (`prop:complete`, paper/paper.tex). -/
noncomputable def lightFilteredMass : ℝ :=
  pointAverage (cellCall c hs w) fun z q =>
    ind (population c hs w z q ≤ p.U ∧ p.tau < ((cellCall c hs w).column z).X q)

/-- Event (i) of the paragraph *Uncertified columns* (`prop:complete`, paper/paper.tex) for column `z`: some point
with `smask = 1` has `X ≥ X_max / 2`. -/
def Wide (z : Fin (cellCall c hs w).ncol) : Prop :=
  ∃ q, ((cellCall c hs w).column z).structural q = true ∧ p.Xmax < 2 * ((cellCall c hs w).column z).X q

/-- The conclusion of `lem:localize` (paper/paper.tex) on every walk of mask one of column `z`,
for every circuit of `𝒥` and every pattern with `κ_σ ≠ 0`: `|E_r| ≤ mh` and `|φ| ≤ 172 m A T ℓ̄ / h`. Events (ii)
and (iii) of the paragraph *Uncertified columns* are contained in its failure. -/
def Localized (z : Fin (cellCall c hs w).ncol) : Prop :=
  ∀ j ∈ ((cellCall c hs w).column z).circuits, ∀ σ : Cycle.SignPattern Algorithm.traceOrder,
    Cycle.kappa Algorithm.traceOrder σ ≠ 0 → ∀ walk : Cycle.Walk hs.seedParameters.N Algorithm.traceOrder,
    (cellCall c hs w).walkMask z walk = 1 →
    (∀ r, (((cellCall c hs w).column z).E j σ walk r).natAbs ≤ 4 * p.h) ∧
    ((((cellCall c hs w).column z).phi Algorithm.traceOrder_pos j σ walk).natAbs : ℝ) ≤ finalRadius (p := p)

/-- The fraction of columns with event (i). -/
noncomputable def wideFraction : ℝ := columnFraction (cellCall c hs w) (Wide c hs w)

/-- The fraction of columns where the conclusion of `lem:localize` fails (events (ii) and (iii)). -/
noncomputable def unlocalizedFraction : ℝ :=
  columnFraction (cellCall c hs w) fun z => ¬ Localized c hs w z

/-- **Paragraph *Masked mass*, pointwise** (`prop:complete`, paper/paper.tex): `Pr_{z,u,v}[mask = 0]` is at most
`Pr[smask = 0] + Pr[pop > U] + Pr[pop ≤ U, X > τ]`. -/
theorem maskedMass_le_events :
    (cellCall c hs w).maskedMass ≤ structuralMass c hs w + populationMass c hs w + lightFilteredMass c hs w := by
  have hN : 0 < (cellCall c hs w).seed.N := by have := two_le_N c hs w; omega
  rw [maskedMass_eq_average _ hN]
  refine pointAverage_le_add _ _ _ _ _ fun z q => ?_
  unfold Algorithm.CellCall.realMask Algorithm.CellCall.pointMask Mask.mask
  have h1 := ind_nonneg (((cellCall c hs w).column z).structural q = false)
  have h2 := ind_nonneg (p.U < population c hs w z q)
  have h3 := ind_nonneg (population c hs w z q ≤ p.U ∧ p.tau < ((cellCall c hs w).column z).X q)
  by_cases hs1 : ((cellCall c hs w).column z).structural q = true
  · by_cases hX : ((cellCall c hs w).column z).X q ≤ ((cellCall c hs w).column z).tau
    · rw [if_pos ⟨hs1, hX⟩]
      push_cast
      linarith
    · rw [if_neg (fun h => hX h.2)]
      have hτ : p.tau < ((cellCall c hs w).column z).X q := by
        have : ((cellCall c hs w).column z).tau = p.tau := rfl
        omega
      by_cases hU : p.U < population c hs w z q
      · rw [ind_of _ hU]
        push_cast
        linarith
      · have hP : population c hs w z q ≤ p.U ∧ p.tau < ((cellCall c hs w).column z).X q := ⟨by omega, hτ⟩
        rw [ind_of _ hP]
        push_cast
        linarith
  · rw [if_neg (fun h => hs1 h.1), ind_of _ (by simpa using hs1)]
    push_cast
    linarith

/-- **Paragraph *Uncertified columns*, pointwise** (paper/paper.tex): under the window condition, a
column that is not certified has event (i) or a failure of the conclusion of `lem:localize`. -/
theorem uncertifiedFraction_le_events
    (hwin : 487 * (p.m : ℚ) * p.T * NearCubicGates.Close.Counter.ellBar p.ell0 p.h p.T / p.h < (p.Lw : ℚ) - 1) :
    (cellCall c hs w).uncertifiedFraction ≤ wideFraction c hs w + unlocalizedFraction c hs w := by
  refine uncertifiedFraction_le _ _ _ fun z hz => ?_
  by_contra hno
  push Not at hno
  obtain ⟨hwide, hloc⟩ := hno
  apply hz
  refine cellCall_certified c hs w z hwin (fun q hq => ?_) hloc
  by_contra hlt
  exact hwide ⟨q, hq, by omega⟩

end Events

/-! ### Averaging over a witness law -/

/-- **The probabilities of the bad events of the proof of `prop:complete`** (paper/paper.tex) under
a probability distribution on witness words of length at most `L`. -/
structure EventBounds (c : Call) {p : Cells.Parameters} (hs : Cells.ParameterRules (callInput c) p) (L : ℕ) where
  Ω : Type
  [fintype : Fintype Ω]
  word : Ω → List Bool
  length_le : ∀ ω, (word ω).length ≤ L
  P : Ω → ℝ
  nonneg : ∀ ω, 0 ≤ P ω
  total : ∑ ω, P ω = 1
  /-- `lem:smaskmass` (paper/paper.tex): `Pr[smask = 0] ≤ (W/(d^*(b+1)))² ≤ β/48`. -/
  structural : ∑ ω, P ω * structuralMass c hs (word ω) ≤ (c.radius : ℝ) / 48
  /-- `lem:meanpop` and Markov's inequality: `Pr[pop > U] ≤ 6 r^{3/2} W/(n^{3/2} U) ≤ β/16`. -/
  population : ∑ ω, P ω * populationMass c hs (word ω) ≤ (c.radius : ℝ) / 16
  /-- `lem:filter`(a): `E Pr[pop ≤ U, X > τ] ≤ (e/4)^{τ+1} ≤ 3β/64`. -/
  filter : ∑ ω, P ω * lightFilteredMass c hs (word ω) ≤ 3 * (c.radius : ℝ) / 64
  /-- `lem:filter`(c): event (i) has probability at most `2^k 2^{-X_max/2} ≤ β/64`. -/
  wide : ∑ ω, P ω * wideFraction c hs (word ω) ≤ (c.radius : ℝ) / 64
  /-- `lem:filter`(b) and `lem:localize`: events (ii) and (iii) have probability at most
  `β/16 + β/8`. -/
  unlocalized : ∑ ω, P ω * unlocalizedFraction c hs (word ω) ≤ 3 * (c.radius : ℝ) / 16

attribute [instance] EventBounds.fintype

/-- Averaging a pointwise bound `g ≤ f₁ + f₂ + f₃` over a distribution. -/
theorem expectation_le_add {Ω : Type} [Fintype Ω] (P g f₁ f₂ f₃ : Ω → ℝ) (hP : ∀ ω, 0 ≤ P ω)
    (h : ∀ ω, g ω ≤ f₁ ω + f₂ ω + f₃ ω) :
    ∑ ω, P ω * g ω ≤ ∑ ω, P ω * f₁ ω + ∑ ω, P ω * f₂ ω + ∑ ω, P ω * f₃ ω := by
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun ω _ => ?_
  have := mul_le_mul_of_nonneg_left (h ω) (hP ω)
  linarith

/-- **The two paragraph bounds of `prop:complete`** (paper/paper.tex): from the probabilities of
the bad events and the window condition, the expected masked mass is at most `β/7` and the expected uncertified
fraction at most `β/4`. -/
noncomputable def witnessLaw_of_eventBounds (c : Call) {p : Cells.Parameters}
    (hs : Cells.ParameterRules (callInput c) p) (L : ℕ)
    (hwin : 487 * (p.m : ℚ) * p.T * NearCubicGates.Close.Counter.ellBar p.ell0 p.h p.T / p.h < (p.Lw : ℚ) - 1)
    (E : EventBounds c hs L) : WitnessLaw c hs L where
  Ω := E.Ω
  word := E.word
  length_le := E.length_le
  P := E.P
  nonneg := E.nonneg
  total := E.total
  maskedMass_le := by
    have hβ : (0 : ℝ) ≤ c.radius := by exact_mod_cast (Cells.ParameterRules.beta_pos hs).le
    have h := expectation_le_add E.P (fun ω => (cellCall c hs (E.word ω)).maskedMass)
      (fun ω => structuralMass c hs (E.word ω)) (fun ω => populationMass c hs (E.word ω))
      (fun ω => lightFilteredMass c hs (E.word ω)) E.nonneg (fun ω => maskedMass_le_events c hs (E.word ω))
    have := E.structural
    have := E.population
    have := E.filter
    linarith
  uncertified_le := by
    have hβ : (0 : ℝ) ≤ c.radius := by exact_mod_cast (Cells.ParameterRules.beta_pos hs).le
    have h := expectation_le_add E.P (fun ω => (cellCall c hs (E.word ω)).uncertifiedFraction)
      (fun ω => wideFraction c hs (E.word ω)) (fun ω => unlocalizedFraction c hs (E.word ω)) (fun _ => 0)
      E.nonneg (fun ω => by
        have := uncertifiedFraction_le_events c hs (E.word ω) hwin
        simpa using this)
    have := E.wide
    have := E.unlocalized
    simp only [mul_zero, Finset.sum_const_zero, add_zero] at h
    linarith

/-- **The probabilistic part of `prop:complete` for every call meeting its hypotheses, from the event
probabilities**: `ParagraphBounds L` holds as soon as every such call has a witness law with the event bounds. -/
theorem paragraphBounds_of_events (L : ℕ → ℕ)
    (hE : ∀ (c : Call) (p : Cells.Parameters) (hs : Cells.ParameterRules (callInput c) p), Shaped c →
      CompletenessConditions c p → Nonempty (EventBounds c hs (L c.n))) :
    ParagraphBounds L := by
  intro c p hs hc hcond
  obtain ⟨E⟩ := hE c p hs hc hcond
  exact ⟨witnessLaw_of_eventBounds c hs (L c.n) hcond.window E⟩

end NearQuarticWires.Builder
