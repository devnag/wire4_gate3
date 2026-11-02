import Proof.Quartic.Builder.Localize

/-!
# The law of the vectors `ξ`: nested subsampling by uniform draws

Paper: proof of `prop:complete`, paper/paper.tex ("the vectors `ξ^{(j)}_{r,t} = 1[υ_t ≤ π_r]` with
independent uniform `υ`'s, independently of `𝒮` and between circuits"); `lem:localize`.

Every occurrence label gets one uniform draw `υ_t ∈ [M_1]`, the labels of `C¹` and of `C²` in two independent blocks,
and `ξ_{i,t} = 1[υ_t < A_i]` where `A_i / M_1 = π_{i+1}` is the rate of stage `i + 1` (`Walks.publicSampledSum`, with
the cutoffs `NestedRateChain.product` of the public chain). `drawLaw` is the induced law of `ξ`; expectations under it
are averages over the draws (`expect_drawLaw`), and an average of a function of one circuit's block is the average
over that block (`mean_fst`, `mean_snd`).
-/

set_option autoImplicit false

namespace NearQuarticWires.Builder

open Finset
open NearCubicWires NearCubicWires.WireExponent3_5.Shared
open NearCubicGates.Close.Interfaces
open NearCubicGates.FiniteAverages NearCubicGates.PublishedSources.Witness
open NearCubicGates.PublicSamplingRates NearCubicGates.NestedRateChain

section Law

variable (c : Call) (p : Cells.Parameters)

/-- The common denominator `M_1` of the stage rates, the size of one uniform draw. -/
noncomputable abbrev drawSize : ℕ := denominator (p.T : ℝ) (p.h : ℝ) (p.ell0 : ℝ)

/-- The numerator `A_i = Π_{i' < i} a_{i'+1}` of the rate `π_{i+1} = A_i / M_1` of stage `i + 1`. -/
noncomputable def cutoff (i : ℕ) : ℕ := product (initialRatio (p.T : ℝ) (p.h : ℝ) (p.ell0 : ℝ)) i

/-- A draw: one uniform value in `[M_1]` for every occurrence of `C¹` and every occurrence of `C²`. -/
abbrev Draw := (Fin c.first.gates.length → Fin (drawSize p)) × (Fin c.second.gates.length → Fin (drawSize p))

theorem allGates_length : (allGates c).length = c.first.gates.length + c.second.gates.length := by
  simp [allGates]

/-- The vectors `ξ_{i,t} = 1[υ_t < A_i]` of a draw, over all occurrence labels (those of `C¹` first). -/
noncomputable def xiOf (d : Draw c p) : Fin p.J → Fin (allGates c).length → Bool := fun i t =>
  if h : (t : ℕ) < c.first.gates.length then decide (((d.1 ⟨t, h⟩ : Fin (drawSize p)) : ℕ) < cutoff p i)
  else decide (((d.2 ⟨(t : ℕ) - c.first.gates.length, by
    have := lt_of_lt_of_eq t.isLt (allGates_length c); omega⟩ : Fin (drawSize p)) : ℕ) < cutoff p i)

/-- **The law of the vectors `ξ`** (`prop:complete`, paper/paper.tex): the probability of `ξ` under uniform draws. -/
noncomputable def drawLaw (ξ : Fin p.J → Fin (allGates c).length → Bool) : ℝ :=
  mean fun d : Draw c p => indicator (xiOf c p d = ξ)

theorem drawLaw_nonneg (ξ : Fin p.J → Fin (allGates c).length → Bool) : 0 ≤ drawLaw c p ξ := by
  unfold drawLaw mean
  apply div_nonneg _ (Nat.cast_nonneg _)
  exact Finset.sum_nonneg fun d _ => by unfold indicator; split_ifs <;> norm_num

/-- Expectations under `drawLaw` are averages over the draws. -/
theorem expect_drawLaw (g : (Fin p.J → Fin (allGates c).length → Bool) → ℝ) :
    ∑ ξ, drawLaw c p ξ * g ξ = mean fun d : Draw c p => g (xiOf c p d) := by
  classical
  have h1 : ∀ ξ, drawLaw c p ξ * g ξ = mean fun d : Draw c p => g ξ * indicator (xiOf c p d = ξ) := by
    intro ξ
    unfold drawLaw
    rw [mean_smul, mul_comm]
  simp only [h1]
  rw [← mean_finset_sum]
  congr 1
  funext d
  rw [Finset.sum_eq_single (xiOf c p d)]
  · unfold indicator
    rw [if_pos rfl, mul_one]
  · intro ξ _ hξ
    unfold indicator
    rw [if_neg (Ne.symm hξ), mul_zero]
  · simp

variable {c p}

/-- A draw exists: `M_1 ≥ 1`. -/
theorem drawSize_pos {x : Cells.ParameterInput} (hs : Cells.ParameterRules x p) : 0 < drawSize p := by
  have hT : (0 : ℝ) < p.T := by exact_mod_cast Cells.ParameterRules.T_pos hs
  have hh : 64 * (p.T : ℝ) ≤ p.h := by exact_mod_cast hs.height
  exact (denominator_bounds _ _ _ hT hh).1

theorem sum_drawLaw {x : Cells.ParameterInput} (hs : Cells.ParameterRules x p) : ∑ ξ, drawLaw c p ξ = 1 := by
  haveI : Nonempty (Fin (drawSize p)) := ⟨⟨0, drawSize_pos hs⟩⟩
  have h := expect_drawLaw c p (fun _ => 1)
  simp only [mul_one] at h
  rw [h, mean_const]

/-- The average of a function of the draws of `C¹` is its average over those draws. -/
theorem mean_fst {x : Cells.ParameterInput} (hs : Cells.ParameterRules x p)
    (f : (Fin c.first.gates.length → Fin (drawSize p)) → ℝ) :
    (mean fun d : Draw c p => f d.1) = mean f := by
  haveI : Nonempty (Fin (drawSize p)) := ⟨⟨0, drawSize_pos hs⟩⟩
  rw [mean_prod]
  simp only
  rw [mean_const]

/-- The average of a function of the draws of `C²` is its average over those draws. -/
theorem mean_snd {x : Cells.ParameterInput} (hs : Cells.ParameterRules x p)
    (f : (Fin c.second.gates.length → Fin (drawSize p)) → ℝ) :
    (mean fun d : Draw c p => f d.2) = mean f := by
  haveI : Nonempty (Fin (drawSize p)) := ⟨⟨0, drawSize_pos hs⟩⟩
  rw [mean_prod]
  simp only [mean_const]

end Law

/-! ### The column data under a witness word of the law -/

section Word

variable (c : Call) {p : Cells.Parameters} (hs : Cells.ParameterRules (callInput c) p)

/-- The center of column `z` in the partition of `lem:meanpop`. -/
noncomputable def goodCenter (z : Fin (2 ^ (c.n - p.k))) : BitInput c.n :=
  centerOf c hs (goodTranslation c hs) z

theorem center_word (s : Fin (allGates c).length → Bool) (ξ : Fin p.J → Fin (allGates c).length → Bool)
    (z : Fin (2 ^ (c.n - p.k))) : center c hs (witnessWord c (goodIndex c hs) s ξ) z = goodCenter c hs z := by
  unfold center goodCenter
  rw [translation_goodIndex]

/-- `X = Σ_{(j,i) ∈ 𝒮} |Δ_{j,i}|` for the selection `𝒮` and the partition of `lem:meanpop`. -/
noncomputable def selectedX (s : Fin (allGates c).length → Bool) (z : Fin (2 ^ (c.n - p.k)))
    (q : Sampler.Cell hs.seedParameters.N) : ℕ :=
  ∑ i : Fin (allGates c).length, if s i then
    (Cells.delta (star c hs) ((allGates c)[(i : ℕ)]'i.isLt) (goodCenter c hs z) (pattern c hs q.1)
      (pattern c hs q.2)).natAbs else 0

theorem X_word (s : Fin (allGates c).length → Bool) (ξ : Fin p.J → Fin (allGates c).length → Bool)
    (z : Fin (2 ^ (c.n - p.k))) :
    ((cellCall c hs (witnessWord c (goodIndex c hs) s ξ)).column z).X = selectedX c hs s z := by
  funext q
  show (∑ i : Fin (allGates c).length, if selection c (p := p) (witnessWord c (goodIndex c hs) s ξ) i then
    (Cells.delta (star c hs) ((allGates c)[(i : ℕ)]'i.isLt) (center c hs (witnessWord c (goodIndex c hs) s ξ) z)
      (pattern c hs q.1) (pattern c hs q.2)).natAbs else 0) = _
  rw [selection_witnessWord, center_word]
  rfl

/-- The structural mask of a column, the same for every witness word. -/
theorem structural_eq (w : List Bool) (z : Fin (2 ^ (c.n - p.k))) :
    ((cellCall c hs w).column z).structural = fun q =>
      Mask.structuralMask ((star c hs).flipSet (star c hs).leftBlock) ((star c hs).flipSet (star c hs).rightBlock)
        (Mask.heavyCoordinates (Cells.incidence (allGates c)) p.dstar) (pattern c hs q.1) (pattern c hs q.2) := rfl

theorem tau_eq (w : List Bool) (z : Fin (2 ^ (c.n - p.k))) : ((cellCall c hs w).column z).tau = p.tau := rfl

/-- The structural mask of the star at a point of a cell. -/
def structuralAt (q : Sampler.Cell hs.seedParameters.N) : Bool :=
  Mask.structuralMask ((star c hs).flipSet (star c hs).leftBlock) ((star c hs).flipSet (star c hs).rightBlock)
    (Mask.heavyCoordinates (Cells.incidence (allGates c)) p.dstar) (pattern c hs q.1) (pattern c hs q.2)

/-- The walk mask under a witness word of the law, in terms of the selection only. -/
theorem walkMask_eq (s : Fin (allGates c).length → Bool) (ξ : Fin p.J → Fin (allGates c).length → Bool)
    (z : Fin (2 ^ (c.n - p.k))) (walk : Cycle.Walk hs.seedParameters.N Algorithm.traceOrder) :
    (cellCall c hs (witnessWord c (goodIndex c hs) s ξ)).walkMask z walk =
      Walks.walkMaskInt Algorithm.traceOrder_pos (structuralAt c hs) p.tau (selectedX c hs s z) walk := by
  unfold Algorithm.CellCall.walkMask
  rw [X_word, structural_eq, tau_eq]
  rfl

/-- The walk mask does not depend on the vectors `ξ`. -/
theorem walkMask_word (s : Fin (allGates c).length → Bool) (ξ ξ' : Fin p.J → Fin (allGates c).length → Bool)
    (z : Fin (2 ^ (c.n - p.k))) (walk : Cycle.Walk hs.seedParameters.N Algorithm.traceOrder) :
    (cellCall c hs (witnessWord c (goodIndex c hs) s ξ)).walkMask z walk =
      (cellCall c hs (witnessWord c (goodIndex c hs) s ξ')).walkMask z walk := by
  rw [walkMask_eq, walkMask_eq]

/-- Event (ii) under a witness word of the law, in terms of the selection only. -/
theorem crowded_iff (s : Fin (allGates c).length → Bool) (ξ : Fin p.J → Fin (allGates c).length → Bool)
    (z : Fin (2 ^ (c.n - p.k))) :
    Crowded c hs (witnessWord c (goodIndex c hs) s ξ) z ↔
      ∃ q : Sampler.Cell hs.seedParameters.N, Mask.mask (structuralAt c hs q) p.tau (selectedX c hs s z q) = 1 ∧
        16 * p.U < Cells.population (star c hs) (allGates c) (goodCenter c hs z) (pattern c hs q.1)
          (pattern c hs q.2) := by
  unfold Crowded Algorithm.CellCall.pointMask population
  rw [X_word, center_word, structural_eq, tau_eq]
  exact Iff.rfl

/-- Event (ii) does not depend on the vectors `ξ`. -/
theorem crowded_word (s : Fin (allGates c).length → Bool) (ξ ξ' : Fin p.J → Fin (allGates c).length → Bool)
    (z : Fin (2 ^ (c.n - p.k))) :
    Crowded c hs (witnessWord c (goodIndex c hs) s ξ) z ↔ Crowded c hs (witnessWord c (goodIndex c hs) s ξ') z :=
  (crowded_iff c hs s ξ z).trans (crowded_iff c hs s ξ' z).symm

/-- The contributions `c_{j,t}(z, w, σ)` in the column `z` of the partition of `lem:meanpop`. -/
noncomputable def contributionVector (z : Fin (2 ^ (c.n - p.k))) (j : Fin 2) (σ : Cycle.SignPattern Algorithm.traceOrder)
    (walk : Cycle.Walk hs.seedParameters.N Algorithm.traceOrder) (t : Fin (occurrences c j)) : ℤ :=
  ∑ l, Cycle.signValue (σ l) *
    Cells.delta (star c hs) ((gatesOf c j)[(t : ℕ)]'t.isLt) (goodCenter c hs z)
      (pattern c hs (Cycle.edge Algorithm.traceOrder_pos walk l).1)
      (pattern c hs (Cycle.edge Algorithm.traceOrder_pos walk l).2)

theorem contribution_word (s : Fin (allGates c).length → Bool) (ξ : Fin p.J → Fin (allGates c).length → Bool)
    (z : Fin (2 ^ (c.n - p.k))) (j : Fin 2) (t : Fin (occurrences c j)) (σ : Cycle.SignPattern Algorithm.traceOrder)
    (walk : Cycle.Walk hs.seedParameters.N Algorithm.traceOrder) :
    contribution c hs (witnessWord c (goodIndex c hs) s ξ) z j t σ walk = contributionVector c hs z j σ walk t := by
  unfold contribution contributionVector
  rw [center_word]

/-- The label of occurrence `t` of circuit `j` among all occurrences. -/
def offset (j : Fin 2) (t : Fin (occurrences c j)) : Fin (allGates c).length :=
  ⟨(if j = 0 then 0 else c.first.gates.length) + t, by
    have ht := t.isLt
    fin_cases j
    all_goals simp [occurrences, gatesOf, allGates] at ht ⊢
    all_goals omega⟩

/-- **The conclusion of `lem:localize` for the cell call from the localization event of the public chain**: if the
vectors `ξ` of circuit `j` are the cutoffs of the draws `dd`, the event `Walks.LocalizationEvent` of
`lem:localize` at `(T, h, ℓ_0)` gives `|E_r| ≤ mh` and `|φ| ≤ 172 m A T ℓ̄ / h` for the column data. -/
theorem localizedAt_of_event (s : Fin (allGates c).length → Bool) (ξ : Fin p.J → Fin (allGates c).length → Bool)
    (z : Fin (2 ^ (c.n - p.k))) (walk : Cycle.Walk hs.seedParameters.N Algorithm.traceOrder)
    (σ : Cycle.SignPattern Algorithm.traceOrder) (j : Fin 2) (dd : Fin (occurrences c j) → Fin (drawSize p))
    (hxi : ∀ (i : Fin p.J) t, ξ i (offset c j t) = decide ((dd t : ℕ) < cutoff p i))
    (hev : Walks.LocalizationEvent (p.T : ℝ) (p.h : ℝ) (p.ell0 : ℝ) 4 (p.J - 1)
      (contributionVector c hs z j σ walk) dd) :
    LocalizedAt c hs (witnessWord c (goodIndex c hs) s ξ) z walk σ j := by
  have hJ : 1 ≤ p.J := hs.J_pos
  set W := witnessWord c (goodIndex c hs) s ξ with hW
  have hvals : ∀ i, i ≤ p.J - 1 → ((cellCall c hs W).column z).values j σ walk i =
      Walks.publicSampledSum (p.T : ℝ) (p.h : ℝ) (p.ell0 : ℝ) (contributionVector c hs z j σ walk) dd i := by
    intro i hi
    have hiJ : i < p.J := by omega
    show (∑ t : Fin (occurrences c j), chainBit c (p := p) W j i t * contribution c hs W z j t σ walk) = _
    unfold Walks.publicSampledSum Walks.cutoffSum
    refine Finset.sum_congr rfl fun t _ => ?_
    have hcb : chainBit c (p := p) W j i t = Algorithm.CellCall.bitInt (ξ ⟨i, hiJ⟩ (offset c j t)) :=
      chainBit_witnessWord c (goodIndex c hs) s ξ j ⟨i, hiJ⟩ t
    rw [hcb, hxi, hW, contribution_word]
    unfold Walks.cutoffCoefficient Algorithm.CellCall.bitInt cutoff
    by_cases hlt : ((dd t : ℕ) < product (initialRatio (p.T : ℝ) (p.h : ℝ) (p.ell0 : ℝ)) i) <;> simp [hlt]
  have hCJ : (cellCall c hs W).J = p.J - 1 := rfl
  have hrate : ∀ i, i < p.J - 1 → ((cellCall c hs W).column z).rate i =
      Walks.chainFactor (p.T : ℝ) (p.h : ℝ) (p.ell0 : ℝ) i := fun i hi => rate_eq_chainFactor hs i hi
  constructor
  · intro r
    have h1 := hev.1 r
    have hcongr : ((cellCall c hs W).column z).E j σ walk r =
        NearCubicGates.CountingCore.proposedDigit (Walks.chainFactor (p.T : ℝ) (p.h : ℝ) (p.ell0 : ℝ))
          (Walks.publicSampledSum (p.T : ℝ) (p.h : ℝ) (p.ell0 : ℝ) (contributionVector c hs z j σ walk) dd) r.val := by
      unfold Walks.WalkData.E
      apply proposedDigit_congr
      · intro i hi
        exact hrate i (by have := r.isLt; omega)
      · intro i hi
        exact hvals i (by have := r.isLt; omega)
    rw [hcongr]
    have h2 : (((NearCubicGates.CountingCore.proposedDigit (Walks.chainFactor (p.T : ℝ) (p.h : ℝ) (p.ell0 : ℝ))
        (Walks.publicSampledSum (p.T : ℝ) (p.h : ℝ) (p.ell0 : ℝ) (contributionVector c hs z j σ walk) dd)
          r.val).natAbs : ℕ) : ℝ) ≤ ((4 * p.h : ℕ) : ℝ) := by
      rw [Nat.cast_natAbs, Int.cast_abs]
      push_cast at h1 ⊢
      exact h1
    exact_mod_cast h2
  · have hY : ((cellCall c hs W).column z).Y Algorithm.traceOrder_pos j σ walk =
        ∑ t, contributionVector c hs z j σ walk t := by
      rw [walkSum_eq_sum_contribution]
      exact Finset.sum_congr rfl fun t _ => contribution_word c hs s ξ z j t σ walk
    have hphi : ((cellCall c hs W).column z).phi Algorithm.traceOrder_pos j σ walk =
        Walks.finalError (p.T : ℝ) (p.h : ℝ) (p.ell0 : ℝ)
          (Walks.publicSampledSum (p.T : ℝ) (p.h : ℝ) (p.ell0 : ℝ) (contributionVector c hs z j σ walk) dd)
          (∑ t, contributionVector c hs z j σ walk t) (p.J - 1) := by
      unfold Walks.WalkData.phi Walks.finalError
      rw [hY]
      show (p.M1 : ℤ) * ((cellCall c hs W).column z).values j σ walk (p.J - 1) -
        (p.A : ℤ) * ∑ t, contributionVector c hs z j σ walk t = _
      rw [hvals (p.J - 1) le_rfl, M1_eq_denominator hs, A_eq_product hs]
    rw [hphi]
    have h2 := hev.2
    rw [Nat.cast_natAbs, Int.cast_abs]
    unfold finalRadius
    rw [A_eq_product hs, ellBar_cast]
    push_cast at h2 ⊢
    linarith

end Word

/-! ### `lem:localize` for the cell call under the draw law -/

section Core

variable (c : Call) {p : Cells.Parameters} (hs : Cells.ParameterRules (callInput c) p)

/-- The vectors of the draw at the occurrences of `C¹` are the cutoffs of the first block. -/
theorem xiOf_offset_first (d : Draw c p) (i : Fin p.J) (t : Fin c.first.gates.length) :
    xiOf c p d i (offset c 0 t) = decide (((d.1 t : Fin (drawSize p)) : ℕ) < cutoff p i) := by
  have hv : ((offset c 0 t : Fin (allGates c).length) : ℕ) = t := by simp [offset]
  have h : ((offset c 0 t : Fin (allGates c).length) : ℕ) < c.first.gates.length := by rw [hv]; exact t.isLt
  unfold xiOf
  rw [dif_pos h]
  have he : (⟨((offset c 0 t : Fin (allGates c).length) : ℕ), h⟩ : Fin c.first.gates.length) = t := Fin.ext hv
  rw [he]

/-- The vectors of the draw at the occurrences of `C²` are the cutoffs of the second block. -/
theorem xiOf_offset_second (d : Draw c p) (i : Fin p.J) (t : Fin c.second.gates.length) :
    xiOf c p d i (offset c 1 t) = decide (((d.2 t : Fin (drawSize p)) : ℕ) < cutoff p i) := by
  have hv : ((offset c 1 t : Fin (allGates c).length) : ℕ) = c.first.gates.length + t := by simp [offset]
  have h : ¬ ((offset c 1 t : Fin (allGates c).length) : ℕ) < c.first.gates.length := by rw [hv]; omega
  unfold xiOf
  rw [dif_neg h]
  have he : (⟨((offset c 1 t : Fin (allGates c).length) : ℕ) - c.first.gates.length, by
      have := lt_of_lt_of_eq (offset c 1 t).isLt (allGates_length c); omega⟩ : Fin c.second.gates.length) = t :=
    Fin.ext (by simp only [hv]; omega)
  rw [he]

/-- **`lem:localize` for one circuit** (paper/paper.tex), under the draw law: the probability that a
walk has mask one, the column has no crowded point, and the conclusion of `lem:localize` fails, is at most
`2J e^{-T}`. The circuit's vectors are the cutoffs of its block of draws (`hxi`), and the average over all draws of a
function of that block is its average over the block (`hmarg`). -/
theorem localize_core (bern : Vershynin18_Theorem2_8_4_FiniteBernstein.{0, 0})
    (s : Fin (allGates c).length → Bool) (z : Fin (2 ^ (c.n - p.k)))
    (walk : Cycle.Walk hs.seedParameters.N Algorithm.traceOrder) (σ : Cycle.SignPattern Algorithm.traceOrder)
    (j : Fin 2) (dj : Draw c p → Fin (occurrences c j) → Fin (drawSize p))
    (hxi : ∀ d (i : Fin p.J) t, xiOf c p d i (offset c j t) = decide ((dj d t : ℕ) < cutoff p i))
    (hmarg : ∀ f : (Fin (occurrences c j) → Fin (drawSize p)) → ℝ, (mean fun d => f (dj d)) = mean f) :
    ∑ ξ, drawLaw c p ξ * ind ((cellCall c hs (witnessWord c (goodIndex c hs) s ξ)).walkMask z walk = 1 ∧
      ¬ Crowded c hs (witnessWord c (goodIndex c hs) s ξ) z ∧
      ¬ LocalizedAt c hs (witnessWord c (goodIndex c hs) s ξ) z walk σ j) ≤
      2 * p.J * Real.exp (-(p.T : ℝ)) := by
  classical
  have hJ : 1 ≤ p.J := hs.J_pos
  have hK : 0 ≤ 2 * (p.J : ℝ) * Real.exp (-(p.T : ℝ)) := by positivity
  let ξ0 : Fin p.J → Fin (allGates c).length → Bool := fun _ _ => false
  by_cases hpre : (cellCall c hs (witnessWord c (goodIndex c hs) s ξ0)).walkMask z walk = 1 ∧
      ¬ Crowded c hs (witnessWord c (goodIndex c hs) s ξ0) z
  · -- the hypotheses of `lem:localize` hold on the walk
    have hpop : ∀ l, population c hs (witnessWord c (goodIndex c hs) s ξ0) z
        (Cycle.edge Algorithm.traceOrder_pos walk l) ≤ 16 * p.U := by
      intro l
      have hm := pointMask_of_walkMask c hs (witnessWord c (goodIndex c hs) s ξ0) z walk hpre.1 l
      by_contra h
      exact hpre.2 ⟨_, hm, by omega⟩
    have hb := contribution_bounds c hs (witnessWord c (goodIndex c hs) s ξ0) z j σ walk hpop
    have hc : ∀ t, |contributionVector c hs z j σ walk t| ≤ (2 * 4 : ℕ) := fun t => by
      rw [← contribution_word c hs s ξ0 z j t σ walk]
      exact hb.1 t
    have hmass : (∑ t, |(contributionVector c hs z j σ walk t : ℝ)|) ≤
        liveCap (p.T : ℝ) (p.h : ℝ) (p.ell0 : ℝ) := by
      have h1 : (∑ t, |contributionVector c hs z j σ walk t|) ≤ (32 * Algorithm.traceOrder * p.U : ℕ) := by
        have := hb.2
        simp only [contribution_word] at this
        exact this
      have h3 : (∑ t, |(contributionVector c hs z j σ walk t : ℝ)|) ≤ ((32 * Algorithm.traceOrder * p.U : ℕ) : ℝ) := by
        have := (Int.cast_le (R := ℝ)).mpr h1
        push_cast at this ⊢
        linarith
      refine h3.trans ?_
      have h4 : ((32 * Algorithm.traceOrder * p.U : ℕ) : ℝ) = (p.ell0 : ℝ) := by
        rw [hs.ell0_eq, hs.m_eq]
        push_cast
        ring
      rw [h4]
      exact le_max_left _ _
    have hT : (0 : ℝ) < p.T := by exact_mod_cast Cells.ParameterRules.T_pos hs
    have hh : 64 * (p.T : ℝ) ≤ p.h := by exact_mod_cast hs.height
    have hloc := Walks.chain_localization_failure_bound bern (p.T : ℝ) (p.h : ℝ) (p.ell0 : ℝ) hT hh 4
      (by norm_num) (contributionVector c hs z j σ walk) hc hmass (p.J - 1) (chain_active hs) (chain_stopped hs)
    rw [expect_drawLaw]
    calc (mean fun d : Draw c p =>
          ind ((cellCall c hs (witnessWord c (goodIndex c hs) s (xiOf c p d))).walkMask z walk = 1 ∧
            ¬ Crowded c hs (witnessWord c (goodIndex c hs) s (xiOf c p d)) z ∧
            ¬ LocalizedAt c hs (witnessWord c (goodIndex c hs) s (xiOf c p d)) z walk σ j))
        ≤ mean fun d : Draw c p => indicator (¬ Walks.LocalizationEvent (p.T : ℝ) (p.h : ℝ) (p.ell0 : ℝ) 4
            (p.J - 1) (contributionVector c hs z j σ walk) (dj d)) := by
          apply mean_le_mean
          intro d
          by_cases hL : Walks.LocalizationEvent (p.T : ℝ) (p.h : ℝ) (p.ell0 : ℝ) 4 (p.J - 1)
              (contributionVector c hs z j σ walk) (dj d)
          · have hloc' := localizedAt_of_event c hs s (xiOf c p d) z walk σ j (dj d) (hxi d) hL
            have : ind ((cellCall c hs (witnessWord c (goodIndex c hs) s (xiOf c p d))).walkMask z walk = 1 ∧
                ¬ Crowded c hs (witnessWord c (goodIndex c hs) s (xiOf c p d)) z ∧
                ¬ LocalizedAt c hs (witnessWord c (goodIndex c hs) s (xiOf c p d)) z walk σ j) = 0 := by
              unfold ind
              rw [if_neg (fun h => h.2.2 hloc')]
            rw [this]
            unfold indicator
            split_ifs
            norm_num
          · have : indicator (¬ Walks.LocalizationEvent (p.T : ℝ) (p.h : ℝ) (p.ell0 : ℝ) 4 (p.J - 1)
                (contributionVector c hs z j σ walk) (dj d)) = 1 := by
              unfold indicator
              rw [if_pos hL]
            rw [this]
            exact ind_le_one _
      _ = mean fun dd : Fin (occurrences c j) → Fin (drawSize p) =>
            indicator (¬ Walks.LocalizationEvent (p.T : ℝ) (p.h : ℝ) (p.ell0 : ℝ) 4 (p.J - 1)
              (contributionVector c hs z j σ walk) dd) :=
          hmarg (fun dd => indicator (¬ Walks.LocalizationEvent (p.T : ℝ) (p.h : ℝ) (p.ell0 : ℝ) 4 (p.J - 1)
            (contributionVector c hs z j σ walk) dd))
      _ ≤ 2 * ((p.J - 1 + 1 : ℕ) : ℝ) * Real.exp (-(p.T : ℝ)) := hloc
      _ = 2 * p.J * Real.exp (-(p.T : ℝ)) := by rw [Nat.sub_add_cancel hJ]
  · -- the hypotheses fail for every `ξ`, and the event is empty
    have h0 : ∀ ξ, ind ((cellCall c hs (witnessWord c (goodIndex c hs) s ξ)).walkMask z walk = 1 ∧
        ¬ Crowded c hs (witnessWord c (goodIndex c hs) s ξ) z ∧
        ¬ LocalizedAt c hs (witnessWord c (goodIndex c hs) s ξ) z walk σ j) = 0 := by
      intro ξ
      unfold ind
      rw [if_neg]
      rintro ⟨h1, h2, _⟩
      apply hpre
      refine ⟨?_, (crowded_word c hs s ξ ξ0 z).not.mp h2⟩
      rw [← walkMask_word c hs s ξ ξ0 z walk]
      exact h1
    simp only [h0, mul_zero, Finset.sum_const_zero]
    exact hK

/-- **`lem:localize` for the cell call under the draw law** (paper/paper.tex), given
the finite Bernstein inequality of the statement's inputs. -/
theorem localizeLaw_drawLaw (bern : Vershynin18_Theorem2_8_4_FiniteBernstein.{0, 0}) :
    LocalizeLaw c hs (drawLaw c p) := by
  intro s z walk σ j _ _
  fin_cases j
  · exact localize_core c hs bern s z walk σ 0 Prod.fst (fun d i t => xiOf_offset_first c d i t) (mean_fst hs)
  · exact localize_core c hs bern s z walk σ 1 Prod.snd (fun d i t => xiOf_offset_second c d i t) (mean_snd hs)

end Core

end NearQuarticWires.Builder
