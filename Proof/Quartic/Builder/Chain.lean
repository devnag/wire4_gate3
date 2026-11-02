import Proof.Quartic.Builder.Stray
import Proof.Quartic.Walks.ChainProbability

/-!
# The rate chain of the parameters is the public rate chain of `lem:localize`

Paper: `imp:chain`, paper/paper.tex; `sec:params` item 7; `lem:localize`.

The parameters of `sec:params` run the chain of `imp:chain` over `ℚ` (`Counter.firstRatio`, `RationalRateChain.ratio`,
`RationalRateChain.factorRat`, `Counter.stopIndex`); `lem:localize` (`Walks.chain_localization_failure_bound`) is stated
for the same chain over `ℝ` (`PublicSamplingRates.initialRatio`, `NestedRateChain.rateRatio`,
`NestedRateChain.factor`, `NestedRateChain.product`) at `(T, h, ℓ_0)`. This file proves that the two agree on
everything the cell call reads: `ℓ̄` (`ellBar_cast`), `M_1` (`M1_eq_denominator`), `x_1` (`firstRatio_cast`), the
multipliers `a_{i+1}` of the active stages (`rate_eq_chainFactor`), the stopping conditions (`chain_active`,
`chain_stopped`), and `A` (`A_eq_product`).
-/

set_option autoImplicit false

namespace NearQuarticWires.Builder

open NearCubicGates.Close.Counter NearCubicGates.PublicSamplingRates NearCubicGates.NestedRateChain

section Chain

variable {x : Cells.ParameterInput} {p : Cells.Parameters} (hs : Cells.ParameterRules x p)
include hs

omit hs in
/-- `imp:chain`: `ℓ̄ = max{ℓ_0, h²/(256T)}`, over `ℚ` and over `ℝ`. -/
theorem ellBar_cast :
    ((ellBar p.ell0 p.h p.T : ℚ) : ℝ) = liveCap (p.T : ℝ) (p.h : ℝ) (p.ell0 : ℝ) := by
  unfold ellBar liveCap
  push_cast
  rfl

omit hs in
/-- A natural ceiling commutes with the cast `ℚ → ℝ`. -/
theorem natCeil_cast (q : ℚ) : ⌈q⌉₊ = ⌈(q : ℝ)⌉₊ := by
  apply le_antisymm
  · apply Nat.ceil_le.mpr
    have h := Nat.le_ceil (q : ℝ)
    exact_mod_cast h
  · apply Nat.ceil_le.mpr
    have h := Nat.le_ceil q
    exact_mod_cast h

/-- `sec:params` item 7: `M_1 = ⌈4ℓ̄/h⌉` is the public denominator. -/
theorem M1_eq_denominator : p.M1 = denominator (p.T : ℝ) (p.h : ℝ) (p.ell0 : ℝ) := by
  rw [hs.M1_eq]
  unfold firstDen denominator
  rw [natCeil_cast]
  congr 1
  push_cast
  rw [ellBar_cast]

/-- `imp:chain`: the first ratio `x_1 = π_1/π^*`, over `ℚ` and over `ℝ`. -/
theorem firstRatio_cast :
    ((firstRatio p.ell0 p.h p.T : ℚ) : ℝ) = initialRatio (p.T : ℝ) (p.h : ℝ) (p.ell0 : ℝ) := by
  unfold firstRatio initialRatio piStar targetRate
  rw [← M1_eq_denominator hs, ← hs.M1_eq]
  push_cast
  rw [ellBar_cast]

/-- The ratios of the chain, over `ℚ` and over `ℝ`. -/
theorem ratio_cast_chain (i : ℕ) :
    ((NearCubicGates.RationalRateChain.ratio (firstRatio p.ell0 p.h p.T) i : ℚ) : ℝ) =
      rateRatio (initialRatio (p.T : ℝ) (p.h : ℝ) (p.ell0 : ℝ)) i := by
  rw [NearCubicGates.RationalRateChain.ratio_cast _ (Cells.ParameterRules.firstRatio_pos hs), firstRatio_cast hs]

/-- `imp:chain`: the stages before the stopping index are active, `x_i < 2^{-8}`. -/
theorem chain_active (r : ℕ) (hr : r < p.J - 1) :
    rateRatio (initialRatio (p.T : ℝ) (p.h : ℝ) (p.ell0 : ℝ)) r < 1 / 256 := by
  have hmin := (leastUpTo_spec _ _ _ hs.chain_eq).2.2 r hr
  rw [← ratio_cast_chain hs]
  have h : NearCubicGates.RationalRateChain.ratio (firstRatio p.ell0 p.h p.T) r < 1 / 256 := not_le.mp hmin
  have := (Rat.cast_lt (K := ℝ)).mpr h
  push_cast at this
  exact this

/-- `imp:chain`: the stopping stage has `x ≥ 2^{-8}`. -/
theorem chain_stopped : 1 / 256 ≤ rateRatio (initialRatio (p.T : ℝ) (p.h : ℝ) (p.ell0 : ℝ)) (p.J - 1) := by
  have hstop := (leastUpTo_spec _ _ _ hs.chain_eq).1
  rw [← ratio_cast_chain hs]
  have := (Rat.cast_le (K := ℝ)).mpr hstop
  push_cast at this
  exact this

/-- `imp:chain`: the multiplier `a_{i+1}` of an active stage, over `ℚ` and over `ℝ`. -/
theorem rate_eq_chainFactor (i : ℕ) (hi : i < p.J - 1) :
    (NearCubicGates.RationalRateChain.factorRat
      (NearCubicGates.RationalRateChain.ratio (firstRatio p.ell0 p.h p.T) i) : ℤ) =
      Walks.chainFactor (p.T : ℝ) (p.h : ℝ) (p.ell0 : ℝ) i := by
  unfold Walks.chainFactor
  have hpos := NearCubicGates.Close.Counter.ratio_pos _ (Cells.ParameterRules.firstRatio_pos hs) i
  have hsmall : NearCubicGates.RationalRateChain.ratio (firstRatio p.ell0 p.h p.T) i < 1 / 256 :=
    not_le.mp ((leastUpTo_spec _ _ _ hs.chain_eq).2.2 i hi)
  rw [NearCubicGates.RationalRateChain.factorRat_eq _ hpos hsmall, ratio_cast_chain hs]

/-- `imp:chain`: `A = Π_{i < J-1} a_{i+1}` is the public product of the multipliers. -/
theorem A_eq_product : p.A = product (initialRatio (p.T : ℝ) (p.h : ℝ) (p.ell0 : ℝ)) (p.J - 1) := by
  rw [hs.A_eq, hs.factors_eq]
  unfold chainFactors
  have key : ∀ m, m ≤ p.J - 1 →
      ((List.range m).map fun i => NearCubicGates.RationalRateChain.factorRat
        (NearCubicGates.RationalRateChain.ratio (firstRatio p.ell0 p.h p.T) i)).prod =
      product (initialRatio (p.T : ℝ) (p.h : ℝ) (p.ell0 : ℝ)) m := by
    intro m
    induction m with
    | zero => intro _; rfl
    | succ m ih =>
      intro hm
      rw [List.range_succ, List.map_append, List.prod_append, ih (by omega)]
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      show _ = multiplier _ m * product _ m
      unfold multiplier
      rw [if_pos (chain_active hs m (by omega))]
      have h := rate_eq_chainFactor hs m (by omega)
      unfold Walks.chainFactor at h
      have h' : NearCubicGates.RationalRateChain.factorRat
          (NearCubicGates.RationalRateChain.ratio (firstRatio p.ell0 p.h p.T) m) =
          factor (rateRatio (initialRatio (p.T : ℝ) (p.h : ℝ) (p.ell0 : ℝ)) m) := by exact_mod_cast h
      rw [h', Nat.mul_comm]
  exact key _ le_rfl

end Chain

end NearQuarticWires.Builder
