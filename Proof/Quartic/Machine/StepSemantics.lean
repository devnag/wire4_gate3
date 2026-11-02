import Proof.Quartic.Machine.Interfaces
import Proof.Wire_3_5.SeedFixGreedy

set_option autoImplicit false

namespace NearQuarticWires.Machine

/-- `sec:algorithm`, paper/paper.tex: exact integer conditional
potential sums choose the smaller child, with ties going to zero. -/
def chosenSeed (S : ℕ) (printedConditionalSum : List Bool → ℤ) : List Bool :=
  NearCubicWires.WireExponent3_5.SeedFix.greedyLoop S printedConditionalSum

/-- `sec:algorithm`, paper/paper.tex: the concrete reused greedy
control semantics makes exactly `S` one-bit decisions. -/
theorem chosenSeed_length (S : ℕ) (printedConditionalSum : List Bool → ℤ) :
    (chosenSeed S printedConditionalSum).length = S := by
  unfold chosenSeed
  rw [NearCubicWires.WireExponent3_5.SeedFix.greedyLoop_eq_prefix]
  have h : ∀ (s : ℕ) (R : List Bool → ℤ),
      (NearCubicWires.WireExponent3_5.SeedFix.greedyPrefix s R).length = s := by
    intro s
    induction s with
    | zero => intro R; rfl
    | succ s ih =>
      intro R
      simp only [NearCubicWires.WireExponent3_5.SeedFix.greedyPrefix, List.length_cons, ih]
  exact h S printedConditionalSum

/-- `sec:algorithm`, paper/paper.tex: one sample is a left/right
star-pattern pair; `kh` is the half-width `k/2`. -/
abbrev SamplePair (kh : ℕ) := Fin (2 ^ kh) × Fin (2 ^ kh)

/-- `sec:algorithm`, paper/paper.tex: direct exact averaging of
the sampled predicate or mask. The generator supplies the actual list. -/
def sampleMean {kh : ℕ} (samples : List (SamplePair kh))
    (value : SamplePair kh → ℚ) : ℚ :=
  (samples.map value).sum / samples.length

/-- `sec:algorithm`, paper/paper.tex: exact aggregate inputs to
the output pass.  Bounds and identification with the actual main pass
remain explicit obligations of the producing program. -/
structure OutputPassData where
  n : ℕ
  k : ℕ
  Q : ℕ
  MF : ℕ
  eta : ℚ
  certifiedColumns : ℕ
  maskedAcceptTotal : ℕ
  maskTotal : ℕ

/-- `sec:algorithm`, paper/paper.tex: the unrounded lower endpoint. -/
def outputLower (data : OutputPassData) : ℚ :=
  ((data.maskedAcceptTotal : ℚ) / data.Q -
      2 * data.MF * data.certifiedColumns * data.eta) / 2 ^ (data.n - data.k)

/-- `sec:algorithm`, paper/paper.tex: the unrounded upper endpoint.
The difference `n_col-n_c` is taken over the rationals without truncation. -/
def outputUpper (data : OutputPassData) : ℚ :=
  ((data.maskedAcceptTotal : ℚ) / data.Q + data.certifiedColumns -
      (data.maskTotal : ℚ) / data.Q +
      (2 * data.MF + 1) * data.certifiedColumns * data.eta +
      ((2 : ℚ) ^ (data.n - data.k) - data.certifiedColumns)) /
    2 ^ (data.n - data.k)

/-- `sec:algorithm`, paper/paper.tex: round the lower endpoint
down to the dyadic grid, using exact rational floor. -/
def dyadicFloor (n : ℕ) (q : ℚ) : ℚ :=
  (⌊q * 2 ^ n⌋ : ℤ) / (2 : ℚ) ^ n

/-- `sec:algorithm`, paper/paper.tex: round the upper endpoint
up to the dyadic grid, using exact rational ceiling. -/
def dyadicCeil (n : ℕ) (q : ℚ) : ℚ :=
  (⌈q * 2 ^ n⌉ : ℤ) / (2 : ℚ) ^ n

/-- `sec:algorithm`, paper/paper.tex: the actual rounded center
and radius; this is an unclocked exact semantic definition. -/
def roundedInterval (n : ℕ) (lo hi : ℚ) : ℚ × ℚ :=
  ((dyadicFloor n lo + dyadicCeil n hi) / 2,
    (dyadicCeil n hi - dyadicFloor n lo) / 2)

/-- `prop:sound`, paper/paper.tex: outward dyadic rounding
preserves an already proved unrounded probability interval. -/
theorem roundedInterval_contains (n : ℕ) (lo hi probability : ℚ)
    (hlo : lo ≤ probability) (hhi : probability ≤ hi) :
    |(roundedInterval n lo hi).1 - probability| ≤ (roundedInterval n lo hi).2 := by
  have hp : (0 : ℚ) < 2 ^ n := by positivity
  have hf : dyadicFloor n lo ≤ lo := by
    apply (div_le_iff₀ hp).mpr
    exact Int.floor_le (lo * 2 ^ n)
  have hc : hi ≤ dyadicCeil n hi := by
    apply (le_div_iff₀ hp).mpr
    exact Int.le_ceil (hi * 2 ^ n)
  have hl := hf.trans hlo
  have hh := hhi.trans hc
  rw [abs_sub_le_iff]
  dsimp only [roundedInterval, Prod.fst, Prod.snd]
  constructor <;> linarith

end NearQuarticWires.Machine
