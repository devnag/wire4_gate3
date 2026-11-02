import Proof.Quartic.Cells.AsymptoticsOccurrences
import Proof.Quartic.Cells.Partition

set_option autoImplicit false

namespace NearQuarticWires.Cells.CoreRules

open NearCubicWires.WireExponent3_5.Shared

variable {x : ParameterInput} {p : Parameters}

/-- `sec:params`, paper/paper.tex: the selected number
of blocks is even and is at least sixteen. -/
theorem r_even_large (hs : CoreRules x p) : Even p.r ∧ 16 ≤ p.r := by
  rw [hs.r_eq]
  constructor
  · exact ⟨8 * p.mu, by ring⟩
  · have := hs.logarithms_pos.2
    omega

/-- `imp:partition` and `sec:params`, paper/paper.tex: the actual star partition supplied by the public parameters. -/
def starParams (hs : CoreRules x p) : StarParams where
  n := x.n
  r := p.r
  r_even := hs.r_even_large.1
  two_le_r := by have := hs.r_even_large.2; omega
  four_r_le_n := hs.r_bound

/-- `sec:params`, paper/paper.tex: the partition's
block logarithm agrees with the selected integer. -/
theorem star_s (hs : CoreRules x p) : hs.starParams.s = p.s := hs.s_eq.symm

/-- `sec:params`, paper/paper.tex: the partition's
block length agrees with the selected integer. -/
theorem star_b (hs : CoreRules x p) : hs.starParams.b = p.b := by
  change 2 ^ hs.starParams.s - 1 = p.b
  rw [hs.star_s, hs.b_eq]

/-- `sec:params`, paper/paper.tex: the partition's
inner dimension agrees with the selected integer. -/
theorem star_k (hs : CoreRules x p) : hs.starParams.k = p.k := by
  change p.r * hs.starParams.s = p.k
  rw [hs.star_s, hs.k_eq]

/-- `imp:partition`, paper/paper.tex: the exact number
of translations produced by the selected partition. -/
theorem translations_card (hs : CoreRules x p) :
    Fintype.card hs.starParams.Translation = 2 ^ p.k := by
  rw [hs.starParams.card_translation, hs.star_k]

/-- `imp:partition`, paper/paper.tex: the exact number
of centers in every selected translation. -/
theorem centers_card (hs : CoreRules x p) (sigma : hs.starParams.Translation) :
    Fintype.card {c // hs.starParams.IsCenter sigma c} = 2 ^ (x.n - p.k) := by
  rw [hs.starParams.card_centers sigma, hs.star_k]
  rfl

/-- `imp:partition`, paper/paper.tex: the exact number
of points per selected cell. -/
theorem cell_card (hs : CoreRules x p) :
    Fintype.card (hs.starParams.Errors × hs.starParams.Errors) = 2 ^ p.k := by
  rw [hs.starParams.card_cell, hs.star_k]

/-- `sec:params` and `lem:asymptotics`, paper/paper.tex: the block logarithm is at most the input ceiling logarithm. -/
theorem s_le_lambda (hs : CoreRules x p) : p.s ≤ p.lambda := by
  have hn := hs.n_pos
  have hr : 1 < p.r := by have := hs.r_even_large.2; omega
  have hd : x.n / p.r + 1 ≤ x.n := by have := Nat.div_lt_self hn hr; omega
  rw [hs.s_eq, hs.lambda_eq]
  exact (Nat.log_mono_right hd).trans (Nat.log_le_clog 2 x.n)

/-- `lem:asymptotics`, paper/paper.tex: the actual inner
dimension is bounded by sixteen times the product of the logarithmic scales. -/
theorem k_le (hs : CoreRules x p) : p.k ≤ 16 * p.mu * p.lambda := by
  rw [hs.k_eq, hs.r_eq]
  exact Nat.mul_le_mul_left _ hs.s_le_lambda

/-- `sec:params`, paper/paper.tex: an inactive second
group has precisely the trivial Fourier period. -/
theorem inactive_omega2 (hs : CoreRules x p) (hp : x.pair = false) : p.omega2 = 1 := by
  have hg := hs.input_valid.2.2.2.2.2.2 hp
  rw [hs.omega2_eq, hg]
  simp

end NearQuarticWires.Cells.CoreRules

namespace NearQuarticWires.Cells.ParameterRules

open NearCubicWires.WireExponent3_5.Shared

variable {x : ParameterInput} {p : Parameters}

/-- `sec:params`, paper/paper.tex: the selected number
of blocks is even and is at least sixteen. -/
theorem r_even_large (hs : ParameterRules x p) : Even p.r ∧ 16 ≤ p.r :=
  CoreRules.r_even_large (hs : CoreRules x p)

/-- `imp:partition` and `sec:params`, paper/paper.tex: the actual star partition supplied by the public parameters. -/
def starParams (hs : ParameterRules x p) : StarParams :=
  CoreRules.starParams (hs : CoreRules x p)

/-- `sec:params`, paper/paper.tex: the partition's
block logarithm agrees with the selected integer. -/
theorem star_s (hs : ParameterRules x p) : hs.starParams.s = p.s :=
  CoreRules.star_s (hs : CoreRules x p)

/-- `sec:params`, paper/paper.tex: the partition's
block length agrees with the selected integer. -/
theorem star_b (hs : ParameterRules x p) : hs.starParams.b = p.b :=
  CoreRules.star_b (hs : CoreRules x p)

/-- `sec:params`, paper/paper.tex: the partition's
inner dimension agrees with the selected integer. -/
theorem star_k (hs : ParameterRules x p) : hs.starParams.k = p.k :=
  CoreRules.star_k (hs : CoreRules x p)

/-- `imp:partition`, paper/paper.tex: the exact number
of translations produced by the selected partition. -/
theorem translations_card (hs : ParameterRules x p) :
    Fintype.card hs.starParams.Translation = 2 ^ p.k :=
  CoreRules.translations_card (hs : CoreRules x p)

/-- `imp:partition`, paper/paper.tex: the exact number
of centers in every selected translation. -/
theorem centers_card (hs : ParameterRules x p) (sigma : hs.starParams.Translation) :
    Fintype.card {c // hs.starParams.IsCenter sigma c} = 2 ^ (x.n - p.k) :=
  CoreRules.centers_card (hs : CoreRules x p) sigma

/-- `imp:partition`, paper/paper.tex: the exact number
of points per selected cell. -/
theorem cell_card (hs : ParameterRules x p) :
    Fintype.card (hs.starParams.Errors × hs.starParams.Errors) = 2 ^ p.k :=
  CoreRules.cell_card (hs : CoreRules x p)

/-- `sec:params` and `lem:asymptotics`, paper/paper.tex: the block logarithm is at most the input ceiling logarithm. -/
theorem s_le_lambda (hs : ParameterRules x p) : p.s ≤ p.lambda :=
  CoreRules.s_le_lambda (hs : CoreRules x p)

/-- `lem:asymptotics`, paper/paper.tex: the actual inner
dimension is bounded by sixteen times the product of the logarithmic scales. -/
theorem k_le (hs : ParameterRules x p) : p.k ≤ 16 * p.mu * p.lambda :=
  CoreRules.k_le (hs : CoreRules x p)

/-- `sec:params`, paper/paper.tex: an inactive second
group has precisely the trivial Fourier period. -/
theorem inactive_omega2 (hs : ParameterRules x p) (hp : x.pair = false) : p.omega2 = 1 :=
  CoreRules.inactive_omega2 (hs : CoreRules x p) hp

end NearQuarticWires.Cells.ParameterRules

