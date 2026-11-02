import Proof.Quartic.Cells.ParametersDimension
import Proof.Quartic.Cycle.ConditionalGamma

set_option autoImplicit false

namespace NearQuarticWires.Cells.CoreRules

variable {x : ParameterInput} {p : Parameters}

/-- `imp:seed` and `sec:params`, paper/paper.tex: the concrete eight-wise generator supplied by the finite parameters. -/
def seedParameters (hs : CoreRules x p) : Cycle.SeedParameters where
  ell := p.ellf
  kh := p.k / 2
  Q := p.Q
  one_le_ell := by rw [hs.ellf_eq]; omega
  k_le := by rw [hs.ellf_eq]; omega
  Q_le := by
    rw [hs.Q_eq]
    apply Nat.pow_le_pow_right (by norm_num)
    rw [hs.ellf_eq]
    omega

/-- `imp:seed` and `sec:params`, paper/paper.tex: the generator's matrix dimension is exactly the selected `N`. -/
theorem seed_N (hs : CoreRules x p) : hs.seedParameters.N = p.N := hs.N_eq.symm

/-- `imp:seed` and `sec:params`, paper/paper.tex: the generator's sample count is exactly the selected `Q`. -/
theorem seed_Q (hs : CoreRules x p) : hs.seedParameters.Q = p.Q := rfl

/-- `imp:seed` and `sec:params`, paper/paper.tex: the generator uses precisely the selected number of seed bits. -/
theorem seed_length (hs : CoreRules x p) : Cycle.seedLength hs.seedParameters = p.S := by
  change 8 * p.ellf = p.S
  rw [hs.S_eq, hs.m_eq]

/-- `imp:seed`, paper/paper.tex: the actual selected
sample generator is eight-wise uniform. -/
theorem seed_kwise (hs : CoreRules x p) :
    NearCubicWires.WireExponent3_5.Shared.KWiseUniform 8 hs.seedParameters.pos :=
  hs.seedParameters.pos_kwise

/-- `imp:seed` and `sec:params`, paper/paper.tex: the actual seed space has precisely `2^S` elements. -/
theorem seed_card (hs : CoreRules x p) :
    Fintype.card hs.seedParameters.Seed = 2 ^ p.S := by
  rw [hs.seedParameters.card_seed]
  change 2 ^ (8 * p.ellf) = 2 ^ p.S
  rw [hs.S_eq, hs.m_eq]

/-- `cor:conditional` and `sec:params`, paper/paper.tex: the exact total absolute numerator mass of every conditional
walk sum is bounded by the selected common exponent. -/
theorem conditional_mass_bound (hs : CoreRules x p) (plen pre : ℕ) :
    (2 : ℚ) * 2 ^ p.S *
      (∑ w : Cycle.Walk hs.seedParameters.N 4,
        |Cycle.conditionalGamma hs.seedParameters plen pre w|) ≤ ((2 ^ p.BN : ℕ) : ℚ) := by
  have hc : Fintype.card (Cycle.Walk hs.seedParameters.N 4) = 2 ^ (p.m * p.k) := by
    rw [hs.seed_N]
    simpa only [hs.m_eq] using hs.walks_card
  have hw (w : Cycle.Walk hs.seedParameters.N 4) :
      |Cycle.conditionalGamma hs.seedParameters plen pre w| ≤ ((p.N ^ 2 * p.Q : ℕ) : ℚ) ^ 8 := by
    have h := Cycle.abs_conditionalGamma_le hs.seedParameters plen pre w
    simpa only [hs.seed_N, hs.seed_Q, Nat.cast_mul, Nat.cast_pow, mul_comm] using h
  have hsum : (∑ w : Cycle.Walk hs.seedParameters.N 4,
      |Cycle.conditionalGamma hs.seedParameters plen pre w|) ≤
        ((2 ^ (p.m * p.k) : ℕ) : ℚ) * ((p.N ^ 2 * p.Q : ℕ) : ℚ) ^ 8 := by
    calc
      _ ≤ ∑ _w : Cycle.Walk hs.seedParameters.N 4, ((p.N ^ 2 * p.Q : ℕ) : ℚ) ^ 8 :=
        Finset.sum_le_sum (fun w _ => hw w)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hc]
  calc
    _ ≤ (2 : ℚ) * 2 ^ p.S *
        (((2 ^ (p.m * p.k) : ℕ) : ℚ) * ((p.N ^ 2 * p.Q : ℕ) : ℚ) ^ 8) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = ((2 ^ p.BN : ℕ) : ℚ) := by
      rw [hs.numerator_power_identity, hs.m_eq]
      push_cast
      ring

end NearQuarticWires.Cells.CoreRules

namespace NearQuarticWires.Cells.ParameterRules

variable {x : ParameterInput} {p : Parameters}

/-- `imp:seed` and `sec:params`, paper/paper.tex: the concrete eight-wise generator supplied by the finite parameters. -/
def seedParameters (hs : ParameterRules x p) : Cycle.SeedParameters :=
  CoreRules.seedParameters (hs : CoreRules x p)

/-- `imp:seed` and `sec:params`, paper/paper.tex: the generator's matrix dimension is exactly the selected `N`. -/
theorem seed_N (hs : ParameterRules x p) : hs.seedParameters.N = p.N :=
  CoreRules.seed_N (hs : CoreRules x p)

/-- `imp:seed` and `sec:params`, paper/paper.tex: the generator's sample count is exactly the selected `Q`. -/
theorem seed_Q (hs : ParameterRules x p) : hs.seedParameters.Q = p.Q :=
  CoreRules.seed_Q (hs : CoreRules x p)

/-- `imp:seed` and `sec:params`, paper/paper.tex: the generator uses precisely the selected number of seed bits. -/
theorem seed_length (hs : ParameterRules x p) : Cycle.seedLength hs.seedParameters = p.S :=
  CoreRules.seed_length (hs : CoreRules x p)

/-- `imp:seed`, paper/paper.tex: the actual selected
sample generator is eight-wise uniform. -/
theorem seed_kwise (hs : ParameterRules x p) :
    NearCubicWires.WireExponent3_5.Shared.KWiseUniform 8 hs.seedParameters.pos :=
  CoreRules.seed_kwise (hs : CoreRules x p)

/-- `imp:seed` and `sec:params`, paper/paper.tex: the actual seed space has precisely `2^S` elements. -/
theorem seed_card (hs : ParameterRules x p) :
    Fintype.card hs.seedParameters.Seed = 2 ^ p.S :=
  CoreRules.seed_card (hs : CoreRules x p)

/-- `cor:conditional` and `sec:params`, paper/paper.tex: the exact total absolute numerator mass of every conditional
walk sum is bounded by the selected common exponent. -/
theorem conditional_mass_bound (hs : ParameterRules x p) (plen pre : ℕ) :
    (2 : ℚ) * 2 ^ p.S *
      (∑ w : Cycle.Walk hs.seedParameters.N 4,
        |Cycle.conditionalGamma hs.seedParameters plen pre w|) ≤ ((2 ^ p.BN : ℕ) : ℚ) :=
  CoreRules.conditional_mass_bound (hs : CoreRules x p) plen pre

/-- `lem:residue` and `sec:params`, paper/paper.tex: every chosen prime power strictly exceeds twice the total
absolute scaled conditional coefficient mass of the actual generator. -/
theorem selected_prime_conditional_mass (hs : ParameterRules x p) (plen pre q : ℕ)
    (hq : q ∈ p.primes) :
    (2 : ℚ) * 2 ^ p.S *
      (∑ w : Cycle.Walk hs.seedParameters.N 4,
        |Cycle.conditionalGamma hs.seedParameters plen pre w|) < (q : ℚ) ^ p.e := by
  apply (hs.conditional_mass_bound plen pre).trans_lt
  exact_mod_cast hs.selected_prime_pow_gt q hq

end NearQuarticWires.Cells.ParameterRules

