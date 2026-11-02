import Proof.Quartic.Cells.ParametersWordBounds

set_option autoImplicit false

namespace NearQuarticWires.Cells.ParameterRules

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Interfaces
open ParameterArithmetic

variable {x : ParameterInput} {p : Parameters}

/-- The chain values stored by `sec:params`, paper/paper.tex, have explicit polynomial value bounds at every admitted
precision, including the lifted reconstruction window. -/
theorem rate_values_preparation_bound (hs : ParameterRules x p) (B1 : ℕ)
    (hb : 1 ≤ x.beta * (x.n : ℚ) ^ B1) :
    (p.M1 ≤ (512 * (B1 + 20000) + 4) * x.n ^ (B1 + 4)) ∧
    (p.A ≤ (512 * (B1 + 20000) + 4) * x.n ^ (B1 + 4)) ∧
    (p.Lambda ≤ (512 * (B1 + 20000) + 5) * (x.n + 1) ^ (B1 + 6)) := by
  have hU := CoreRules.U_preparation_bound (hs : CoreRules x p) B1 hb
  have hn := hs.n_pos
  have hpower : x.n ^ 2 ≤ x.n ^ (B1 + 4) := Nat.pow_le_pow_right hn (by omega)
  have hM : p.M1 ≤ (512 * (B1 + 20000) + 4) * x.n ^ (B1 + 4) := by
    calc
      p.M1 ≤ 512 * p.U + 4 * x.n ^ 2 := hs.M1_preparation_bound
      _ ≤ 512 * ((B1 + 20000) * x.n ^ (B1 + 4)) + 4 * x.n ^ (B1 + 4) :=
        Nat.add_le_add (Nat.mul_le_mul_left _ hU) (Nat.mul_le_mul_left _ hpower)
      _ = _ := by ring
  refine ⟨hM, hs.A_le_M1.trans hM, ?_⟩
  have hNpow : x.n ^ (B1 + 6) ≤ (x.n + 1) ^ (B1 + 6) := Nat.pow_le_pow_left (Nat.le_succ _) _
  have hone : 1 ≤ (x.n + 1) ^ (B1 + 6) := Nat.pow_pos (Nat.succ_pos _)
  calc
    p.Lambda ≤ x.n ^ 2 * p.M1 + 1 := hs.Lambda_preparation_bound
    _ ≤ x.n ^ 2 * ((512 * (B1 + 20000) + 4) * x.n ^ (B1 + 4)) + 1 :=
      Nat.add_le_add_right (Nat.mul_le_mul_left _ hM) _
    _ = (512 * (B1 + 20000) + 4) * x.n ^ (B1 + 6) + 1 := by
      simp only [pow_add]
      ring
    _ ≤ (512 * (B1 + 20000) + 4) * (x.n + 1) ^ (B1 + 6) + (x.n + 1) ^ (B1 + 6) :=
      Nat.add_le_add (Nat.mul_le_mul_left _ hNpow) hone
    _ = _ := by ring

/-- Every actual stored rate factor in `sec:params`, paper/paper.tex, is bounded by the arity. -/
theorem factor_member_preparation_bound (hs : ParameterRules x p) (a : ℕ) (ha : a ∈ p.factors) : a ≤ x.n := by
  rw [hs.factors_eq] at ha
  unfold NearCubicGates.Close.Counter.chainFactors at ha
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp ha
  exact hs.chain_factor_le_n i

/-- The actual serialized rate-factor list of `sec:params`,
paper/paper.tex, has quadratic length in the arity. -/
theorem factor_word_preparation_bound (hs : ParameterRules x p) :
    (listWord natWord p.factors).length ≤ 7 * (x.n + 1) ^ 2 := by
  have hlen := hs.factors_length_preparation_bound
  have hlenPower : p.factors.length ≤ 2 ^ (x.n + 1) := hlen.trans Nat.lt_two_pow_self.le
  have hvalues : ∀ a ∈ p.factors, a ≤ 2 ^ (x.n + 1) := by
    intro a ha
    exact (hs.factor_member_preparation_bound a ha).trans
      ((Nat.le_succ x.n).trans Nat.lt_two_pow_self.le)
  have hword := listWord_nat_length_of_power_bounds p.factors (x.n + 1) hlenPower hvalues
  have hscale := Nat.mul_le_mul_right (2 * (x.n + 1) + 3) (show p.factors.length + 1 ≤ x.n + 2 by omega)
  nlinarith only [hword, hscale, hs.input_valid.1]

/-- The actual serialized prime list of `sec:params`,
paper/paper.tex, has quadratic length in the arity. -/
theorem prime_word_preparation_bound (hs : ParameterRules x p) :
    (listWord natWord (p.primes.sort (· ≤ ·))).length ≤ 7 * (x.n + 1) ^ 2 := by
  have hcard : p.primes.card ≤ x.n := hs.prime_card_le.trans hs.prime_candidate.2.1
  have hlen : (p.primes.sort (· ≤ ·)).length ≤ x.n + 1 := by simpa only [Finset.length_sort] using hcard.trans (Nat.le_succ _)
  have hlenPower : (p.primes.sort (· ≤ ·)).length ≤ 2 ^ (x.n + 1) := hlen.trans Nat.lt_two_pow_self.le
  have hvalues : ∀ q ∈ p.primes.sort (· ≤ ·), q ≤ 2 ^ (x.n + 1) := by
    intro q hq
    have hmem : q ∈ p.primes := by simpa only [Finset.mem_sort] using hq
    rw [hs.primes_eq] at hmem
    have hqP := ((NearCubicGates.Close.Counter.mem_dyadicPrimes p.P q).mp hmem).1
    exact (hqP.trans hs.prime_candidate.2.1).trans
      ((Nat.le_succ x.n).trans Nat.lt_two_pow_self.le)
  have hword := listWord_nat_length_of_power_bounds (p.primes.sort (· ≤ ·)) (x.n + 1) hlenPower hvalues
  have hscale := Nat.mul_le_mul_right (2 * (x.n + 1) + 3)
    (show (p.primes.sort (· ≤ ·)).length + 1 ≤ x.n + 2 by omega)
  nlinarith only [hword, hscale, hs.input_valid.1]

/-- The two exponentially valued fields in `sec:params`,
paper/paper.tex, have quadratic serialized length
at every admitted precision; the record stores their binary words. -/
theorem exponential_field_words_preparation_bound (hs : ParameterRules x p) (B1 : ℕ)
    (hb : 1 ≤ x.beta * (x.n : ℚ) ^ B1) :
    ((natWord p.N).length ≤ 16 * x.n ^ 2 + 3) ∧
    ((natWord p.Q).length ≤ (4 * B1 + 224) * x.n ^ 2 + 3) ∧
    ((natWord p.N).length + (natWord p.Q).length ≤ (4 * B1 + 240) * x.n ^ 2 + 6) := by
  have hL := CoreRules.lambda_le_n (hs : CoreRules x p)
  have hM := hs.mu_le_lambda.trans hL
  have hproduct := Nat.mul_le_mul hM hL
  have hk : p.k ≤ 16 * x.n ^ 2 := by nlinarith only [hs.k_le, hproduct]
  have hN : (natWord p.N).length ≤ p.k + 3 := by
    rw [hs.N_eq]
    have h := natWord_length_of_power_bound (2 ^ (p.k / 2)) (p.k / 2) le_rfl
    omega
  have hQ : (natWord p.Q).length ≤ 2 * p.Qexp + 3 := by
    rw [hs.Q_eq]
    exact natWord_length_of_power_bound _ _ le_rfl
  have hq := hs.Qexp_four_upper B1 hb
  have hnsquare : x.n ≤ x.n ^ 2 := Nat.le_self_pow (by norm_num) _
  have hscale := Nat.mul_le_mul_left (2 * B1 + 100) (hL.trans hnsquare)
  have hq2 : 2 * p.Qexp ≤ (4 * B1 + 224) * x.n ^ 2 := by
    nlinarith only [hq, hk, hscale]
  refine ⟨by omega, by omega, ?_⟩
  nlinarith only [hN, hQ, hk, hq2]

end NearQuarticWires.Cells.ParameterRules
