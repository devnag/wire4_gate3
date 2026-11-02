import Proof.Quartic.Cells.AsymptoticsBundle

set_option autoImplicit false

namespace NearQuarticWires.Cells.CoreRules

variable {x : ParameterInput} {p : Parameters}

/-- The unpadded sample census in `prop:time`, paper/paper.tex: the actual eight-fold expansion has at most
`2^(6k+O(lambda))` choices. -/
theorem sample_choice_census (hs : CoreRules x p) (B1 : ℕ)
    (hb : 1 ≤ x.beta * (x.n : ℚ) ^ B1) :
    (p.Q + 1) ^ 8 ≤ 2 ^ (6 * p.k + (8 * (2 * B1 + 100) + 8) * p.lambda) := by
  have hQ : 0 < p.Q := by rw [hs.Q_eq]; positivity
  have hq := hs.Qexp_four_upper B1 hb
  have hL := hs.logarithms_pos.1
  calc
    (p.Q + 1) ^ 8 ≤ (2 * p.Q) ^ 8 := Nat.pow_le_pow_left (by omega) _
    _ = 2 ^ (8 + 8 * p.Qexp) := by
      rw [hs.Q_eq, mul_pow, ← pow_mul, ← pow_add]
      congr 1
      omega
    _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by nlinarith only [hq, hL])

/-- The combined walk and unpadded sample census in `prop:time`,
paper/paper.tex: the exact `2^(mk)(Q+1)^(2m)`
factor has exponent `10k+O(lambda)` at `m=4`. -/
theorem walk_sample_census (hs : CoreRules x p) (B1 : ℕ)
    (hb : 1 ≤ x.beta * (x.n : ℚ) ^ B1) :
    2 ^ (p.m * p.k) * (p.Q + 1) ^ (2 * p.m) ≤
      2 ^ (10 * p.k + (8 * (2 * B1 + 100) + 8) * p.lambda) := by
  rw [hs.m_eq]
  norm_num only [show 2 * (4 : ℕ) = 8 by norm_num]
  calc
    _ ≤ 2 ^ (4 * p.k) * 2 ^ (6 * p.k + (8 * (2 * B1 + 100) + 8) * p.lambda) :=
      Nat.mul_le_mul_left _ (hs.sample_choice_census B1 hb)
    _ = _ := by rw [← pow_add]; congr 1; ring

end NearQuarticWires.Cells.CoreRules

namespace NearQuarticWires.Cells.ParameterRules

open scoped BigOperators

variable {x : ParameterInput} {p : Parameters}

/-- The table-construction term in `prop:time`, paper/paper.tex: the literal printer degree budget pays the doubled
occurrence exponent in the actual construction cost. -/
theorem table_building_census (hs : ParameterRules x p) :
    2 ^ (p.m * p.k) * p.Uocc ^ (2 * p.Dmax) ≤ 2 ^ ((x.n - p.k) / 50) := by
  have h := hs.printing_entries p.Dmax le_rfl
  calc
    _ ≤ 2 ^ (2 * (p.m * p.k)) * p.Uocc ^ (2 * p.Dmax) :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by omega))
    _ = (2 ^ (p.m * p.k) * p.Uocc ^ p.Dmax) ^ 2 := by
      rw [mul_pow, ← pow_mul, ← pow_mul]
      simp only [Nat.mul_comm 2]
    _ ≤ (2 ^ ((x.n - p.k) / 100)) ^ 2 := Nat.pow_le_pow_left h _
    _ = 2 ^ (2 * ((x.n - p.k) / 100)) := by rw [← pow_mul]; congr 1; omega
    _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- The prime-list census in `prop:time`, paper/paper.tex: the actual selected list has at most `P` entries. -/
theorem prime_card_le (hs : ParameterRules x p) : p.primes.card ≤ p.P := by
  have hsub : p.primes ⊆ Finset.Icc 1 p.P := by
    intro q hq
    rw [hs.primes_eq] at hq
    obtain ⟨hle, hprime, _⟩ := (NearCubicGates.Close.Counter.mem_dyadicPrimes p.P q).mp hq
    exact Finset.mem_Icc.mpr ⟨hprime.one_le, hle⟩
  exact (Finset.card_le_card hsub).trans_eq (by simp [Nat.card_Icc])

/-- The scalar-window size used in the exact solver census of
`prop:time`, paper/paper.tex: `Dprime ≤ P²` at
the actual selected prime list. -/
theorem scalar_window_upper (hs : ParameterRules x p) : p.Dprime ≤ p.P ^ 2 := by
  have hsum : ∑ q ∈ p.primes, (q - 1) ≤ p.P * (p.P - 1) := by
    calc
      _ ≤ ∑ _q ∈ p.primes, (p.P - 1) := by
        apply Finset.sum_le_sum
        intro q hq
        rw [hs.primes_eq] at hq
        have hle := ((NearCubicGates.Close.Counter.mem_dyadicPrimes p.P q).mp hq).1
        omega
      _ = p.primes.card * (p.P - 1) := by simp
      _ ≤ _ := Nat.mul_le_mul_right _ hs.prime_card_le
  have hP := hs.prime_candidate.1
  have hpred : p.P - 1 + 1 = p.P := Nat.sub_add_cancel (by omega)
  rw [hs.Dprime_eq]
  unfold NearCubicGates.ScalarWindow.window
  nlinarith

/-- The unknown count in the exact reconstruction systems of
`prop:time`, paper/paper.tex: the actual clipped
window has at most `P⁴` pair unknowns. -/
theorem reconstruction_unknowns (hs : ParameterRules x p) : p.Lw ^ 2 ≤ p.P ^ 4 := by
  have hL : p.Lw ≤ p.Dprime := by
    rw [hs.Lw_eq]
    unfold NearCubicGates.Close.Counter.windowInUse
    split_ifs
    · exact hs.window_bounds.2.1
    · exact le_rfl
  calc
    p.Lw ^ 2 ≤ p.Dprime ^ 2 := Nat.pow_le_pow_left hL _
    _ ≤ (p.P ^ 2) ^ 2 := Nat.pow_le_pow_left hs.scalar_window_upper _
    _ = p.P ^ 4 := by ring

/-- The table count per conditional-child evaluation in `prop:time`,
paper/paper.tex, expressed in the public input length
and the actual stage bound. -/
theorem prime_table_census (hs : ParameterRules x p) :
    4 ^ p.m * p.primes.card * p.P ^ (2 * p.J + 2) ≤ x.n ^ (2 * p.Jmax + 7) := by
  have hn := hs.input_valid.1
  have hP := hs.prime_candidate.2.1
  have hJ := hs.J_bound
  have hfour : 4 ^ p.m ≤ x.n ^ 4 := by rw [hs.m_eq]; exact Nat.pow_le_pow_left hn _
  have hcard : p.primes.card ≤ x.n := hs.prime_card_le.trans hP
  have hpow : p.P ^ (2 * p.J + 2) ≤ x.n ^ (2 * p.Jmax + 2) := by
    exact (Nat.pow_le_pow_left hP _).trans (Nat.pow_le_pow_right (by omega) (by omega))
  calc
    _ ≤ x.n ^ 4 * x.n * x.n ^ (2 * p.Jmax + 2) := Nat.mul_le_mul (Nat.mul_le_mul hfour hcard) hpow
    _ = _ := by rw [← pow_succ, ← pow_add]; congr 1; omega

/-- The exact-system count in `prop:time`, paper/paper.tex: all certified columns and all bounded digit patterns fit
the first exponential term of the running-time ledger. -/
theorem reconstruction_system_census (hs : ParameterRules x p) :
    2 ^ (x.n - p.k) * 4 ^ p.m * (2 * p.hE) ^ (2 * p.J) ≤
      2 ^ (x.n - p.k) * x.n ^ (2 * p.Jmax + 4) := by
  have hn := hs.input_valid.1
  have hP := hs.prime_candidate.2.1
  have hJ := hs.J_bound
  have hfour : 4 ^ p.m ≤ x.n ^ 4 := by rw [hs.m_eq]; exact Nat.pow_le_pow_left hn _
  have hheight : 2 * p.hE ≤ x.n := by rw [hs.hE_eq]; omega
  have hpow : (2 * p.hE) ^ (2 * p.J) ≤ x.n ^ (2 * p.Jmax) :=
    (Nat.pow_le_pow_left hheight _).trans (Nat.pow_le_pow_right (by omega) (by omega))
  calc
    _ ≤ 2 ^ (x.n - p.k) * x.n ^ 4 * x.n ^ (2 * p.Jmax) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ hfour) hpow
    _ = _ := by rw [pow_add]; ring

end NearQuarticWires.Cells.ParameterRules
