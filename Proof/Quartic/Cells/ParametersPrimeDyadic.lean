import Mathlib.NumberTheory.Bertrand

set_option autoImplicit false

namespace NearQuarticWires.Cells.PrimeArithmetic

open Nat Finset
open scoped BigOperators

/-- The primes in one doubled interval used for the window in
`sec:params`, paper/paper.tex. -/
def doubledIntervalPrimes (n : ℕ) : Finset ℕ := (Ioc n (2 * n)).filter Nat.Prime

/-- The prime factors of the central binomial coefficient split
into the small range and the doubled interval. This keeps all the
large primes, rather than assuming that the interval is empty,
as needed for the density bound in `lem:asymptotics`,
paper/paper.tex. -/
theorem centralBinom_split (n : ℕ) (hn : 2 < n) :
    centralBinom n =
      (∏ p ∈ range (2 * n / 3 + 1), p ^ (centralBinom n).factorization p) *
      (∏ p ∈ doubledIntervalPrimes n, p ^ (centralBinom n).factorization p) := by
  let A := range (2 * n / 3 + 1)
  let B := doubledIntervalPrimes n
  let f := fun p => p ^ (centralBinom n).factorization p
  have hA : A ⊆ range (2 * n + 1) := by
    intro p hp
    simp only [A, mem_range] at hp ⊢
    have := Nat.div_le_self (2 * n) 3
    omega
  have hB : B ⊆ range (2 * n + 1) := by
    intro p hp
    have h := (mem_filter.mp hp).1
    simp only [mem_Ioc] at h
    simp only [mem_range]
    omega
  have hdis : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    have h := (mem_filter.mp hq).1
    simp only [mem_Ioc] at h
    simp only [A, mem_range] at hp
    omega
  have hsub : A ∪ B ⊆ range (2 * n + 1) := union_subset hA hB
  have hprod : (∏ p ∈ A ∪ B, f p) = ∏ p ∈ range (2 * n + 1), f p := by
    apply Finset.prod_subset hsub
    intro p hp hnot
    by_cases hprime : p.Prime
    · have hpR : p ≤ 2 * n := by simpa only [mem_range, Nat.lt_succ_iff] using hp
      have hpn : p ≤ n := by
        by_contra hpn
        apply hnot
        apply mem_union_right
        exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨by omega, hpR⟩, hprime⟩
      have hpA : p ∉ A := fun hm => hnot (mem_union_left _ hm)
      have hlarge : 2 * n < 3 * p := by
        simp only [A, mem_range] at hpA
        omega
      dsimp [f]
      rw [factorization_centralBinom_of_two_mul_self_lt_three_mul hn hpn hlarge, pow_zero]
    · dsimp [f]
      rw [factorization_eq_zero_of_not_prime _ hprime, pow_zero]
  calc
    centralBinom n = ∏ p ∈ range (2 * n + 1), f p := n.prod_pow_factorization_centralBinom.symm
    _ = ∏ p ∈ A ∪ B, f p := hprod.symm
    _ = (∏ p ∈ A, f p) * ∏ p ∈ B, f p := prod_union hdis

/-- The small prime factors satisfy the elementary primorial
bound used in `lem:asymptotics`, paper/paper.tex. -/
theorem centralBinom_small_product_le (n : ℕ) (hn : 2 < n) :
    (∏ p ∈ range (2 * n / 3 + 1), p ^ (centralBinom n).factorization p) ≤
      (2 * n) ^ sqrt (2 * n) * 4 ^ (2 * n / 3) := by
  have n_pos : 0 < n := (Nat.zero_le _).trans_lt hn
  have n2_pos : 1 ≤ 2 * n := mul_pos (zero_lt_two' ℕ) n_pos
  let S := {p ∈ range (2 * n / 3 + 1) | Nat.Prime p}
  let f := fun p => p ^ (centralBinom n).factorization p
  have hfilter : ∏ p ∈ S, f p = ∏ p ∈ range (2 * n / 3 + 1), f p := by
    refine prod_filter_of_ne fun p _ h => ?_
    contrapose h
    dsimp only [f]
    rw [factorization_eq_zero_of_not_prime n.centralBinom h, pow_zero]
  rw [← hfilter, ← prod_filter_mul_prod_filter_not S (· ≤ sqrt (2 * n))]
  apply mul_le_mul'
  · refine (prod_le_prod' fun p _ => (?_ : f p ≤ 2 * n)).trans ?_
    · exact pow_factorization_choose_le (mul_pos two_pos n_pos)
    have hc : (Icc 1 (sqrt (2 * n))).card = sqrt (2 * n) := by rw [card_Icc, Nat.add_sub_cancel]
    rw [prod_const]
    refine pow_right_mono₀ n2_pos ((card_le_card fun p hp => ?_).trans hc.le)
    obtain ⟨h1, h2⟩ := mem_filter.mp hp
    exact mem_Icc.mpr ⟨(mem_filter.mp h1).2.one_lt.le, h2⟩
  · refine le_trans ?_ (primorial_le_four_pow (2 * n / 3))
    refine (prod_le_prod' fun p hp => (?_ : f p ≤ p)).trans ?_
    · obtain ⟨h1, h2⟩ := mem_filter.mp hp
      refine (pow_right_mono₀ (mem_filter.mp h1).2.one_lt.le ?_).trans (pow_one p).le
      exact Nat.factorization_choose_le_one (sqrt_lt'.mp (not_le.mp h2))
    refine prod_le_prod_of_subset_of_one_le' (filter_subset _ _) ?_
    exact fun p hp _ => (mem_filter.mp hp).2.one_lt.le

/-- A quantitative central-binomial bound retains the number of
actual interval primes. It is the elementary density input for
`lem:asymptotics`, paper/paper.tex. -/
theorem centralBinom_interval_count_bound (n : ℕ) (hn : 2 < n) :
    centralBinom n ≤ (2 * n) ^ sqrt (2 * n) * 4 ^ (2 * n / 3) *
      (2 * n) ^ (doubledIntervalPrimes n).card := by
  rw [centralBinom_split n hn]
  apply Nat.mul_le_mul (centralBinom_small_product_le n hn)
  calc
    (∏ p ∈ doubledIntervalPrimes n, p ^ (centralBinom n).factorization p) ≤
        ∏ _p ∈ doubledIntervalPrimes n, (2 * n) :=
      prod_le_prod' fun _ _ => pow_factorization_choose_le (by omega : 0 < 2 * n)
    _ = _ := by rw [prod_const]

end NearQuarticWires.Cells.PrimeArithmetic
