import Proof.Quartic.Cells.AsymptoticsResources

set_option autoImplicit false

namespace NearQuarticWires.Cells.ParameterArithmetic

/-- `prop:time`, paper/paper.tex: increasing the
fixed polynomial overhead increases each of the three ledger terms. -/
theorem time_envelope_mono (n k Q J lam a b : ℕ) (hn : 0 < n) (hab : a ≤ b) :
    Machine.propTimeEnvelope n k Q J lam a ≤ Machine.propTimeEnvelope n k Q J lam b := by
  unfold Machine.propTimeEnvelope
  apply Nat.add_le_add (Nat.add_le_add ?_ ?_) ?_
  · exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hn (by omega))
  · exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hn hab)
  · apply Nat.pow_le_pow_right (by norm_num)
    have h := Nat.mul_le_mul_right lam hab
    omega

/-- `prop:time`, paper/paper.tex: the first ledger
term already dominates a polynomial of its fixed overhead degree. -/
theorem polynomial_le_time_envelope (n k Q J lam overhead : ℕ) (hn : 0 < n) :
    n ^ overhead ≤ Machine.propTimeEnvelope n k Q J lam overhead := by
  calc
    n ^ overhead ≤ n ^ (2 * J + overhead) := Nat.pow_le_pow_right hn (by omega)
    _ ≤ 2 ^ (n - k) * n ^ (2 * J + overhead) := Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)
    _ ≤ _ := by
      unfold Machine.propTimeEnvelope
      exact (Nat.le_add_right _ _).trans (Nat.le_add_right _ _)

/-- `prop:time`, paper/paper.tex: one extra
overhead exponent absorbs a factor of the input length in every ledger
term, including the term whose overhead is written in binary length. -/
theorem time_envelope_raise (n k Q J lam overhead : ℕ) (hn : n ≤ 2 ^ lam) :
    n * Machine.propTimeEnvelope n k Q J lam overhead ≤
      Machine.propTimeEnvelope n k Q J lam (overhead + 1) := by
  have hthird : 2 ^ (10 * k + overhead * lam) * n ≤ 2 ^ (10 * k + (overhead + 1) * lam) := by
    calc
      _ ≤ 2 ^ (10 * k + overhead * lam) * 2 ^ lam := Nat.mul_le_mul_left _ hn
      _ = _ := by rw [← pow_add]; congr 1; ring
  unfold Machine.propTimeEnvelope
  rw [show 2 * J + (overhead + 1) = (2 * J + overhead) + 1 by omega, pow_succ, pow_succ]
  nlinarith only [hthird]

end NearQuarticWires.Cells.ParameterArithmetic

namespace NearQuarticWires.Cells.CoreRules

open ParameterArithmetic

/-- `prop:time`, paper/paper.tex: fixed
multiplicative constants and a polynomial setup term are absorbed in
the actual three-term envelope, uniformly for every normalized input. -/
theorem eventual_scaled_time_envelope (B1 overhead setup K : ℕ) :
    ∃ onset : ℕ, 4 ≤ onset ∧ ∀ (x : ParameterInput) (p : Parameters), onset ≤ x.n → CoreRules x p →
      1 ≤ x.beta * (x.n : ℚ) ^ B1 →
      (K * (Machine.propTimeEnvelope x.n p.k p.Q p.Jmax p.lambda overhead + x.n ^ setup)) *
        x.n ^ p.mu ≤ 2 ^ x.n := by
  obtain ⟨onset, hon, h⟩ := eventual_time_envelope B1 (max overhead setup + 1)
  refine ⟨max onset (2 * K), by omega, ?_⟩
  intro x p hn hs hb
  have hnpos := hs.n_pos
  have hnlog : x.n ≤ 2 ^ p.lambda := by rw [hs.lambda_eq]; exact Nat.le_pow_clog (by norm_num) _
  have hmain := time_envelope_mono x.n p.k p.Q p.Jmax p.lambda overhead (max overhead setup)
    hnpos (le_max_left _ _)
  have hsetup := (polynomial_le_time_envelope x.n p.k p.Q p.Jmax p.lambda setup hnpos).trans
    (time_envelope_mono x.n p.k p.Q p.Jmax p.lambda setup (max overhead setup)
      hnpos (le_max_right _ _))
  have hbudget : K * (Machine.propTimeEnvelope x.n p.k p.Q p.Jmax p.lambda overhead + x.n ^ setup) ≤
      Machine.propTimeEnvelope x.n p.k p.Q p.Jmax p.lambda (max overhead setup + 1) := by
    calc
      _ ≤ K * (Machine.propTimeEnvelope x.n p.k p.Q p.Jmax p.lambda (max overhead setup) +
          Machine.propTimeEnvelope x.n p.k p.Q p.Jmax p.lambda (max overhead setup)) :=
        Nat.mul_le_mul_left _ (Nat.add_le_add hmain hsetup)
      _ = (2 * K) * Machine.propTimeEnvelope x.n p.k p.Q p.Jmax p.lambda (max overhead setup) := by ring
      _ ≤ x.n * Machine.propTimeEnvelope x.n p.k p.Q p.Jmax p.lambda (max overhead setup) :=
        Nat.mul_le_mul_right _ (by omega)
      _ ≤ _ := time_envelope_raise x.n p.k p.Q p.Jmax p.lambda _ hnlog
  exact (Nat.mul_le_mul_right _ hbudget).trans (h x p (by omega) hs hb)

end NearQuarticWires.Cells.CoreRules
