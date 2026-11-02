import Proof.Quartic.Machine.Interfaces

set_option autoImplicit false

namespace NearQuarticWires.Machine

/-- `prop:time`, paper/paper.tex: exact finite headroom conditions
absorb the THREE stated terms into `2^n/n^mu`. This proves only the
envelope arithmetic; the actual program-to-envelope ledger is separate. -/
theorem propTimeEnvelope_fast_of_headroom (n k Q Jmax lam exponent mu q : ℕ)
    (hkn : k ≤ n) (hn : n ≤ 2 ^ lam) (hQ : Q ≤ 2 ^ q)
    (hfirst : (2 * Jmax + exponent + mu) * lam + 2 ≤ k)
    (hsecond : q + (exponent + mu) * lam + 2 ≤ k)
    (hthird : 10 * k + (exponent + mu) * lam + 2 ≤ n) :
    propTimeEnvelope n k Q Jmax lam exponent * n ^ mu ≤ 2 ^ n := by
  have hpower (a : ℕ) : n ^ a ≤ 2 ^ (lam * a) := by
    simpa only [pow_mul] using Nat.pow_le_pow_left hn a
  have hA : 4 * (2 ^ (n - k) * n ^ (2 * Jmax + exponent)) * n ^ mu ≤ 2 ^ n := by
    calc
      4 * (2 ^ (n - k) * n ^ (2 * Jmax + exponent)) * n ^ mu =
          2 ^ 2 * 2 ^ (n - k) * n ^ (2 * Jmax + exponent + mu) := by
        rw [pow_add]
        ring
      _ ≤ 2 ^ 2 * 2 ^ (n - k) * 2 ^ (lam * (2 * Jmax + exponent + mu)) :=
        Nat.mul_le_mul_left _ (hpower _)
      _ = 2 ^ (2 + (n - k) + lam * (2 * Jmax + exponent + mu)) := by
        rw [pow_add, pow_add]
      _ ≤ 2 ^ n := by
        apply Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ))
        have he : n - k + k = n := Nat.sub_add_cancel hkn
        nlinarith
  have hB : 4 * (2 ^ (n - k) * Q * n ^ exponent) * n ^ mu ≤ 2 ^ n := by
    calc
      4 * (2 ^ (n - k) * Q * n ^ exponent) * n ^ mu =
          2 ^ 2 * 2 ^ (n - k) * Q * n ^ (exponent + mu) := by
        rw [pow_add]
        ring
      _ ≤ 2 ^ 2 * 2 ^ (n - k) * 2 ^ q * 2 ^ (lam * (exponent + mu)) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ hQ) (hpower _)
      _ = 2 ^ (2 + (n - k) + q + lam * (exponent + mu)) := by
        rw [pow_add, pow_add, pow_add]
      _ ≤ 2 ^ n := by
        apply Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ))
        have he : n - k + k = n := Nat.sub_add_cancel hkn
        nlinarith
  have hC : 4 * 2 ^ (10 * k + exponent * lam) * n ^ mu ≤ 2 ^ n := by
    calc
      4 * 2 ^ (10 * k + exponent * lam) * n ^ mu ≤
          2 ^ 2 * 2 ^ (10 * k + exponent * lam) * 2 ^ (lam * mu) :=
        Nat.mul_le_mul_left _ (hpower _)
      _ = 2 ^ (2 + (10 * k + exponent * lam) + lam * mu) := by
        simp only [pow_add]
      _ ≤ 2 ^ n := by
        apply Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ))
        nlinarith
  have hsum : 4 * (propTimeEnvelope n k Q Jmax lam exponent * n ^ mu) ≤ 3 * 2 ^ n := by
    calc
      4 * (propTimeEnvelope n k Q Jmax lam exponent * n ^ mu) =
          (4 * (2 ^ (n - k) * n ^ (2 * Jmax + exponent)) * n ^ mu +
            4 * (2 ^ (n - k) * Q * n ^ exponent) * n ^ mu) +
            4 * 2 ^ (10 * k + exponent * lam) * n ^ mu := by
        unfold propTimeEnvelope
        ring
      _ ≤ (2 ^ n + 2 ^ n) + 2 ^ n := Nat.add_le_add (Nat.add_le_add hA hB) hC
      _ = 3 * 2 ^ n := by ring
  omega

end NearQuarticWires.Machine
