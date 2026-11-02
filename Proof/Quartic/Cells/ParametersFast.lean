import Proof.Quartic.Cells.ParametersBuilderCap
import Proof.Quartic.Cells.AsymptoticsRuntime

set_option autoImplicit false

namespace NearQuarticWires.Cells

open NearCubicGates.Close.Interfaces

/-- `prop:time`, paper/paper.tex: every fixed
polynomial is eventually smaller than the counter's time bound, even
after multiplication by the actual `n^mu` factor. -/
theorem eventual_polynomial_fast (overhead : ℕ) : ∃ onset : ℕ, 4 ≤ onset ∧
    ∀ n : ℕ, onset ≤ n → n ^ overhead * n ^ NearCubicGates.Target.mu n ≤ 2 ^ n := by
  obtain ⟨onset, hon, hpoly⟩ := NearCubicGates.Close.Closure.lambda_poly_lt (overhead + 2) 2
  refine ⟨onset, hon, ?_⟩
  intro n hn
  have hL : 0 < NearCubicGates.Target.lambda n :=
    Nat.clog_pos (by norm_num) (by omega : 1 < n)
  have hmu : NearCubicGates.Target.mu n ≤ NearCubicGates.Target.lambda n :=
    NearCubicGates.Close.Counter.clog_le_self _
  have hmul := Nat.mul_le_mul_right (NearCubicGates.Target.lambda n) hmu
  have hLsquare : NearCubicGates.Target.lambda n ≤ (NearCubicGates.Target.lambda n) ^ 2 := by
    nlinarith only [hL]
  have hover := Nat.mul_le_mul_left overhead hLsquare
  have hnum := hpoly n hn
  have hexp : NearCubicGates.Target.lambda n * (overhead + NearCubicGates.Target.mu n) ≤ n := by
    nlinarith only [hmul, hover, hnum]
  calc
    n ^ overhead * n ^ NearCubicGates.Target.mu n = n ^ (overhead + NearCubicGates.Target.mu n) :=
      (pow_add _ _ _).symm
    _ ≤ (2 ^ NearCubicGates.Target.lambda n) ^ (overhead + NearCubicGates.Target.mu n) :=
      Nat.pow_le_pow_left (Nat.le_pow_clog (by norm_num) n) _
    _ = 2 ^ (NearCubicGates.Target.lambda n * (overhead + NearCubicGates.Target.mu n)) :=
      (pow_mul _ _ _).symm
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hexp

/-- `prop:time`, paper/paper.tex: a polynomial
closed-form branch with a fixed coefficient also meets the same fast
bound for all sufficiently large input lengths. -/
theorem eventual_polynomial_prefactor_fast (K overhead : ℕ) : ∃ onset : ℕ, 4 ≤ onset ∧
    ∀ n : ℕ, onset ≤ n →
      (K * (n + 1) ^ overhead) * n ^ NearCubicGates.Target.mu n ≤ 2 ^ n := by
  obtain ⟨onset, hon, h⟩ := eventual_polynomial_fast (2 * overhead + 1)
  refine ⟨max onset K, by omega, ?_⟩
  intro n hn
  have hK : K ≤ n := by omega
  have hn4 : 4 ≤ n := by omega
  have hbase : n + 1 ≤ n ^ 2 := by nlinarith only [hn4]
  have hcost : K * (n + 1) ^ overhead ≤ n ^ (2 * overhead + 1) := by
    calc
      _ ≤ n * (n ^ 2) ^ overhead := Nat.mul_le_mul hK (Nat.pow_le_pow_left hbase _)
      _ = _ := by rw [← pow_mul, pow_succ]; ring
  exact (Nat.mul_le_mul_right _ hcost).trans (h n (by omega))

/-- The exact `Counter4.fast` conclusion from the actual parameter
ledger and a polynomial zero-wire branch, `thm:counter` and `prop:time`,
paper/paper.tex. All normalized nonzero-wire
calls are included, independently of the completeness cap. -/
theorem fast_of_parameter_ledger (B1 B2 overhead : ℕ) (budget : Call → List Bool → ℕ)
    (hledger : ∃ onset : ℕ, ∀ (c : Call) (p : Parameters), onset ≤ c.n →
      Transfer.Admitted4 B1 B2 c → Transfer.callWires c ≠ 0 →
      prepare (Builder.callInput c) = some p → ∀ w : List Bool,
        budget c w ≤ Machine.propTimeEnvelope c.n p.k p.Q p.Jmax p.lambda overhead)
    (hzero : ∃ K exponent onset : ℕ, ∀ c : Call, onset ≤ c.n → Transfer.Admitted4 B1 B2 c →
      Transfer.callWires c = 0 → ∀ w : List Bool, budget c w ≤ K * (c.n + 1) ^ exponent) :
    ∃ onset : ℕ, ∀ c : Call, onset ≤ c.n → Transfer.Admitted4 B1 B2 c → ∀ w : List Bool,
      budget c w * c.n ^ NearCubicGates.Target.mu c.n ≤ 2 ^ c.n := by
  obtain ⟨ol, hl⟩ := hledger
  obtain ⟨K, exponent, oz, hz⟩ := hzero
  obtain ⟨ot, _, ht⟩ := eventual_prepared_time B1 overhead
  obtain ⟨op, _, hp⟩ := eventual_polynomial_prefactor_fast K exponent
  refine ⟨max ol (max oz (max ot op)), ?_⟩
  intro c hn hadm w
  by_cases hW : Transfer.callWires c = 0
  · exact (Nat.mul_le_mul_right _ (hz c (by omega) hadm hW w)).trans (hp c.n (by omega))
  · have hv := callInput_valid c hadm hW
    have hb : 1 ≤ c.radius * (c.n : ℚ) ^ B1 := hadm.2.2.2.2.2.2.2.2.2.1
    obtain ⟨p, hp, _, htime⟩ := ht (Builder.callInput c) (by change ot ≤ c.n; omega) hv hb
    exact (Nat.mul_le_mul_right _ (hl c p (by omega) hadm hW hp w)).trans htime

end NearQuarticWires.Cells
