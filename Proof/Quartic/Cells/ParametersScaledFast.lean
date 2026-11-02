import Proof.Quartic.Cells.AsymptoticsRuntimeOverhead

set_option autoImplicit false

namespace NearQuarticWires.Cells

open NearCubicGates.Close.Interfaces

/-- The exact `Counter4.fast` conclusion with fixed composition
constants and polynomial setup work, `thm:counter` and `prop:time`,
paper/paper.tex. The ledger hypothesis
refers to the actual canonically selected parameters in every call. -/
theorem fast_of_scaled_parameter_ledger (B1 B2 : ℕ) (budget : Call → List Bool → ℕ)
    (hledger : ∃ K overhead setup onset : ℕ, ∀ (c : Call) (p : Parameters), onset ≤ c.n →
      Transfer.Admitted4 B1 B2 c → Transfer.callWires c ≠ 0 →
      prepare (Builder.callInput c) = some p → ∀ w : List Bool,
        budget c w ≤ K * (Machine.propTimeEnvelope c.n p.k p.Q p.Jmax p.lambda overhead + c.n ^ setup))
    (hzero : ∃ K exponent onset : ℕ, ∀ c : Call, onset ≤ c.n → Transfer.Admitted4 B1 B2 c →
      Transfer.callWires c = 0 → ∀ w : List Bool, budget c w ≤ K * (c.n + 1) ^ exponent) :
    ∃ onset : ℕ, ∀ c : Call, onset ≤ c.n → Transfer.Admitted4 B1 B2 c → ∀ w : List Bool,
      budget c w * c.n ^ NearCubicGates.Target.mu c.n ≤ 2 ^ c.n := by
  obtain ⟨K, overhead, setup, ol, hl⟩ := hledger
  obtain ⟨Kz, exponent, oz, hz⟩ := hzero
  obtain ⟨os, _, hs⟩ := eventual_prepare B1
  obtain ⟨ot, _, ht⟩ := CoreRules.eventual_scaled_time_envelope B1 overhead setup K
  obtain ⟨op, _, hp⟩ := eventual_polynomial_prefactor_fast Kz exponent
  refine ⟨max ol (max oz (max os (max ot op))), ?_⟩
  intro c hn hadm w
  by_cases hW : Transfer.callWires c = 0
  · exact (Nat.mul_le_mul_right _ (hz c (by omega) hadm hW w)).trans (hp c.n (by omega))
  · have hv := callInput_valid c hadm hW
    have hb : 1 ≤ c.radius * (c.n : ℚ) ^ B1 := hadm.2.2.2.2.2.2.2.2.2.1
    obtain ⟨p, hp, hr⟩ := hs (Builder.callInput c) (by change os ≤ c.n; omega) hv hb
    have htime := ht (Builder.callInput c) p (by change ot ≤ c.n; omega) (hr : CoreRules _ p) hb
    rw [hr.mu_eq] at htime
    exact (Nat.mul_le_mul_right _ (hl c p (by omega) hadm hW hp w)).trans htime

end NearQuarticWires.Cells
