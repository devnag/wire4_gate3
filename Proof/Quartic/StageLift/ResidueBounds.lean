import Proof.Quartic.StageLift.ResidueFormula
import Proof.Quartic.Cells.ParametersGuards

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open NearCubicWires NearCubicGates.Close.Interfaces NearCubicGates.Close.Tabulator
open NearQuarticWires

/-- `lem:print`, `eq:prime-budget` and `prop:time`, paper/paper.tex: the degree header is
computed from the actual mask, chain and prime request fields. -/
def residueDegreeBound (p : Cells.Parameters) (prime : ℕ) : ℕ :=
  16 * p.Xmax + (2 * p.e - 1) * (2 * (p.J - 1 + 2)) * (prime - 1)

/-- `eq:prime-budget`, paper/paper.tex: every
prime within the selected range preserves the unchanged Dmax budget. -/
theorem residueDegreeBound_le_Dmax {x : Cells.ParameterInput} {p : Cells.Parameters}
    (hs : Cells.ParameterRules x p) (prime : ℕ) (hprime : prime ≤ p.P) :
    residueDegreeBound p prime ≤ p.Dmax := by
  have hj : 2 * (p.J - 1 + 2) ≤ 2 * p.Jmax + 2 := by
    have := hs.J_pos
    have := hs.J_bound
    omega
  have hp : prime - 1 ≤ p.P - 1 := Nat.sub_le_sub_right hprime 1
  calc
    residueDegreeBound p prime ≤
        16 * p.Xmax + (2 * p.e - 1) * (2 * p.Jmax + 2) * (p.P - 1) := by
      exact Nat.add_le_add_left (Nat.mul_le_mul (Nat.mul_le_mul_left _ hj) hp) _
    _ = (2 * p.e - 1) * (2 * p.Jmax + 2) * (p.P - 1) + 4 * p.m * p.Xmax := by
      rw [hs.m_eq]
      ring
    _ ≤ p.Dmax := hs.prime_budget

/-- `sec:params` and `lem:residue`, paper/paper.tex: an actual selected prime and positive lift exponent
give the nontrivial modulus required by the modular compiler. -/
theorem selected_modulus_ge_two {x : Cells.ParameterInput} {p : Cells.Parameters}
    (hs : Cells.ParameterRules x p) (prime : ℕ) (hprime : prime ∈ p.primes) :
    2 ≤ prime ^ p.e := by
  have hp := (hs.selected_prime_guards prime hprime).1.two_le
  calc
    2 = 2 ^ 1 := by simp
    _ ≤ 2 ^ p.e := Nat.pow_le_pow_right (by decide) hs.e_pos
    _ ≤ prime ^ p.e := Nat.pow_le_pow_left hp _

/-- `lem:print`, paper/paper.tex: the normalized
coefficient-token formula obeys the literal selected Dmax bound. -/
theorem reducedResidueFormula_degree (c : Call) {p : Cells.Parameters}
    (hs : Cells.ParameterRules (Builder.callInput c) p) (w : List Bool)
    (walk : Cycle.Walk hs.seedParameters.N 4) (sigma : Cycle.SignPattern 4)
    (prime : ℕ) (hprime : prime ≤ p.P)
    (digits : Fin 2 → Fin (p.J - 1 + 1) → ℤ) (residues : Fin 2 → ℤ) (weight : ℤ) :
    (reduceConstants (prime ^ p.e)
      (callResidueWalkFormula c hs w walk sigma prime digits residues weight)).degree ≤ p.Dmax := by
  rw [reduceConstants_degree]
  exact (callResidueWalkFormula_degree c hs w walk sigma prime digits residues weight).trans
    (residueDegreeBound_le_Dmax hs prime hprime)

end NearQuarticWires.StageLift
