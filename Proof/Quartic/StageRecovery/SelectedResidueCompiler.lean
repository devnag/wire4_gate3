import Proof.Quartic.StageRecovery.ResidueCompiler
import Proof.Quartic.StageRecovery.SelectedSyntaxLedger

set_option autoImplicit false

namespace NearQuarticWires.StageRecovery

open NearCubicWires NearCubicGates.Close.Tabulator NearCubicGates.Close.Interfaces

/-- `lem:print` and `prop:time`, paper/paper.tex: the actual normalized tuple-Formula cold compiler,
including its real serialized syntax and all length/copy work, fits the
unchanged column-times-polynomial budget for every walk in the census. -/
theorem selected_residueCompileRequest_budget (c : Call) {p : Cells.Parameters}
    (hs : Cells.ParameterRules (Builder.callInput c) p) (B1 : ℕ)
    (hb : 1 ≤ (Builder.callInput c).beta * ((Builder.callInput c).n : ℚ) ^ B1)
    (w : List Bool) (walk : Cycle.Walk hs.seedParameters.N 4) (sigma : Cycle.SignPattern 4)
    (prime : ℕ) (hprime : prime ∈ p.primes)
    (digits : Fin 2 → Fin (p.J - 1 + 1) → ℤ) (residues : Fin 2 → ℤ) (weight : ℤ) :
    2 ^ (4 * p.k) *
        (residueCompileRequest c hs w walk sigma prime hprime digits residues weight).modularTermsBudget ≤
      selectedCompilerConstant B1 * 2 ^ (c.n - p.k) * (c.n + 1) ^ selectedCompilerExponent B1 := by
  have hb0 := residueCompileRequest_budget c hs w walk sigma prime hprime digits residues weight
  have hp : prime ≤ p.P := by
    rw [hs.primes_eq, NearCubicGates.Close.Counter.mem_dyadicPrimes] at hprime
    exact hprime.1
  have hd := StageLift.residueDegreeBound_le_Dmax hs prime hp
  have hx : 16 * p.Xmax ≤ StageLift.residueDegreeBound p prime := by
    unfold StageLift.residueDegreeBound
    omega
  have hs0 := selected_tuple_compiler_envelope c hs B1 hb prime hprime
    (StageLift.residueDegreeBound p prime) hd hx
  exact (Nat.mul_le_mul_left _ hb0).trans hs0

end NearQuarticWires.StageRecovery
