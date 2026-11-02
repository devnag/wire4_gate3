import Proof.Quartic.StageCert.MomentSyntaxScale

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicGates.Close.Tabulator
open Cells.ParameterArithmetic

/-- `lem:print` and `prop:time`, paper/paper.tex: the actual emitted guarded-tuple source has the
original polynomial formal-mass height on every proposed witness,
without assuming that any column or moment test is valid. -/
theorem MomentRequest.formula_mass_bound {B1 B2 : ℕ} (r : MomentRequest B1 B2) :
    r.formula.mass≤2^certificateBitEnvelope (preparationEnvelope B1 r.call.n) := by
  cases ht : r.test with
  | population =>
    simp only [MomentRequest.formula,ht]
    exact Cells.call_population_moment_mass_bound r.call r.rules r.retainedWitness 0
      (StagePrint.callStructural r.call r.rules r.walk 0) B1 r.radius_lower
  | digit j code row =>
    simp only [MomentRequest.formula,ht]
    rw [source_digit_moment_mass r.call r.rules r.retainedWitness r.walk j row code.val]
    exact Cells.call_digit_moment_mass_bound r.call r.rules r.retainedWitness r.walk j
      (StageCertTests.patternOfCode code.val) row B1 r.radius_lower
  | finalError j code =>
    simp only [MomentRequest.formula,ht]
    rw [source_final_moment_mass r.call r.rules r.retainedWitness r.walk j code.val]
    exact Cells.call_final_moment_mass_bound r.call r.rules r.retainedWitness r.walk j
      (StageCertTests.patternOfCode code.val) B1 r.radius_lower

/-- `lem:print` and `prop:time`, paper/paper.tex: every coefficient actually produced by exact
expansion of the emitted signed source fits the fixed polynomial
native field, including all failed columns and arbitrary child bits. -/
theorem MomentRequest.expansion_coefficient_bits {B1 B2 : ℕ} (r : MomentRequest B1 B2)
    (term : Finset (Fin (17*(Builder.allGates r.call).length))×ℤ)
    (ht : term∈NearCubicGates.Close.Expand.expansionMachine.expand ⟨_,r.formula⟩) :
    term.2.natAbs<2^Cells.nativeCertificateBits B1 r.call.n ∧
      Nat.size term.2.natAbs≤Cells.nativeCertificateBits B1 r.call.n :=
  Cells.actual_coefficient_native_width r.formula B1 r.call.n r.formula_mass_bound term ht

end NearQuarticWires.StageCert.Tokens
