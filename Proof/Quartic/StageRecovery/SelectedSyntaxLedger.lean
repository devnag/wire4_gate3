import Proof.Quartic.StageRecovery.ResidueFactor
import Proof.Quartic.Cells.ParametersFormulaReserve

set_option autoImplicit false

namespace NearQuarticWires.StageRecovery

open NearCubicWires NearCubicGates.Close.Cells
open NearCubicGates.Close.Interfaces

/-- `prop:time`, paper/paper.tex:
the literal tuple-residue compiler multiplier retains the factor two
from the actual tuple-mask syntax, all codec headers and the degree field. -/
def tupleResidueCompilerFactor (c : Call) (p : Cells.Parameters) (prime D : ℕ) : ℕ :=
  6 * ((StageLift.formulaByteFactor (17 * (Builder.allGates c).length) (prime ^ p.e) + 1) *
    StageLift.residueSyntaxPolynomial (Builder.allGates c).length p.Xmax (p.J - 1) prime p.e) +
    3 * (17 * (Builder.allGates c).length) + D + natBitLength (prime ^ p.e) + 20

/-- `prop:time`, paper/paper.tex:
the actual original atom pool is quartically bounded and is charged
inside the selected unchanged occurrence factor. -/
theorem selected_pool_bounds (c : Call) {p : Cells.Parameters}
    (hs : Cells.ParameterRules (Builder.callInput c) p) :
    17 * (Builder.allGates c).length ≤ 34 * c.n ^ 4 ∧
      17 * (Builder.allGates c).length + 1 ≤ p.Uocc := by
  have hv := hs.input_valid
  have hG : (Builder.allGates c).length ≤ 2 * c.n ^ 4 := by
    have heq : (Builder.allGates c).length = (Builder.callInput c).G1 + (Builder.callInput c).G2 := by
      simp [Builder.allGates, Builder.callInput]
    rw [heq]
    exact hv.2.2.1.trans hv.2.2.2.1
  have hV : 17 * (Builder.allGates c).length ≤ p.NatAtoms := by
    rw [hs.NatAtoms_eq, hs.m_eq]
    change 17 * (Builder.allGates c).length ≤ (4 * 4 + 1) * (2 * c.n ^ 4)
    nlinarith
  have hc : 0 < p.childCap := by
    have hn := Cells.ParameterRules.n_pos hs
    rw [hs.childCap_eq]
    unfold Cells.childCap
    positivity
  constructor
  · nlinarith
  · rw [hs.Uocc_eq]
    have hh : p.NatAtoms ≤ p.NatAtoms * p.childCap := Nat.le_mul_of_pos_right _ hc
    omega


/-- `prop:time`, paper/paper.tex:
the selected common scalar envelope plus one remains a fixed polynomial
of the original arity before taking the compiler's fixed sixth power. -/
theorem preparationEnvelope_succ_le (B1 n : ℕ) :
    Cells.ParameterArithmetic.preparationEnvelope B1 n + 1 ≤
      (Cells.ParameterArithmetic.preparationCoefficient B1 + 1) * (n + 1) ^ (B1 + 12) := by
  have hp : 1 ≤ (n + 1) ^ (B1 + 12) := Nat.one_le_pow _ _ (by omega)
  unfold Cells.ParameterArithmetic.preparationEnvelope
  nlinarith


/-- `prop:time`, paper/paper.tex:
the exact sixth power of the actual tuple-residue syntax multiplier is
bounded by one displayed fixed arity polynomial at every admitted precision. -/
theorem selected_tupleFactor_pow_six (c : Call) {p : Cells.Parameters}
    (hs : Cells.ParameterRules (Builder.callInput c) p) (B1 : ℕ)
    (hb : 1 ≤ (Builder.callInput c).beta * ((Builder.callInput c).n : ℚ) ^ B1)
    (prime : ℕ) (hprime : prime ∈ p.primes) (D : ℕ) (hD : D ≤ p.Dmax) :
    (tupleResidueCompilerFactor c p prime D) ^ 6 ≤
      10 ^ 36 * (Cells.ParameterArithmetic.preparationCoefficient B1 + 1) ^ 30 *
        (c.n + 1) ^ (30 * (B1 + 12)) := by
  have hf := selected_residueCompilerFactor c hs B1 hb prime hprime D hD
  change tupleResidueCompilerFactor c p prime D ≤
    10 ^ 6 * (Cells.ParameterArithmetic.preparationEnvelope B1 c.n + 1) ^ 5 at hf
  have he := preparationEnvelope_succ_le B1 c.n
  calc (tupleResidueCompilerFactor c p prime D) ^ 6 ≤
      (10 ^ 6 * (Cells.ParameterArithmetic.preparationEnvelope B1 c.n + 1) ^ 5) ^ 6 :=
        Nat.pow_le_pow_left hf _
    _ = 10 ^ 36 * (Cells.ParameterArithmetic.preparationEnvelope B1 c.n + 1) ^ 30 := by
      rw [mul_pow, ← pow_mul, ← pow_mul]
    _ ≤ 10 ^ 36 * ((Cells.ParameterArithmetic.preparationCoefficient B1 + 1) *
      (c.n + 1) ^ (B1 + 12)) ^ 30 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left he _)
    _ = _ := by
      simp only [mul_pow, ← pow_mul, show (B1 + 12) * 30 = 30 * (B1 + 12) by omega, Nat.mul_assoc]


/-- `prop:time`, paper/paper.tex:
the compiler's entire fixed multiplier depends only on admitted
precision, not on the original circuit, targets, witness or walk. -/
noncomputable def selectedCompilerConstant (B1 : ℕ) : ℕ :=
  4 * 27 * 10 ^ 22 * (TSK packetCallee + 10) * 10 ^ 36 *
    (Cells.ParameterArithmetic.preparationCoefficient B1 + 1) ^ 30 * 35 ^ 6


/-- `prop:time`, paper/paper.tex:
the complete syntax/byte/compilation multiplier has a fixed polynomial
degree at every admitted precision. -/
def selectedCompilerExponent (B1 : ℕ) : ℕ := 30 * (B1 + 12) + 24

/-- `prop:time`, paper/paper.tex: fixed scalar
multipliers commute with the two explicit polynomial factors. -/
theorem compilerEnvelope_reassociate (A B C U N Z e f : ℕ) :
    A * (B * C * N ^ e) * ((U * N ^ f) * Z) =
      (A * B * C * U) * Z * N ^ (e + f) := by
  rw [Nat.pow_add]
  ac_rfl

/-- `prop:time`, paper/paper.tex:
the literal all-walk compiler envelope fits the unchanged native column
budget, using the original atom-pool and actual selected degree bounds. -/
theorem selected_tuple_compiler_envelope (c : Call) {p : Cells.Parameters}
    (hs : Cells.ParameterRules (Builder.callInput c) p) (B1 : ℕ)
    (hb : 1 ≤ (Builder.callInput c).beta * ((Builder.callInput c).n : ℚ) ^ B1)
    (prime : ℕ) (hprime : prime ∈ p.primes) (D : ℕ) (hD : D ≤ p.Dmax)
    (hX : 16 * p.Xmax ≤ D) :
    2 ^ (4 * p.k) * (4 * 27 * 10 ^ 22 * (TSK packetCallee + 10) *
      (tupleResidueCompilerFactor c p prime D) ^ 6 *
        (17 * (Builder.allGates c).length + 1) ^ (2 * D + 6 * p.Xmax + 6)) ≤
      selectedCompilerConstant B1 * 2 ^ (c.n - p.k) * (c.n + 1) ^ selectedCompilerExponent B1 := by
  have hpool := selected_pool_bounds c hs
  have hr := Cells.ParameterRules.formula_all_walks_reserve hs
    (17 * (Builder.allGates c).length) D p.Xmax hpool.1 hpool.2 hD hX
  have hf := selected_tupleFactor_pow_six c hs B1 hb prime hprime D hD
  calc _ = 4 * 27 * 10 ^ 22 * (TSK packetCallee + 10) *
      (tupleResidueCompilerFactor c p prime D) ^ 6 *
        (2 ^ (4 * p.k) * (17 * (Builder.allGates c).length + 1) ^ (2 * D + 6 * p.Xmax + 6)) := by ac_rfl
    _ ≤ 4 * 27 * 10 ^ 22 * (TSK packetCallee + 10) *
      (10 ^ 36 * (Cells.ParameterArithmetic.preparationCoefficient B1 + 1) ^ 30 *
        (c.n + 1) ^ (30 * (B1 + 12))) *
          ((35 ^ 6 * (c.n + 1) ^ 24) * 2 ^ (c.n - p.k)) := by
            exact Nat.mul_le_mul (Nat.mul_le_mul_left _ hf) hr
    _ = _ := by
      exact compilerEnvelope_reassociate
        (4 * 27 * 10 ^ 22 * (TSK packetCallee + 10)) (10 ^ 36)
        ((Cells.ParameterArithmetic.preparationCoefficient B1 + 1) ^ 30)
        (35 ^ 6) (c.n + 1) (2 ^ (c.n - p.k)) (30 * (B1 + 12)) 24

end NearQuarticWires.StageRecovery
