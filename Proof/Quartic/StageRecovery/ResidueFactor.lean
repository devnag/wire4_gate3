import Proof.Quartic.StageRecovery.TermsSyntaxCost
import Proof.Quartic.StageLift.ResidueSize
import Proof.Quartic.Cells.ParametersScalarBounds

set_option autoImplicit false

namespace NearQuarticWires.StageRecovery

open NearCubicWires NearCubicGates.Close.Cells
open NearCubicGates.Close.Interfaces

/-- `prop:time`, paper/paper.tex:
the binary length of an actual prime power is polynomial in any common
value envelope for its base and exponent, with no raw index magnitude. -/
theorem primePower_bits_envelope (prime e E : ℕ) (hp : prime ≤ E) (he : e ≤ E) :
    natBitLength (prime ^ e) ≤ (E + 1) ^ 2 := by
  have hb : natBitLength prime ≤ E + 1 := (nbl_le_self prime).trans (by omega)
  have hp2 : prime ≤ 2 ^ (E + 1) :=
    (lt_natBitLength prime).le.trans (Nat.pow_le_pow_right (by decide) hb)
  have hq : prime ^ e < 2 ^ ((E + 1) ^ 2) := by
    calc prime ^ e ≤ (2 ^ (E + 1)) ^ e := Nat.pow_le_pow_left hp2 _
      _ ≤ (2 ^ (E + 1)) ^ E := Nat.pow_le_pow_right (by positivity) he
      _ = 2 ^ ((E + 1) * E) := (pow_mul (2 : ℕ) (E + 1) E).symm
      _ < 2 ^ ((E + 1) ^ 2) := Nat.pow_lt_pow_right (by decide) (by nlinarith)
  exact NearCubicGates.Close.WorkerArith.WorkerBounds.nbl_le_of_lt (by nlinarith) hq

/-- `prop:time`, paper/paper.tex:
the explicit mask/Fermat/amplifier syntax multiplier has degree three
in the common selected scalar-value envelope. -/
theorem residueSyntaxPolynomial_envelope (G X J prime e E : ℕ)
    (hG : G ≤ E) (hX : X ≤ E) (hJ : J ≤ E) (hp : prime ≤ E) (he : e ≤ E) :
    StageLift.residueSyntaxPolynomial G X J prime e ≤ 1000 * (E + 1) ^ 3 := by
  calc StageLift.residueSyntaxPolynomial G X J prime e ≤
      StageLift.residueSyntaxPolynomial E E E E E := by
        unfold StageLift.residueSyntaxPolynomial
        gcongr
    _ ≤ _ := by
      unfold StageLift.residueSyntaxPolynomial
      nlinarith [Nat.zero_le (E ^ 3), Nat.zero_le (E ^ 2)]

/-- `prop:time`, paper/paper.tex:
normalized constant and variable codec bytes have a quadratic common
scalar factor before the original mask-source exponent. -/
theorem formulaByteFactor_envelope (V prime e E : ℕ)
    (hV : V ≤ E) (hp : prime ≤ E) (he : e ≤ E) :
    StageLift.formulaByteFactor V (prime ^ e) + 1 ≤ 20 * (E + 1) ^ 2 := by
  have hv := (nbl_le_self V).trans (show V + 1 ≤ E + 1 by omega)
  have hq := primePower_bits_envelope prime e E hp he
  unfold StageLift.formulaByteFactor
  nlinarith

/-- `prop:time`, paper/paper.tex:
the complete literal tuple-mask source multiplier includes its factor
two syntax expansion and remains a fifth-degree scalar polynomial. -/
theorem residueCompilerFactor_envelope (G X J prime e D E : ℕ)
    (hV : 17 * G ≤ E) (hX : X ≤ E) (hJ : J ≤ E)
    (hp : prime ≤ E) (he : e ≤ E) (hD : D ≤ E) :
    6 * ((StageLift.formulaByteFactor (17 * G) (prime ^ e) + 1) *
      StageLift.residueSyntaxPolynomial G X J prime e) +
      3 * (17 * G) + D + natBitLength (prime ^ e) + 20 ≤ 10 ^ 6 * (E + 1) ^ 5 := by
  have hG : G ≤ E := by omega
  have hb := formulaByteFactor_envelope (17 * G) prime e E hV hp he
  have hs := residueSyntaxPolynomial_envelope G X J prime e E hG hX hJ hp he
  have hq := primePower_bits_envelope prime e E hp he
  have hprod := Nat.mul_le_mul hb hs
  have hE5 : E + 1 ≤ (E + 1) ^ 5 := Nat.le_self_pow (by norm_num) _
  have hE25 : (E + 1) ^ 2 ≤ (E + 1) ^ 5 := Nat.pow_le_pow_right (by omega) (by omega)
  nlinarith

/-- `prop:time`, paper/paper.tex:
the actual original shared occurrence pool obeys the selected scalar
envelope, independently of coefficient or target magnitudes. -/
theorem selected_occurrence_envelope (c : Call) {p : Cells.Parameters}
    (hs : Cells.ParameterRules (Builder.callInput c) p) (B1 : ℕ)
    (hb : 1 ≤ (Builder.callInput c).beta * ((Builder.callInput c).n : ℚ) ^ B1) :
    17 * (Builder.allGates c).length ≤ Cells.ParameterArithmetic.preparationEnvelope B1 c.n := by
  have hv := hs.input_valid
  have hG : (Builder.allGates c).length ≤ 2 * c.n ^ 4 := by
    have heq : (Builder.allGates c).length = (Builder.callInput c).G1 + (Builder.callInput c).G2 := by
      simp [Builder.allGates, Builder.callInput]
    rw [heq]
    exact hv.2.2.1.trans hv.2.2.2.1
  have hNat : 17 * (Builder.allGates c).length ≤ p.NatAtoms := by
    rw [hs.NatAtoms_eq, hs.m_eq]
    change 17 * (Builder.allGates c).length ≤ (4 * 4 + 1) * (2 * c.n ^ 4)
    nlinarith
  exact hNat.trans (hs.scalar_preparation_bounds B1 hb).NatAtoms

/-- `prop:time`, paper/paper.tex:
the exact selected tuple-mask residue multiplier is bounded by one
fixed polynomial of the original arity, using actual selected fields. -/
theorem selected_residueCompilerFactor (c : Call) {p : Cells.Parameters}
    (hs : Cells.ParameterRules (Builder.callInput c) p) (B1 : ℕ)
    (hb : 1 ≤ (Builder.callInput c).beta * ((Builder.callInput c).n : ℚ) ^ B1)
    (prime : ℕ) (hprime : prime ∈ p.primes) (D : ℕ) (hD : D ≤ p.Dmax) :
    6 * ((StageLift.formulaByteFactor (17 * (Builder.allGates c).length) (prime ^ p.e) + 1) *
      StageLift.residueSyntaxPolynomial (Builder.allGates c).length p.Xmax (p.J - 1) prime p.e) +
      3 * (17 * (Builder.allGates c).length) + D + natBitLength (prime ^ p.e) + 20 ≤
        10 ^ 6 * (Cells.ParameterArithmetic.preparationEnvelope B1 c.n + 1) ^ 5 := by
  have hbds := hs.scalar_preparation_bounds B1 hb
  have hp : prime ≤ p.P := by
    rw [hs.primes_eq, NearCubicGates.Close.Counter.mem_dyadicPrimes] at hprime
    exact hprime.1
  exact residueCompilerFactor_envelope _ _ _ _ _ _ _ (selected_occurrence_envelope c hs B1 hb)
    hbds.Xmax ((Nat.sub_le _ _).trans hbds.J) (hp.trans hbds.P) hbds.e (hD.trans hbds.Dmax)

end NearQuarticWires.StageRecovery
