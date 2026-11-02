import Proof.Quartic.StageCert.MomentHeader
import Proof.Quartic.StageCert.SourceCallGuards
import Proof.Quartic.Cells.ParametersCertSyntaxWeight
import Proof.Quartic.StageLift.FormulaBytes

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells

/-- `lem:print` and `prop:time`, paper/paper.tex: the literal raw atom and complete signed-coefficient
binary lengths determine the concrete source emitter's word bounds. -/
def MomentRequest.atomBits {B1 B2 : ℕ} (r : MomentRequest B1 B2) : ℕ :=
  natBitLength (17*(Builder.allGates r.call).length)

def MomentRequest.coefficientBits {B1 B2 : ℕ} (r : MomentRequest B1 B2) : ℕ :=
  natBitLength (1+r.call.n+r.selected.1.M1+r.selected.1.A)

/-- `lem:print`, paper/paper.tex: every actual
original atom index fits the physical seventeen-role pool's binary bound. -/
theorem MomentRequest.atom_bits_bound {B1 B2 : ℕ} (r : MomentRequest B1 B2)
    (g : ℕ) (hg : g<(Builder.allGates r.call).length) (edge : Fin 8) (corner : Fin 4) :
    natBitLength (cornerRoleCode edge corner*(Builder.allGates r.call).length+g)≤r.atomBits := by
  have hi := (Cells.atomIndex (Cells.cornerRole (by decide : 0<4) edge corner)
    (⟨g,hg⟩ : Fin (Builder.allGates r.call).length)).isLt
  rw [atomIndex_eq_code] at hi
  exact StageLift.codec_nbl_mono hi.le

/-- `eq:testE` and `lem:print`, paper/paper.tex: every actual retained digit coefficient has the same
unconditional whole-source binary bound, on every proposed witness. -/
theorem MomentRequest.digit_coefficient_bits {B1 B2 : ℕ} (r : MomentRequest B1 B2)
    (j : Fin 2) (row : Fin (r.selected.1.J-1+1))
    (g : Fin (Builder.allGates r.call).length) :
    natBitLength (sourceDigitGlobalWeights r.call r.selected.1 r.retainedWitness j row.val g).natAbs≤
      r.coefficientBits := by
  apply StageLift.codec_nbl_mono
  exact (source_digit_global_natAbs_le r.call r.rules r.retainedWitness j row g).trans (by omega)

/-- `eq:testPhi` and `lem:print`, paper/paper.tex: the complete final offset remains inside the original
coefficient bound without a certification or good-column premise. -/
theorem MomentRequest.final_coefficient_bits {B1 B2 : ℕ} (r : MomentRequest B1 B2)
    (j : Fin 2) (g : Fin (Builder.allGates r.call).length) :
    natBitLength (sourceFinalGlobalWeights r.call r.selected.1 r.retainedWitness j g).natAbs≤
      r.coefficientBits := by
  apply StageLift.codec_nbl_mono
  exact (source_final_global_natAbs_le r.call r.selected.1 r.retainedWitness j g).trans (by omega)

/-- `lem:maskpoly` and `lem:print`, paper/paper.tex: every emitted signed Newton coefficient has at most
Xmax+1 binary bits, including its literal zero cases. -/
theorem MomentRequest.newton_bits_bound {B1 B2 : ℕ} (r : MomentRequest B1 B2)
    (degree : ℕ) (hd : degree≤r.selected.1.Xmax) :
    natBitLength (Mask.newtonCoeff r.selected.1.tau degree).natAbs≤r.selected.1.Xmax+1 := by
  have h := Mask.newtonCoeff_abs_le r.selected.1.tau degree
  rw [←Int.natCast_natAbs] at h
  have hn : (Mask.newtonCoeff r.selected.1.tau degree).natAbs≤2^degree := by exact_mod_cast h
  have hbits := StageLift.codec_nbl_mono hn
  have hp : natBitLength (2^degree)=degree+1 := by
    unfold natBitLength
    rw [Nat.log_pow (by decide : 1<(2:ℕ))]
  rw [hp] at hbits
  omega

end NearQuarticWires.StageCert.Tokens
