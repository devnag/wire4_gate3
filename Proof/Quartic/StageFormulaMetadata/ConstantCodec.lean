import Proof.Quartic.StageFormulaMetadata.ConstantNormalize
import Proof.Quartic.StageFormulaMetadata.TokenStats

set_option autoImplicit false

namespace NearQuarticWires.StageFormulaMetadata

open NearCubicWires
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Interfaces

/-- `lem:print`, paper/paper.tex: every signed
constant has the unchanged canonical sign and magnitude fields. -/
theorem integerWord_fields (value : ℤ) :
    intWord value=natWord (decide (value<0)).toNat++natWord value.natAbs := by
  by_cases hnegative : value<0 <;> simp [intWord,hnegative]

/-- `lem:print` and `lem:residue`, paper/paper.tex: physical constant normalization produces
exactly the canonical original signed-integer codec in both modes. -/
theorem normalizedInteger_fields (modulus : ℕ) (value : ℤ)
    (hmode : modulus=0 ∨ 2 ≤ modulus) :
    intWord (value%(modulus:ℤ))=
      natWord (normalizedSign modulus (decide (value<0)))++
        natWord (normalizedMagnitude modulus value.natAbs (decide (value<0))) := by
  rcases hmode with hzero | hpositive
  · subst modulus
    simpa [normalizedSign,normalizedMagnitude] using integerWord_fields value
  · have hnz : modulus≠0 := by omega
    have hq : 0 < modulus := by omega
    have hnonneg : 0≤value%(modulus:ℤ) := Int.emod_nonneg _ (by exact_mod_cast hnz)
    have hres:=StageRecovery.signedNaturalResidue_eq modulus hq value
    have hm : StageRecovery.signedNaturalResidue modulus value.natAbs (decide (value<0))=
        (value%(modulus:ℤ)).natAbs := by
      simpa only [Int.natAbs_natCast] using congrArg Int.natAbs hres
    rw [integerWord_fields]
    simp only [normalizedSign,normalizedMagnitude,if_neg hnz,hm,
      show ¬value%(modulus:ℤ)<0 from not_lt_of_ge hnonneg,decide_false,Bool.toNat_false]

end NearQuarticWires.StageFormulaMetadata
