import Proof.Quartic.StagePrint.FullTable
import Proof.Supplier.EquationRowRequest

set_option autoImplicit false

namespace NearQuarticWires.StagePrint
open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey
open NearCubicGates.Close.WordPrograms

/-- `lem:print`, paper/paper.tex: the low-first signed integer field is exactly the native sign-and-magnitude field, with no numerical decoding pass. -/
theorem binary_encS_signMagnitude (p : ℕ) (z : ℤ) :
    binary (p+1) (SInt.encS z)=MatrixScoreBatch.signMagnitude p z := by
  have hd : SInt.encS z/2=z.natAbs:=by
    unfold SInt.encS
    split_ifs <;> omega
  have hm : (SInt.encS z%2==1)=decide (z<0):=by
    by_cases hz : z<0
    · simp only [SInt.encS,if_pos hz]
      have he : (2*z.natAbs+1)%2=1:=by omega
      rw [he]
      simp [hz]
    · simp only [SInt.encS,if_neg hz,Nat.add_zero]
      have he : (2*z.natAbs)%2=0:=by omega
      rw [he]
      simp [hz]
  simp only [binary,hd,hm,MatrixScoreBatch.signMagnitude]

end NearQuarticWires.StagePrint
