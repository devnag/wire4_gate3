import Proof.Quartic.StagePrep.NativePackaging
import Proof.Quartic.Cells.ParametersPreparationBits

/-!
# One original-call word width for every preparation exit

Paper: the normalized call codec in `thm:counter`,
paper/paper.tex, and `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open NearCubicGates.Close.Dispatch

/-- All concrete preparation instructions of `prop:time`,
paper/paper.tex, use one fixed fourth-power
word width in the original serialized call length. -/
theorem originalPreparationWidth (B1 B2 : ℕ) :
    ∃ K : ℕ, 1≤K ∧ ∀ L : ℕ,
      2*L+8≤wdOf K L ∧ 2*L+4<2^(wdOf K L) ∧
      (B1+B2+5)*(L+1)≤wdOf K L ∧
      100*Cells.ParameterArithmetic.preparationBitBase B1 L≤wdOf K L := by
  obtain ⟨K0,hK0,hwidth⟩ := Cells.ParameterArithmetic.preparationBitBase_width B1
  let K := K0+B1+B2+20
  refine ⟨K,by omega,?_⟩
  intro L
  have h100 : 100*Cells.ParameterArithmetic.preparationBitBase B1 L≤wdOf K L :=
    (hwidth L).trans (Nat.pow_le_pow_left (by omega) 4)
  have hH := Cells.ParameterArithmetic.preparationBitBase_bounds B1 L
  have hfront : 2*L+8≤wdOf K L := by omega
  have hbase : 1≤L+K := by omega
  have hprod : (B1+B2+5)*(L+1)≤(L+K)^2 := by
    calc
      _ ≤ (L+K)*(L+K) := Nat.mul_le_mul (by omega) (by omega)
      _ = _ := by ring
  have hadm : (B1+B2+5)*(L+1)≤wdOf K L :=
    hprod.trans (Nat.pow_le_pow_right hbase (by norm_num))
  exact ⟨hfront,(by omega : 2*L+4≤wdOf K L).trans_lt Nat.lt_two_pow_self,hadm,h100⟩

end NearQuarticWires.StagePrep
