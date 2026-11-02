import Proof.Quartic.StageNativeWidth.StackBounds

set_option autoImplicit false

namespace NearQuarticWires.StageNativeWidth

open NearCubicGates.Close.TabMachine NearCubicGates.Close.WordPrograms

/-- `lem:print`, paper/paper.tex: the actual
sum-of-field-magnitudes radix and its Horner successor have linear
bit length in the source width, row dimension and monomial degree. -/
theorem radix_le_power (L s D : ℕ) (ls : List (List ℤ)) (hl : ls.length ≤ D)
    (h : ∀ row ∈ ls, row.length = s+1 ∧ ∀ z ∈ row, SInt.encS z < 2^L) :
    magL ls + 2 ≤ 2^(L+s+D+4) := by
  have hm := magL_le L s D ls hl h
  have hd : D ≤ 2^D := (Nat.lt_two_pow_self (n := D)).le
  have hs : s+1 ≤ 2^s := Nat.lt_two_pow_self
  have hmag : magL ls ≤ 2^(L+s+D) := by
    calc
      _ ≤ D * ((s+1) * 2^L) := hm
      _ ≤ 2^D * (2^s * 2^L) :=
        Nat.mul_le_mul hd (Nat.mul_le_mul_right _ hs)
      _ = _ := by rw [← pow_add, ← pow_add]; congr 1; omega
  have hp := Nat.two_pow_pos (L+s+D)
  rw [pow_add]
  norm_num only [Nat.reducePow]
  omega

end NearQuarticWires.StageNativeWidth
