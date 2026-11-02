import Proof.Quartic.StageNativeWidth.PackingBase

set_option autoImplicit false

namespace NearQuarticWires.StageNativeWidth

open NearCubicGates.Close.TabMachine NearCubicGates.Close.WordPrograms
open StagePrint.NativeWidth

/-- `lem:print`, paper/paper.tex: the literal
proposed packing width covers the actual radix power, concrete stackL
and coefficient in cutL, including empty tuples and coefficient zero. -/
theorem packed_fits (L s D cbits : ℕ) : PackedFit L s D cbits := by
  intro ls c hl hrows hc
  let H := L+s+D+4
  let W := packedBits L s D cbits
  have hW : (D+2)*H+4 ≤ W :=
    Nat.add_le_add_right (Nat.le_max_right cbits ((D+2)*H)) 4
  have hcb : cbits ≤ W := by
    have h := Nat.le_max_left cbits ((D+2)*H)
    dsimp [W, packedBits]
    omega
  have hL : L ≤ H := by dsimp [H]; omega
  have hrad : magL ls + 2 ≤ 2^H := radix_le_power L s D ls hl hrows
  have hexp : H * (ls.length+1) < W := by
    have hm := Nat.mul_le_mul_left H (show ls.length+1 ≤ D+1 by omega)
    nlinarith only [hm, hW]
  have hstackexp : L + H * ls.length < W := by
    have hm := Nat.mul_le_mul_left H hl
    nlinarith only [hm, hW, hL]
  have hradix : (magL ls + 1)^(ls.length+1) < 2^W := by
    calc
      _ ≤ (2^H)^(ls.length+1) :=
        Nat.pow_le_pow_left (by omega : magL ls + 1 ≤ 2^H) _
      _ = 2^(H*(ls.length+1)) := (pow_mul _ _ _).symm
      _ < _ := Nat.pow_lt_pow_right (by decide) hexp
  have hstack : ∀ z ∈ stackL s ((magL ls+1 : ℕ) : ℤ) ls, z.natAbs < 2^W := by
    intro z hz
    have hh := stackL_abs s (magL ls+1) (2^L) ls
      (fun row hr z hz => (natAbs_le_encS z).trans ((hrows row hr).2 z hz).le) z hz
    calc
      _ ≤ 2^L * (magL ls+1+1)^ls.length := hh
      _ ≤ 2^L * (2^H)^ls.length :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hrad _)
      _ = 2^(L + H*ls.length) := by rw [← pow_mul, ← pow_add]
      _ < _ := Nat.pow_lt_pow_right (by decide) hstackexp
  have hcut : ∀ z ∈ cutL s c ls, z.natAbs < 2^W := by
    intro z hz
    rcases List.mem_append.mp hz with hz | hz
    · exact hstack z hz
    · have he := List.mem_singleton.mp hz
      subst z
      exact hc.trans_le (Nat.pow_le_pow_right (by decide) hcb)
  exact ⟨hradix, fun z hz => SInt.encS_lt (hcut z hz), hcut⟩

end NearQuarticWires.StageNativeWidth
