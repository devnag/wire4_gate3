import Proof.Quartic.StageNativeKidsPrice.Final

set_option autoImplicit false

namespace NearQuarticWires.StageNativeKidsPrice

open NearCubicGates.Close.Interfaces StageNativeKids

/-- `lem:print` and `prop:time`, paper/paper.tex: at the actual normalization bit bound,
the unchanged original child cap is cubic in original arity. -/
theorem originalChildCap_polynomial (n : ℕ) :
    Cells.childCap n (Call.B0 n) ≤ 16*(n+1)^3 := by
  have hs : Nat.clog 2 (n+1) ≤ n+1 := by
    apply Nat.clog_le_of_le_pow
    exact Nat.lt_two_pow_self.le
  have hn : Nat.clog 2 n ≤ n+1 := by
    apply Nat.clog_le_of_le_pow
    exact (Nat.le_succ n).trans Nat.lt_two_pow_self.le
  unfold Cells.childCap Call.B0
  have hm : n*(4*n*Nat.clog 2 (n+1)+Nat.clog 2 n+3) ≤
      n*(4*n*(n+1)+(n+1)+3) := by gcongr
  calc
    _ ≤ n*(4*n*(n+1)+(n+1)+3) := hm
    _ ≤ _ := by ring_nf; omega

/-- `prop:time`, paper/paper.tex: the
retained structural source resource itself has a fixed polynomial bound
in literal source length and original arity. -/
theorem originalSourceScale_polynomial (r : NativeKidsRequest) :
    r.originalSourceScale ≤ 20*(r.word.length+r.header.call.n+1)^3 := by
  let S := r.word.length+r.header.call.n+1
  have hp : 1 ≤ S := by dsimp [S]; omega
  have hn : r.header.call.n+1 ≤ S := by dsimp [S]; omega
  have hc := (originalChildCap_polynomial r.header.call.n).trans
    (Nat.mul_le_mul_left 16 (Nat.pow_le_pow_left hn 3))
  have hl : S ≤ S^3 := Nat.le_self_pow (by decide) S
  change r.originalSourceScale ≤ 20*S^3
  unfold NativeKidsRequest.originalSourceScale
  dsimp only [S] at hl hc ⊢
  omega

end NearQuarticWires.StageNativeKidsPrice
