import Proof.Quartic.StageLiftSourceCost.Machine

/-!
# Selected cost of the actual original source machine

`lem:print` and `prop:time`, paper/paper.tex: all original-walk construction is bounded by one
polynomial times the outer-column count. The raw-index acquisition
contributes a separate additive polynomial in its literal bit length.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageLiftSourceCost
open StageLift

private theorem product_le_squares (a b : ℕ) : a*b ≤ a^2+b^2 := by
  rcases le_total a b with h|h
  · have hh:=Nat.mul_le_mul_right b h
    nlinarith only [hh,Nat.zero_le (a^2)]
  · have hh:=Nat.mul_le_mul_left a h
    nlinarith only [hh,Nat.zero_le (b^2)]

theorem sourceMachineBudget_selected (B1 B2 : ℕ) : sourceMachineBudgetSelectedSpec B1 B2 := by
  let A:=scaleCoefficient B1 B2+1
  let d:=scaleExponent B1 B2
  let e:=d*32+2
  refine ⟨10^19*(2*A^32+1),e,?_⟩
  intro r
  let S:=sourceScale r
  let b:=r.child.call.n+1
  let J:=(Greedy.printIndexWord r).length+1
  let C:=2^(r.child.call.n-r.child.selected.1.k)
  have hA : 1 ≤ A := by dsimp [A];omega
  have hb : 1 ≤ b := by dsimp [b];omega
  have hJ : 1 ≤ J := by dsimp [J];omega
  have hC : 1 ≤ C := Nat.pow_pos (by decide)
  have hs : S ≤ A*b^d := (sourceScale_polynomial r).trans
    (Nat.mul_le_mul_right _ (Nat.le_succ _))
  have h32 : S^32 ≤ A^32*b^e := by
    have hh:=Nat.pow_le_pow_left hs 32
    rw [mul_pow,←pow_mul] at hh
    exact hh.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hb (by dsimp [e];omega)))
  have h10 : S^10 ≤ A^32*b^e := by
    have hh:=Nat.pow_le_pow_left hs 10
    rw [mul_pow,←pow_mul] at hh
    exact hh.trans (Nat.mul_le_mul (Nat.pow_le_pow_right hA (by decide))
      (Nat.pow_le_pow_right hb (by dsimp [e];omega)))
  have hJ2 : J^2 ≤ J^e := Nat.pow_le_pow_right hJ (by dsimp [e];omega)
  have hmix : S^5*J ≤ S^10+J^2 := by
    have hh:=product_le_squares (S^5) J
    simpa only [←pow_mul] using hh
  have hreserve:=original_tuple_reserve r
  have hfirst:=Nat.mul_le_mul_right (S^32) hreserve
  have hC32:=Nat.mul_le_mul_left C h32
  have hCP:=Nat.mul_le_mul_right (A^32*b^e) hC
  have hsum : r.child.cellCall.seed.N^8*
      (Builder.allGates r.child.call).length^r.child.selected.1.Xmax*S^32+S^5*J ≤
      (2*A^32+1)*(C*b^e+J^e) := by
    change _ ≤ C*S^32 at hfirst
    nlinarith only [hfirst,hC32,hmix,h10,hJ2,hCP,
      Nat.zero_le (A^32*J^e),Nat.zero_le (C*b^e)]
  have hmachine:=source_machine_scale r
  change sourceMachineBudget r ≤ 10^19*(2*A^32+1)*(C*b^e+J^e)
  exact hmachine.trans ((Nat.mul_le_mul_left (10^19) hsum).trans_eq (by ring))

end NearQuarticWires.StageLiftSourceCost
