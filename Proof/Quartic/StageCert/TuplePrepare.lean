import Proof.Quartic.StageCert.TuplePower

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicGates.Close.Cells

/-- `lem:maskpoly` and `lem:print`, paper/paper.tex: each actual tuple starts with the full original radix
power and the unit subset coefficient, including degree zero. -/
def prepareTupleOrder : St VV MM :=
  .seq (.op (.copy tuplePower tupleTotal)) (.op (.copy tupleOrdered v1))

/-- `lem:maskpoly` and `lem:print`, paper/paper.tex: actual tuple initialization retains its original address,
degree, occurrence bank, witness records, and all external streams. -/
theorem prepareTupleOrder_run (C : Ctx) (a : DS VV MM) (hc : Cst a) (total : ℕ)
    (ht : a.env tupleTotal=total) :
    Hs C prepareTupleOrder a 3 (fun z=>z.env tuplePower=total ∧ z.env tupleOrdered=1 ∧
      z.sh=a.sh ∧ Cst z ∧ Fr a z [tuplePower,tupleOrdered]) := by
  unfold prepareTupleOrder
  refine Hs.seq (t1 := 1) (t2 := 1)
    (hs_copy C tuplePower tupleTotal a (by decide)) ?_
  rintro b rfl
  refine (hs_copy C tupleOrdered v1 _ (by decide)).mono le_rfl ?_
  rintro z rfl
  exact ⟨by vsimp [ht],by vsimp [hc.one],rfl,
    ⟨by vsimp [hc.z],by vsimp [hc.one],by vsimp [hc.two]⟩,
    (Fr.set _ _ (by simp)).trans (Fr.set _ _ (by simp))⟩

/-- `lem:maskpoly` and `lem:print`, paper/paper.tex: the actual complete radix-order test has exactly the
strictly-increasing finite-function coefficient of the tuple formula. -/
theorem tupleAddress_orderBit (G degree : ℕ) (address : Fin (G^degree)) :
    prefixIncreasingBit (fun i=>address.val/G^(degree-1-i)%G) degree=
      decide (StrictMono (tupleAddressEquiv G degree address)) := by
  apply Bool.eq_iff_iff.mpr
  rw [prefixIncreasingBit_true,decide_eq_true_eq,prefixIncreasing_fin]
  have hf : (fun i : Fin degree=>address.val/G^(degree-1-i.val)%G)=
      (fun i=>(tupleAddressEquiv G degree address i).val) := by
    funext i
    exact (tupleAddress_digit G degree address i).symm
  rw [hf]
  rfl

end NearQuarticWires.StageCert.Tokens
