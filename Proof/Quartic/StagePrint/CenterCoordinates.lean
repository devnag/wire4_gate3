import Proof.Quartic.Builder.CellCall

set_option autoImplicit false

namespace NearQuarticWires.StagePrint
open NearCubicWires NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5
open NearQuarticWires
open NearCubicGates.Close.Interfaces

/-- `imp:partition` and `lem:print`, paper/paper.tex: the low row bits and high column bits encode one actual center index. -/
def centerIndex (c : Call) {p : Cells.Parameters}
    (hs : Cells.ParameterRules (Builder.callInput c) p)
    (row : Fin (2 ^ PrimT.C4Geo.dRow (Builder.star c hs)))
    (col : Fin (2 ^ PrimT.C4Geo.dR (Builder.star c hs))) : Fin (2 ^ (c.n-p.k)) :=
  ⟨row.val + 2 ^ PrimT.C4Geo.dRow (Builder.star c hs) * col.val, by
    rw [Builder.centerCount_eq c hs, pow_add]
    have hr := row.isLt
    have hc := col.isLt
    nlinarith⟩

/-- `imp:pullback` and `lem:print`, paper/paper.tex: the actual Builder column is exactly the shared-generator table point, with no arbitrary indexing permutation. -/
theorem centerIndex_point (c : Call) {p : Cells.Parameters}
    (hs : Cells.ParameterRules (Builder.callInput c) p) (w : List Bool)
    (row : Fin (2 ^ PrimT.C4Geo.dRow (Builder.star c hs)))
    (col : Fin (2 ^ PrimT.C4Geo.dR (Builder.star c hs))) :
    Builder.center c hs w (centerIndex c hs row col) =
      PrimT.C4Geo.centerAt (Builder.star c hs) (Builder.translation c hs w) row.val col.val := by
  rw [Builder.center_eq_centerOf]
  unfold Builder.centerOf centerIndex
  have hp : 0 < 2 ^ PrimT.C4Geo.dRow (Builder.star c hs) := Nat.two_pow_pos _
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt row.isLt,
    Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt row.isLt, zero_add]

/-- `imp:partition` and `lem:print`, paper/paper.tex: every serialized column has its unique low-row/high-column decomposition. -/
theorem centerIndex_surjective (c : Call) {p : Cells.Parameters}
    (hs : Cells.ParameterRules (Builder.callInput c) p) :
    Function.Surjective (fun rc :
      Fin (2 ^ PrimT.C4Geo.dRow (Builder.star c hs)) ×
        Fin (2 ^ PrimT.C4Geo.dR (Builder.star c hs)) => centerIndex c hs rc.1 rc.2) := by
  intro z
  let b := 2 ^ PrimT.C4Geo.dRow (Builder.star c hs)
  have hp : 0 < b := Nat.two_pow_pos _
  have hc : z.val / b < 2 ^ PrimT.C4Geo.dR (Builder.star c hs) := by
    rw [Nat.div_lt_iff_lt_mul hp]
    calc z.val < 2 ^ (c.n-p.k) := z.isLt
      _ = 2 ^ PrimT.C4Geo.dR (Builder.star c hs) * b := by
        rw [Builder.centerCount_eq c hs, pow_add]
        exact Nat.mul_comm _ _
  refine ⟨(⟨z.val%b, Nat.mod_lt _ hp⟩, ⟨z.val/b, hc⟩), ?_⟩
  apply Fin.ext
  exact Nat.mod_add_div _ _

end NearQuarticWires.StagePrint
