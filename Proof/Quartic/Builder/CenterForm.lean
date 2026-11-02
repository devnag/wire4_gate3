import Proof.Quartic.Builder.CellCall

/-!
# The centers of the cell call in affine form

Paper: `imp:partition`, paper/paper.tex.

The center of column `z` of the cell call is affine over `GF(2)` in the bits of `z`: bit `x` is the exclusive-or of
`C4Geo.ctrBit` (the shared linear map of the star: the repeated Hamming-code generator on the blocks and identity
columns on the unblocked coordinates, applied to the row `z mod 2^{d_L}` and the column `⌊z / 2^{d_L}⌋`) and the
offset `C4Geo.offset` of the partition (a point of its coset in every block). Bit `j` of the row is read at
coordinate `C4Geo.rowPos j`, bit `j` of the column at `C4Geo.colPos j`.
-/

set_option autoImplicit false

namespace NearQuarticWires.Builder

open NearCubicWires.WireExponent3_5.PrimT

variable (c : NearCubicGates.Close.Interfaces.Call) {p : Cells.Parameters}
  (hs : Cells.ParameterRules (callInput c) p)

/-- **The center of column `z`, bit by bit**: the shared linear map of the star at the low and high bits of `z`,
plus the offset of the partition named by the witness. -/
theorem center_bit (w : List Bool) (z : Fin (2 ^ (c.n - p.k))) (x : Fin c.n) :
    center c hs w z x =
      xor (C4Geo.ctrBit (star c hs) ((z : ℕ) % 2 ^ C4Geo.dRow (star c hs)) ((z : ℕ) / 2 ^ C4Geo.dRow (star c hs)) x)
        (C4Geo.offset (star c hs) (translation c hs w) x) :=
  C4Geo.centerAt_bit (star c hs) (translation c hs w) _ _ x

/-- The row bits of the center: bit `j < d_L` of `z` is the linear part of the center at `C4Geo.rowPos j`. -/
theorem ctrBit_row (z : Fin (2 ^ (c.n - p.k))) (j : ℕ) (hj : j < C4Geo.dRow (star c hs)) :
    C4Geo.ctrBit (star c hs) ((z : ℕ) % 2 ^ C4Geo.dRow (star c hs)) ((z : ℕ) / 2 ^ C4Geo.dRow (star c hs))
      (C4Geo.rowPos (star c hs) j) = (z : ℕ).testBit j := by
  rw [C4Geo.ctrBit_rowPos (star c hs) _ _ j hj, Nat.testBit_mod_two_pow, decide_eq_true hj, Bool.true_and]

end NearQuarticWires.Builder
