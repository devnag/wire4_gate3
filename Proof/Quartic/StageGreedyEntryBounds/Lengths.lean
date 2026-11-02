import Proof.Quartic.StageGreedyEntryBounds.Codec

set_option autoImplicit false

namespace NearQuarticWires.StageGreedyEntryBounds

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells
open NearCubicGates.Close.Expand.Layout

/-- `lem:print`, paper/paper.tex: adjoining an
actual small prefix adds only its finite byte length to the logarithmic
height of a possibly long actual stream. -/
theorem bitLength_add_prefix (a b : ℕ) :
    natBitLength (a+b)≤a+natBitLength b+2 := by
  have hb : 1≤2^natBitLength b := Nat.one_le_two_pow
  have ha:=Nat.mul_le_mul_left a hb
  have hp : a+b≤2^(a+natBitLength b) := by
    calc
      _≤(a+1)*2^natBitLength b := by nlinarith only [ha,(lt_natBitLength b).le]
      _≤2^a*2^natBitLength b := Nat.mul_le_mul_right _ Nat.lt_two_pow_self
      _=_ := (pow_add _ _ _).symm
  exact nbl_le_of_lt _ _ (hp.trans_lt (Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self _)))

/-- `lem:print`, paper/paper.tex: framing an
actual finite stream adds constant logarithmic overhead. -/
theorem bitLength_frame_length (bits : List Bool) :
    natBitLength (frame bits).length≤natBitLength bits.length+3 := by
  have hx:=lt_natBitLength bits.length
  have hp : 2*bits.length+1<2^(natBitLength bits.length+2) := by
    rw [pow_add]
    norm_num only [Nat.reducePow]
    omega
  rw [frame_length]
  exact nbl_le_of_lt _ _ hp

end NearQuarticWires.StageGreedyEntryBounds
