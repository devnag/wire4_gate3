import Proof.Quartic.StagePrint.RawWeightList
import Proof.Gates.WordPrograms.RecLoop

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StagePrint.RawBits
open NearCubicWires NearCubicWires.RepairOrdinary.SignedSortKey
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.WordPrograms
open NearCubicGates.Close.WordPrograms.SInt (encS)

/-- `lem:print`, paper/paper.tex: two physical framing layers agree bit for bit with the coefficient writer. -/
theorem layered_two_eq (xs : List Bool) :
    xs.flatMap (layeredBit 2)=frameP (frameP xs) := by
  induction xs with
  | nil => rfl
  | cons b bs ih =>
    change [true,true,true,b]++bs.flatMap (layeredBit 2)=
      [true,true,true,b]++frameP (frameP bs)
    rw [ih]

/-- `lem:print`, paper/paper.tex: the serialized signed weight is exactly one framed record inside the outer load field. -/
theorem weightField_eq (W : ℕ) (z : ℤ) :
    weightField W z=frameP (frame (binary W (encS z))) := by
  rw [weightField,layered_two_eq,frame_eq_frameP]
  simp [frameP,List.flatMap_append]

/-- `lem:print`, paper/paper.tex: the original-weight input scan, followed by three closing bits, is exactly the cold child compiler's first load field. -/
theorem weights_field_eq (W : ℕ) (zs : List ℤ) :
    zs.flatMap (weightField W) ++ [true,false,false] =
      frame (recStream (zs.map fun z=>binary W (encS z))) := by
  rw [frame_eq_frameP,recStream]
  simp only [frameP,List.flatMap_append,List.flatMap_singleton]
  have hh : zs.flatMap (weightField W)=
      ((zs.map fun z=>binary W (encS z)).flatMap frame).flatMap (fun b=>[true,b]) := by
    induction zs with
    | nil => rfl
    | cons z zs ih =>
      simp only [List.flatMap_cons,List.map_cons,List.flatMap_append]
      rw [ih,weightField_eq]
      rfl
  rw [hh]
  simp [List.append_assoc]

end NearQuarticWires.StagePrint.RawBits
