import Proof.Quartic.StageResize.Request

set_option autoImplicit false

namespace NearQuarticWires.StageResize

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5.CompilerMachine

/-- `lem:print`, paper/paper.tex: actual low-first
field bits extend by zeros whenever the original value fits. -/
theorem binary_zero_extension {inputWidth outputWidth value : ℕ}
    (hfit : value < 2 ^ inputWidth) (hwidth : inputWidth ≤ outputWidth) :
    binary outputWidth value =
      binary inputWidth value ++ List.replicate (outputWidth - inputWidth) false := by
  have h := Pool.binary_append' inputWidth (outputWidth - inputWidth) value
  rw [Nat.add_sub_cancel' hwidth, Nat.div_eq_of_lt hfit, Pool.binary_zero'] at h
  exact h

/-- `lem:print`, paper/paper.tex: framed fields
decompose into the actual marked payload followed by one terminator. -/
theorem frame_eq_marked (bits : List Bool) : frame bits = Pool.fpre bits ++ [false] := by
  simpa only [List.append_nil, frame] using Pool.frame_append' bits []

/-- `lem:print`, paper/paper.tex: the exact source
payload followed by the required zero bits is the requested field. -/
theorem ResizeRequest.output_padding (r : ResizeRequest) :
    r.output = Pool.fpre (binary r.inputWidth r.value) ++
      Pool.fpre (List.replicate (r.outputWidth - r.inputWidth) false) ++ [false] := by
  rw [ResizeRequest.output, binary_zero_extension r.fits r.width_le, frame_eq_marked]
  simp [Pool.fpre, List.flatMap_append, List.append_assoc]

end NearQuarticWires.StageResize
