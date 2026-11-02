import Proof.Wire_3_5.CompilerMachinePoolConv
import Proof.Gates.Cells.Run

set_option autoImplicit false

namespace NearQuarticWires.StageResize

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicGates.Close.Interfaces

/-- `lem:print`, paper/paper.tex: one actual fixed
binary field, its enclosing target width, and mathematical fit bounds. -/
structure ResizeRequest where
  inputWidth : ℕ
  outputWidth : ℕ
  value : ℕ
  fits : value < 2 ^ inputWidth
  width_le : inputWidth ≤ outputWidth

/-- `lem:print`, paper/paper.tex: the only scalar
input is the target width; the source field is already framed. -/
def ResizeRequest.word (r : ResizeRequest) : List Bool :=
  natWord r.outputWidth ++ frame (binary r.inputWidth r.value)

/-- `lem:print`, paper/paper.tex: extension returns
exactly one frame around the target-width binary payload. -/
def ResizeRequest.output (r : ResizeRequest) : List Bool :=
  frame (binary r.outputWidth r.value)

/-- `lem:print`, paper/paper.tex: the cold machine
contract consumes only the target-width codec and actual source bits. -/
abbrev ResizeWordFunction (budget : ResizeRequest → ℕ) :=
  WordFunction ResizeRequest ResizeRequest.word ResizeRequest.output budget

/-- `prop:time`, paper/paper.tex: the actual source
length charges both the width codec and every framed payload bit. -/
theorem ResizeRequest.word_length (r : ResizeRequest) :
    r.word.length = 2 * natBitLength r.outputWidth + 2 * r.inputWidth + 2 := by
  simp only [ResizeRequest.word, List.length_append, Pool.natWord_eq, List.length_replicate,
    List.length_cons, frame_length, binary_length]
  omega

/-- `lem:print`, paper/paper.tex: empty target
width has the unique empty framed payload. -/
theorem ResizeRequest.output_zero (r : ResizeRequest) (h : r.outputWidth = 0) :
    r.output = [false] := by
  simp [ResizeRequest.output, h, binary, frame]

end NearQuarticWires.StageResize
