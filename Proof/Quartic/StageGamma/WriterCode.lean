import Proof.Quartic.StageGamma.Writer
import Proof.Wire_3_5.GF2Machines

set_option autoImplicit false

namespace NearQuarticWires.StageGamma

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5
open NearCubicGates.Close.Cells

/-- `cor:conditional`, paper/paper.tex: each
physical bit of a recipe may be replaced by its fixed marker code. -/
def Writer.mapBits (code : Bool → List Bool) : Writer → Writer
  | .literal bits => .literal (bits.flatMap code)
  | .ruler count bits => .ruler count (bits.flatMap code)
  | .binary count value payload =>
      .binary count value (fun bit => (payload bit).flatMap code)
  | .seq first second => .seq (first.mapBits code) (second.mapBits code)
  | .nonzero test body => .nonzero test (body.mapBits code)

/-- `cor:conditional`, paper/paper.tex: coding
preserves the exact finite register interface of the producer. -/
theorem Writer.params_mapBits (w : Writer) (code : Bool → List Bool) :
    (w.mapBits code).params = w.params := by
  induction w <;> simp_all [mapBits, params]

/-- `cor:conditional`, paper/paper.tex: coding
adds no source-register or scratch assumptions. -/
theorem Writer.safe_mapBits (w : Writer) (code : Bool → List Bool) :
    (w.mapBits code).Safe ↔ w.Safe := by
  induction w <;> simp_all [mapBits, Safe]

/-- `cor:conditional`, paper/paper.tex: fixed bit
codes commute with finite unary rulers. -/
theorem bitBlocks_flatMap (bits : List Bool) (n : ℕ) (code : Bool → List Bool) :
    (bitBlocks bits n).flatMap code = bitBlocks (bits.flatMap code) n := by
  induction n with
  | zero => simp [bitBlocks]
  | succ n ih => rw [bitBlocks_succ, List.flatMap_append, ih, bitBlocks_succ]

/-- `cor:conditional`, paper/paper.tex: coding a
record recipe prints exactly the coded source word, including branches. -/
theorem Writer.bits_mapBits (w : Writer) (code : Bool → List Bool) (a : DS VV MM) :
    (w.mapBits code).bits a = (w.bits a).flatMap code := by
  induction w with
  | literal payload => rfl
  | ruler count payload => exact (bitBlocks_flatMap payload _ code).symm
  | binary count value payload => simp only [mapBits, bits, List.flatMap_assoc]
  | seq first second hf hs => simp only [mapBits, bits, hf, hs, List.flatMap_append]
  | nonzero test body ih => simp only [mapBits, bits]; split_ifs <;> simp_all

/-- `cor:conditional`, paper/paper.tex: one outer
record frame is physically generated around a complete payload recipe. -/
def Writer.framed (w : Writer) : Writer :=
  .seq (w.mapBits (fun bit => [true, bit])) (.literal [false])

/-- `cor:conditional`, paper/paper.tex: the framed
writer has exactly the original producer's source registers. -/
theorem Writer.params_framed (w : Writer) : w.framed.params = w.params := by
  simp [framed, params, params_mapBits]

/-- `cor:conditional`, paper/paper.tex: the framed
writer is safe precisely when its actual payload writer is safe. -/
theorem Writer.safe_framed (w : Writer) : w.framed.Safe ↔ w.Safe := by
  simp [framed, Safe, safe_mapBits]

/-- `cor:conditional`, paper/paper.tex: the printed
record is literally the handoff frame required by the Gaussian loader. -/
theorem Writer.bits_framed (w : Writer) (a : DS VV MM) :
    w.framed.bits a = frame (w.bits a) := by
  simp only [framed, bits, bits_mapBits]
  induction w.bits a with
  | nil => rfl
  | cons bit bits ih => simpa [frame] using congrArg (fun xs => true :: bit :: xs) ih

/-- `cor:conditional`, paper/paper.tex: the low-bit
binary emission order is exactly the Gaussian arithmetic codec's order. -/
theorem binary_eq_testBits (N v : ℕ) :
    binary N v = (List.range N).map v.testBit := by
  apply List.ext_getElem (by simp)
  intro i hi hj
  rw [GF2.binary_getElem N v i hi]
  simp

/-- `cor:conditional`, paper/paper.tex: an uncoded
binary writer emits the exact fixed-width arithmetic payload. -/
def Writer.binaryWord (count value : Fin VV) : Writer :=
  .binary count value (fun bit => [bit])

/-- `cor:conditional`, paper/paper.tex: payload
bits include every leading zero bit demanded by the actual field width. -/
theorem Writer.bits_binaryWord (count value : Fin VV) (a : DS VV MM) :
    (Writer.binaryWord count value).bits a =
      NearCubicWires.RepairOrdinary.SignedSortKey.binary (a.env count) (a.env value) := by
  simp [binaryWord, bits, ← binary_eq_testBits]

end NearQuarticWires.StageGamma
