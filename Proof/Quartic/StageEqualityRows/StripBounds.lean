import Proof.Quartic.StageEqualityRows.StripData
import Proof.Quartic.Control.Budget

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageEqualityRows

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open StagePrint

/-- `prop:time`, paper/paper.tex: scanning the
actual temporary columns costs their literal quadratic-width bytes. -/
theorem temporaryColumns_streamLength (r : NativeStreamRequest) :
    ((temporaryColumns r).flatMap frame).length=width r*(2*width r+1) := by
  rw [List.length_flatMap]
  have h : (temporaryColumns r).map (fun col=>(frame col).length)=
      (temporaryColumns r).map (fun _=>2*width r+1) := by
    apply List.map_congr_left
    intro col hc
    rw [frame_length,temporaryColumns_bitLength r col hc]
  rw [h]
  simp [temporaryColumns_length]

/-- `prop:time`, paper/paper.tex: the physical
unframer's source capacity accounts for the actual header and weak
body, without expanding the exponential number of table entries. -/
theorem temporaryWord_length_le (r : NativeStreamRequest) :
    (temporaryWord r).length ≤ stripCapacity r := by
  rw [temporaryWord_shape,List.length_append,List.length_append,temporaryColumns_streamLength]
  have hw:=bitLength_le (width r)
  have hp:=bitLength_le (r.fieldWidth+1)
  have hg:=bitLength_le (2*r.cuts.length)
  have hb:=weakStream_le r
  simp only [temporaryNaturals,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.length_append,
    NearCubicGates.Close.CounterAsm.natWord_len]
  unfold stripCapacity capacity
  nlinarith

/-- `lem:print`, paper/paper.tex: only the
small dense width is decoded numerically from the temporary header. -/
theorem width_decode_fits (r : NativeStreamRequest) :
    2^(natBitLength (width r)+1) ≤ stripCapacity r := by
  have h:=Control.two_pow_natBitLength_le (width r)
  rw [Nat.pow_succ]
  unfold stripCapacity capacity
  nlinarith

end NearQuarticWires.StageEqualityRows
