import Proof.Quartic.StagePrintTuple.InputContracts
import Proof.Quartic.StageStackInput.CachedFrames

set_option autoImplicit false

namespace NearQuarticWires.StageTupleInputs

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicGates.Close
open StageTuple

/-- `lem:print`, paper/paper.tex: the exact native
pool packet retains its two nested source frames and three ordinary
fields, followed by the existing six empty fields and outer delimiter. -/
theorem nativeInput_frame (a b c d e : List Bool) :
    frame (nativeKidsInputWord a b c d e)=
      marks (frame (frame a))++marks (frame (frame b))++
      StageStackInput.cachedFramesBytes [c,d,e]++
      marks (List.replicate 6 false)++[false] := by
  simp [nativeKidsInputWord,Top.loadRec,Codec.frame_eq_marks,
    StageStackInput.cachedFramesBytes,List.replicate_succ,marks,List.append_assoc]

/-- `prop:time`, paper/paper.tex: packet length
counts exactly the actual five finite framed source fields. -/
theorem nativeInput_length (a b c d e : List Bool) :
    (frame (nativeKidsInputWord a b c d e)).length=
      4*(frame a).length+4*(frame b).length+2*(frame c).length+
      2*(frame d).length+2*(frame e).length+17 := by
  rw [nativeInput_frame]
  simp only [List.length_append,Codec.marks_length,frame_length,
    StageStackInput.cachedFramesBytes,List.flatMap_cons,List.flatMap_nil,
    List.length_replicate,List.length_cons,List.length_nil]
  omega

theorem nativeCached_length (c d e : List Bool) :
    (StageStackInput.cachedFramesBytes [c,d,e]).length=
      2*(frame c).length+2*(frame d).length+2*(frame e).length := by
  simp only [StageStackInput.cachedFramesBytes,List.flatMap_cons,List.flatMap_nil,
    List.length_append,Codec.marks_length,List.length_nil]
  omega

theorem nativeCached_cost (c d e : List Bool) :
    StageStackInput.cachedFramesCost [c,d,e]=
      100*((frame c).length+(frame d).length+(frame e).length)+303 := by
  simp only [StageStackInput.cachedFramesCost,appendMarkedFrameCost]
  omega

end NearQuarticWires.StageTupleInputs
