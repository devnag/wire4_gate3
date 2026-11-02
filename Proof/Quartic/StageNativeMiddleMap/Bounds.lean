import Proof.Quartic.StageNativeMiddleMap.Codec
import Proof.Quartic.StageNativeMiddleMap.Call

set_option autoImplicit false

namespace NearQuarticWires.StageNativeMiddleMap

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.CompilerMachine

theorem chainCost_eq (q : ℕ) (payload : List Bool) (count : ℕ) :
    chainCost q payload count=(StagePrint.NativeMiddle.word q payload count).length+10 := by
  rw [word_length]
  simp only [chainCost,Top.loadChainCost,List.length_nil]
  omega

theorem loadCost_eq (q : ℕ) (payload : List Bool) (count : ℕ) :
    loadCost q payload count=6*(StagePrint.NativeMiddle.word q payload count).length+27 := by
  change 2*(2*(StagePrint.NativeMiddle.word q payload count).length+1)+2+1+
    (2*chainCost q payload count+2)=_
  rw [chainCost_eq]
  omega

/-- `prop:time`, paper/paper.tex: one
absolute linear scale pays the actual record loader, one actual
callee call and cleanup, all marker copies and every physical reset. -/
def sourceSteps (recordLength calleeBudget : ℕ) : ℕ :=
  1000000*(recordLength+calleeBudget+1)

structure Rooms (q : ℕ) (input output : List Bool) (count B cap : ℕ) : Prop where
  load : 2*(StagePrint.NativeMiddle.word q input count).length+1 ≤ cap
  chain : chainCost q input count ≤ cap
  prepare : (frame input).length+1 ≤ cap
  call : 2*input.length+2+B ≤ cap
  copy : (frame output).length+1 ≤ cap
  emit : 4*((natWord q).length+(frame output).length+(natWord count).length)+100 ≤ cap
  total : loadCost q input count+(50*(frame input).length+10)+
    callCost input.length B output+
    1000*((natWord q).length+(frame output).length+(natWord count).length+1)+3 ≤ cap

theorem source_rooms (q : ℕ) (input output : List Bool) (count B : ℕ)
    (hout : (frame output).length ≤ B+1) :
    Rooms q input output count B (sourceSteps (StagePrint.NativeMiddle.word q input count).length B) := by
  have hrec:=word_length q input count
  have hframe : (frame input).length=2*input.length+1 := frame_length _
  constructor
  · unfold sourceSteps;omega
  · rw [chainCost_eq];unfold sourceSteps;omega
  · unfold sourceSteps;omega
  · unfold sourceSteps;omega
  · unfold sourceSteps;omega
  · unfold sourceSteps;omega
  · rw [loadCost_eq]
    unfold callCost StagePrint.callAppendCost sourceSteps
    omega

end NearQuarticWires.StageNativeMiddleMap
