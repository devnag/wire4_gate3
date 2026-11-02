import Proof.Quartic.StageEqualityRows.StripLoad

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageEqualityRows

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.Codec
open NearCubicGates.Close.Expand.PolyTab
open StagePrint

/-- `lem:print`, paper/paper.tex: compute the
literal dense field stride from the width read from the source. -/
theorem makeStride_general (cap w : ℕ) (a : WState 15 24)
    (hw : a.val 14=w) (h2 : a.val 2=0) (h16 : a.val 16=0) (hcap : 2*w+2≤cap) :
    WExec cap makeStride a (a.setv 2 (2*w+2)) (36*w+16) := by
  have e1:=addTo_spec cap (14 : Fin 24) 2 16 (by decide) (by decide) (by decide) a h16
    (by rw [hw];omega) (by rw [h2,hw];omega)
  let b:=a.setv 2 w
  have e1' : WExec cap (addTo 14 2 16) a b (18*w+3) := by simpa only [hw,h2,Nat.zero_add] using e1
  have e2:=addTo_spec cap (14 : Fin 24) 2 16 (by decide) (by decide) (by decide) b
    (by simp [b,h16]) (by simp [b,hw];omega) (by simp [b,hw];omega)
  let c:=b.setv 2 (2*w)
  have e2' : WExec cap (addTo 14 2 16) b c (18*w+3) := by
    simpa only [c,b,WState.setv_val,Function.update_self,
      Function.update_of_ne (by decide : (14 : Fin 24)≠2),hw,two_mul] using e2
  have e3:=WExec.inc (cap:=cap) (2 : Fin 24) c (by simp [c];omega)
  let d:=c.setv 2 (c.val 2+1)
  have e4:=WExec.inc (cap:=cap) (2 : Fin 24) d (by simp [d,c];omega)
  refine (e1'.seq (e2'.seq (e3.seq e4))).cast cap ?_ (by omega)
  simp only [d,c,b,WState.setv_val,Function.update_self,wsetv_setv]

def columnCounted (r : NativeStreamRequest) : WState 15 24 := (widthRead r).setv 17 (width r)
def stripStride (r : NativeStreamRequest) : WState 15 24 :=
  (columnCounted r).setv 2 (2*width r+2)
def temporaryHeader (r : NativeStreamRequest) : List Bool :=
  (temporaryNaturals r).flatMap NearCubicWires.RepairRepresentation.natWord++(temporaryColumns r).flatMap frame

def headerReady (r : NativeStreamRequest) : WState 15 24 :=
  ((stripStride r).seth 1 (temporaryHeader r).length).setv 17 0

def stripColumnsProgram : WM 15 24 :=
  .seq (dupR 14 17 16) (.seq makeStride (skipRecords 1 17))

def columnsSteps (r : NativeStreamRequest) : ℕ :=
  (18*width r+3)+(36*width r+16)+
    (((temporaryColumns r).map (fun bits=>5*bits.length+7)).sum+1)+2

/-- `lem:print`, paper/paper.tex: the actual
runtime column count scans each genuine framed column, ending exactly
at the original signed weak body without a logical header-length input. -/
theorem stripColumns_run (r : NativeStreamRequest) :
    WExec (stripCapacity r) stripColumnsProgram (widthRead r) (headerReady r) (columnsSteps r) := by
  have e1:=dupR_spec (stripCapacity r) (14 : Fin 24) 17 16 (by decide) (by decide) (by decide)
    (widthRead r) rfl (by simp [widthRead,afterLeading,stripLoaded,stripStart,idealStart];unfold stripCapacity capacity;omega)
  have e1' : WExec (stripCapacity r) (dupR 14 17 16) (widthRead r) (columnCounted r)
      (18*width r+3) := by simpa [widthRead,columnCounted,afterLeading,stripLoaded,stripStart,idealStart] using e1
  have e2:=makeStride_general (stripCapacity r) (width r) (columnCounted r)
    (by simp [columnCounted,widthRead]) rfl rfl (by unfold stripCapacity capacity;omega)
  have e3:=skipRecords_run (stripCapacity r) (1 : Fin 16) 17 (temporaryColumns r)
    ((temporaryNaturals r).flatMap NearCubicWires.RepairRepresentation.natWord) (weakStream r) (stripStride r)
    (by simp [stripStride,columnCounted,widthRead,afterLeading,stripLoaded,temporaryWord_shape,List.append_assoc])
    (by simp [stripStride,columnCounted,widthRead,afterLeading,temporaryNaturals,leadingWord,
      leadingNaturals,List.append_assoc,Nat.add_assoc])
    (by simp [stripStride,columnCounted,temporaryColumns_length])
    (by rw [temporaryColumns_length];unfold stripCapacity capacity;omega)
  have e3' : WExec (stripCapacity r) (skipRecords 1 17) (stripStride r) (headerReady r)
      (((temporaryColumns r).map (fun bits=>5*bits.length+7)).sum+1) := by
    simpa only [headerReady,temporaryHeader,List.length_append] using e3
  exact (e1'.seq (e2.seq e3')).mono (by unfold columnsSteps;omega)

end NearQuarticWires.StageEqualityRows
