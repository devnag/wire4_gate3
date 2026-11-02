import Proof.Quartic.StageEqualityRows.StripColumns

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageEqualityRows

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.Codec
open NearCubicGates.Close.Recovery.HTParts NearCubicGates.Close.Expand.PolyTab
open StagePrint

/-- `lem:print`, paper/paper.tex: the complete
header scan leaves only the actual dense width and field stride in
its arithmetic registers. -/
theorem headerReady_values (r : NativeStreamRequest) :
    (headerReady r).val=![0,0,2*width r+2,0,0,0,0,0,0,0,0,0,0,0,width r,0,0,0,0,0,0,0,0,0] := by
  funext i
  fin_cases i <;> simp [headerReady,stripStride,columnCounted,widthRead,afterLeading,stripLoaded,
    stripStart,idealStart]

def bodyCounted (r : NativeStreamRequest) : WState 15 24 :=
  (adv 1 14 0 1 (headerReady r) [] (weakStream r).length).setv 5 (2*r.cuts.length)
def weakCountSteps (r : NativeStreamRequest) : ℕ :=
  25*(weakStream r).length+(2*r.cuts.length)*(22*(2*width r+2)+11)+1

/-- `lem:print`, paper/paper.tex: the remaining
weak-body byte count is measured by scanning its actual scalar frames. -/
theorem bodyCounted_run (r : NativeStreamRequest) :
    WExec (stripCapacity r) (CutScan.countRows 1 countRegisters) (headerReady r) (bodyCounted r)
      (weakCountSteps r) := by
  have hB:=weakStream_le r
  have e:=CutScan.nativeCutCount_spec (stripCapacity r) 1 14 countRegisters (by decide)
    (width r) (r.fieldWidth+1) (EquationRow.doubled false r.cuts)
    (by change ∀ c∈r.matrix.cuts,c.leftWeights.length=width r ∧ c.rightWeights.length=width r
        exact r.matrix.lengths)
    (temporaryHeader r) [] rfl (headerReady r)
    (by simp only [headerReady,stripStride,columnCounted,widthRead,afterLeading,stripLoaded,
        WState.setv_st,WState.seth_st,WState.sets_st,Function.update_self,
        temporaryWord_shape,temporaryHeader,weakStream,List.append_nil,List.append_assoc])
    (by simp [headerReady])
    (by simp [headerReady,stripStride,columnCounted,widthRead,afterLeading,stripLoaded,
        stripStart,idealStart])
    (by rw [headerReady_values];rfl) rfl rfl
    (by change 0≤ stripCapacity r;omega)
    (by change 0+(weakStream r).length≤ stripCapacity r;unfold stripCapacity capacity;omega)
    (by unfold stripCapacity capacity;omega)
    (by simp only [EquationRow.doubled_length];change 0+2*r.cuts.length≤ stripCapacity r
        unfold stripCapacity capacity;omega)
  have h5 : (headerReady r).val (countRegisters 5)=0 := by rw [headerReady_values];rfl
  rw [h5,Nat.zero_add,EquationRow.doubled_length] at e
  exact e

/-- `lem:print`, paper/paper.tex: the measured
weak body has its literal source-byte count, independently of the
large signed values stored in those fields. -/
theorem bodyCounted_values (r : NativeStreamRequest) :
    (bodyCounted r).val=![0,(weakStream r).length,2*width r+2,0,0,2*r.cuts.length,
      0,0,0,0,0,0,0,0,width r,0,0,0,0,0,0,0,0,0] := by
  funext i
  fin_cases i <;> simp [bodyCounted,adv,headerReady_values]

def bodyCopyReady (r : NativeStreamRequest) : WState 15 24 :=
  (((bodyCounted r).setv 16 (weakStream r).length).setv 1 0).seth 1 (temporaryHeader r).length

/-- `lem:print`, paper/paper.tex: a real rewind
returns to the measured weak-body start, after the physically removed
header, and retains its byte count for unchanged output. -/
theorem bodyCopyReady_run (r : NativeStreamRequest) :
    WExec (stripCapacity r) (.seq (dupR 1 16 17) (WM.rewind 1 1)) (bodyCounted r) (bodyCopyReady r)
      (23*(weakStream r).length+6) := by
  have hB:=weakStream_le r
  have e1:=dupR_spec (stripCapacity r) (1 : Fin 24) 16 17 (by decide) (by decide) (by decide)
    (bodyCounted r) (by rw [bodyCounted_values];rfl)
    (by rw [bodyCounted_values];dsimp;unfold stripCapacity capacity;omega)
  rw [bodyCounted_values] at e1
  let a:=(bodyCounted r).setv 16 (weakStream r).length
  have e1' : WExec (stripCapacity r) (dupR 1 16 17) (bodyCounted r) a
      (18*(weakStream r).length+3) := by simpa [a] using e1
  have h1 : a.val 1=(weakStream r).length := by simp [a,bodyCounted_values]
  have e2:=wrewind_spec (stripCapacity r) (1 : Fin 16) 1 (weakStream r).length a h1
    (by rw [h1];unfold stripCapacity capacity;omega)
  refine (e1'.seq e2).cast (stripCapacity r) ?_ (by omega)
  unfold bodyCopyReady
  congr 1
  simp [a,bodyCounted,adv,headerReady]

end NearQuarticWires.StageEqualityRows
