import Proof.Quartic.StageEqualityRows.Count
import Proof.Gates.Codec.Frame

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageEqualityRows

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.Recovery.HTParts
open NearCubicGates.Close.CounterAsm NearCubicGates.Close.Codec
open StagePrint

/-- `lem:print`, paper/paper.tex: every numeric
metadata value below is the result of the physical field scan. -/
theorem counted_values (r : NativeStreamRequest) :
    (counted r).val=![0,(stream r).length,2*width r+2,0,0,r.cuts.length,0,0,0,0,0,0,0,0,
      width r,r.fieldWidth,0,0,0,0,0,0,0,0] := by
  funext i
  fin_cases i <;> simp [counted,strideState,afterFields,afterWidth,loaded,adv]

def copyReady (r : NativeStreamRequest) : WState 15 24 :=
  (((counted r).setv 16 (stream r).length).setv 1 0).seth 2 0

/-- `lem:print`, paper/paper.tex: retain the
measured original stream length, then rewind precisely those source
bytes for unchanged physical output. -/
theorem copyReady_run (r : NativeStreamRequest) :
    WExec (capacity r) (.seq (dupR 1 16 17) (WM.rewind 2 1)) (counted r) (copyReady r)
      (23*(stream r).length+6) := by
  have e1:=dupR_spec (capacity r) (1 : Fin 24) 16 17 (by decide) (by decide) (by decide)
    (counted r) (by rw [counted_values];rfl)
    (by rw [counted_values];unfold capacity;dsimp;omega)
  rw [counted_values] at e1
  let a:=(counted r).setv 16 (stream r).length
  have e1' : WExec (capacity r) (dupR 1 16 17) (counted r) a (18*(stream r).length+3) := by
    simpa [a] using e1
  have h1 : a.val 1=(stream r).length := by simp [a,counted_values]
  have e2:=wrewind_spec (capacity r) (2 : Fin 16) 1 (stream r).length a h1
    (by rw [h1];unfold capacity;omega)
  refine (e1'.seq e2).cast (capacity r) ?_ (by omega)
  unfold copyReady
  congr 1
  simp [a,counted,adv,strideState,afterFields,afterWidth,loaded]

end NearQuarticWires.StageEqualityRows
