import Proof.Quartic.StageNativeMiddleMap.Load
import Proof.Quartic.StageNativeMiddleMap.Prepare
import Proof.Quartic.StageNativeMiddleMap.Avoid
import Proof.Quartic.StageNativeMiddleMap.Emit
import Proof.Quartic.StageNativeMiddleMap.Bounds
import Proof.Quartic.Control.GammaControl

set_option autoImplicit false

namespace NearQuarticWires.StageNativeMiddleMap

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.CheckedPCPP
open NearCubicGates.Close.Expand.PolyTab
open NearQuarticWires.Control

theorem sequence_cost (l p c e cap : ℕ) (h : l+p+c+e+3 ≤ cap) :
    l+1+(p+1+(c+1+e)) ≤ cap := by omega

/-- `lem:print`, paper/paper.tex: the
complete cold middle mapper loads the real record, isolates its middle
input, executes the actual callee once and emits the unchanged layout. -/
noncomputable def program (p : Program) : WMX (p.tapeCount+19) 32 :=
  .seq (.mach Top.loadM (loadMap p))
    (.seq (prepareProgram p) (.seq (callProgram p) (.wm (formatProgram (formatSlots p) 7 8 9))))

/-- `lem:print` and `prop:time`, paper/paper.tex: the actual source record alone supplies
every byte, head and input-bank field for one actual middle call.
The full clock is linear in source bytes plus the real callee budget. -/
theorem program_exec {Request : Type} {input output : Request→List Bool} {calleeBudget : Request→ℕ}
    (f : WordFunction Request input (fun r=>frame (output r)) calleeBudget)
    (r : Request) (q count : ℕ) :
    let p:=f.program
    let cap:=sourceSteps (StagePrint.NativeMiddle.word q (input r) count).length (calleeBudget r)
    ∃ b,WXExec cap (program p)
      (idealStart (p.tapeCount+19) 32 (StagePrint.NativeMiddle.word q (input r) count) (lens p cap))
      b cap ∧ b.st (final p)=frame (StagePrint.NativeMiddle.word q (output r) count) := by
  let p:=f.program
  let cap:=sourceSteps (StagePrint.NativeMiddle.word q (input r) count).length (calleeBudget r)
  have hrooms:=source_rooms q (input r) (output r) count (calleeBudget r) (output_length_le f r)
  have el:=load_exec p cap q (input r) count hrooms.load hrooms.chain
  have ep:=prepare_exec p cap q (input r) count hrooms.prepare
  obtain ⟨a,ec,hs⟩:=call_exec f r cap q count hrooms.call hrooms.copy
  have hF : (site p).input≠final p := (final_fresh p).2 _
  have hf : (prepared p cap q (input r) count).st (final p)=[] := by
    change Function.update (loaded p cap q (input r) count).st
      (site p).input (frame (input r)) (final p)=[]
    rw [Function.update_of_ne hF.symm]
    simp [loaded,final]
  have ha : a.st (final p)=[] := ((WXExec.avoids ec (call_avoids_final p)).1).trans hf
  obtain ⟨b,ee,hb⟩:=emit_exec p cap q count (input r) (output r) a hs ha hrooms.emit
  have hcost:=sequence_cost (loadCost q (input r) count) (50*(frame (input r)).length+10)
    (callCost (input r).length (calleeBudget r) (output r))
    (1000*((NearCubicWires.RepairRepresentation.natWord q).length+(frame (output r)).length+
      (NearCubicWires.RepairRepresentation.natWord count).length+1)) cap hrooms.total
  exact ⟨b,(el.seq (ep.seq (ec.seq (WXExec.wm ee)))).mono hcost,hb⟩

end NearQuarticWires.StageNativeMiddleMap
