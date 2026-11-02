import Proof.Quartic.StageEqualityRows.Finish
import Proof.Quartic.Program.Pipe

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageEqualityRows

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.Expand.PolyTab
open StagePrint StagePrint.Downstream

def formatterSteps (r : NativeStreamRequest) : ℕ :=
  loadCost r+(16*width r+14)+(16*r.fieldWidth+14)+(36*width r+16)+countCost r+
    (23*(stream r).length+6)+
    (naturalCost (width r)+naturalCost r.fieldWidth+naturalCost r.cuts.length+2)+
    (22*(stream r).length+26)+20

/-- `lem:print`, paper/paper.tex: all ordinary
input acquisition, measured census, metadata emission and original
signed-row copying are performed by one physical program. -/
noncomputable def formatterProgram : WMX 15 24 :=
  .seq (.mach NearCubicWires.WireExponent3_5.CompilerMachine.Top.loadM loadMap)
    (.seq (unaryRegister 3 6 14) (.seq (unaryRegister 4 6 15)
      (.seq (.wm makeStride) (.seq (.wm (CutScan.countRows 2 countRegisters))
        (.seq (.wm (.seq (NearCubicGates.Close.Codec.dupR 1 16 17) (WM.rewind 2 1)))
          (.seq (.wm headerProgram) (.wm finishProgram)))))))

theorem formatterProgram_run (r : NativeStreamRequest) :
    ∃ final,WXExec (capacity r) formatterProgram
      (idealStart 15 24 (equalityRowsInput r) (lens r)) final (formatterSteps r) ∧
      final.st 15=frame r.equalitySource := by
  obtain ⟨final,hf,ho⟩:=finishProgram_run r
  have e:=(load_spec (capacity r) r).seq ((width_run r).seq ((fieldWidth_run r).seq
    ((WXExec.wm (makeStride_run r)).seq ((WXExec.wm (count_run r)).seq
      ((WXExec.wm (copyReady_run r)).seq ((WXExec.wm (headerProgram_run r)).seq (WXExec.wm hf)))))))
  exact ⟨final,e.mono (by unfold formatterSteps;omega),ho⟩

/-- `lem:print` and `prop:time`, paper/paper.tex: the real cold source constructor receives no equality
count and emits precisely the existing original-row request frame. -/
noncomputable def formatterWordFunction :
    WordFunction NativeStreamRequest equalityRowsInput (fun r=>frame r.equalitySource)
      (fun r=>2*formatterSteps r+2) :=
  wordFunction_of_ideal formatterProgram (15 : Fin 16) (by decide) capacity lens formatterSteps
    (fun _=>le_rfl) (fun r=>⟨rfl,formatterProgram_run r⟩)

end NearQuarticWires.StageEqualityRows
