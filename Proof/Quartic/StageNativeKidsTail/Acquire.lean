import Proof.Quartic.StageNativeKidsTail.ReadyABI

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageNativeKidsTail

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close NearCubicGates.Close.WordPrograms NearCubicGates.Close.CounterMachine
open NearCubicGates.Close.Expand.PolyTab
open StageNativeKids StageResize StageTuple

/-- `lem:print`, paper/paper.tex: the concrete
resize source and literal binary count prefix are acquired together,
with actual delimiter emission and all required input-head returns. -/
noncomputable def acquireProgram (f : ResizeCallee) : WMX (f.program.tapeCount+3) 5 :=
  .seq (.wm (StageGamma.unframeRecord 0 1 4))
    (.seq (.wm (copyCount f.program.tapeCount))
      (.seq (.wm (copyNaturalFields 1 1 (inputTape f) 3 1 2))
        (.seq (.wm (CounterAsm.frameLoop 1 1 (fun b=>emitPair (inputTape f) 3 b)))
          (.wm (finishInputProgram f)))))

def acquireSteps (r : ResizeTailRequest) : ℕ := 200*(r.word.length+1)

theorem acquireProgram_run (f : ResizeCallee) (r : ResizeTailRequest) :
    WXExec (capacity r) (acquireProgram f) (start f r) (ready f r) (acquireSteps r) := by
  have hlen:=source_length r
  have e:=(WXExec.wm (load_run f r)).seq ((WXExec.wm (copyCount_run f r)).seq
    ((WXExec.wm (copyWidth_run f r)).seq ((WXExec.wm (copyRecords_run f r)).seq
      (WXExec.wm (finishInput_run f r)))))
  exact e.mono (by unfold acquireSteps;omega)

end NearQuarticWires.StageNativeKidsTail
