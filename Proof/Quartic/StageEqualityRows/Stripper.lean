import Proof.Quartic.StageEqualityRows.StripOutput
import Proof.Quartic.StageEqualityRows.Construct

set_option autoImplicit false

namespace NearQuarticWires.StageEqualityRows

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.Expand.PolyTab
open StagePrint StagePrint.Downstream

def widthReadSteps (r : NativeStreamRequest) : ℕ :=
  (natBitLength (width r)+2)*(40*2^natBitLength (width r)+40)
def stripperSteps (r : NativeStreamRequest) : ℕ :=
  (23*(temporaryWord r).length+5)+rawNaturalCost (leadingNaturals r)+widthReadSteps r+
    columnsSteps r+bodySteps r+10

/-- `lem:print`, paper/paper.tex: the ordinary
stripper consumes the temporary framed header physically and emits
only its original signed two-weak-cut body in one frame. -/
noncomputable def stripperProgram : WMX 15 24 :=
  .seq (.wm (StageGamma.unframeRecord 0 1 20))
    (.seq (.wm (skipRawNaturals 1 6 7 3))
      (.seq (.wm (readNatM false 1 6 7 14 8 9))
        (.seq (.wm stripColumnsProgram) (.wm stripBodyProgram))))

theorem stripperProgram_run (r : NativeStreamRequest) :
    ∃ final,WXExec (stripCapacity r) stripperProgram (stripStart r) final (stripperSteps r) ∧
      final.st 15=equalityRowsOutput r := by
  obtain ⟨final,he,ho⟩:=stripBodyProgram_run r
  have e:=(WXExec.wm (stripLoaded_run r)).seq ((WXExec.wm (afterLeading_run r)).seq
    ((WXExec.wm (widthRead_run r)).seq ((WXExec.wm (stripColumns_run r)).seq (WXExec.wm he))))
  exact ⟨final,e.mono (by unfold stripperSteps widthReadSteps;omega),ho⟩

/-- `lem:print` and `prop:time`, paper/paper.tex: the suffix printer is cold and reads the actual
four-natural, framed-column header rather than a supplied byte offset. -/
noncomputable def stripperWordFunction :
    WordFunction NativeStreamRequest temporaryWord equalityRowsOutput (fun r=>2*stripperSteps r+2) :=
  wordFunction_of_ideal stripperProgram (15 : Fin 16) (by decide) stripCapacity (fun _ _=>0)
    stripperSteps (fun _=>le_rfl) (fun r=>⟨rfl,stripperProgram_run r⟩)

def rowBudget (r : NativeStreamRequest) : ℕ :=
  4*constructionBudget r+4*(2*stripperSteps r+2)+12

/-- `lem:print`, paper/paper.tex: the literal
raw equality stream and its two unary widths suffice for the complete
measured-count, signed-row and framed-body ordinary construction. -/
noncomputable def rowWordFunction :
    WordFunction NativeStreamRequest equalityRowsInput equalityRowsOutput rowBudget :=
  Program.WordFunction.pipe constructionWordFunction stripperWordFunction

end NearQuarticWires.StageEqualityRows
