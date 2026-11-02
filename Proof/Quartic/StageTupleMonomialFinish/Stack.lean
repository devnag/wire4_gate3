import Proof.Quartic.StageTupleMonomialFinish.Input
import Proof.Quartic.StageTupleMonomialFinish.PreparedRecords

set_option autoImplicit false

namespace NearQuarticWires.StageTupleMonomialFinish

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicGates.Close.WordPrograms
open StageTuple

/-- `lem:print`, paper/paper.tex: the genuine
Stack source is physically formatted and its raw signed cuts appended
to the original output prefix before all work tapes are cleared. -/
noncomputable def stackPhase (span : ℕ)
    (hp : stackRecordPrinter.program.tapeCount ≤ span) : WMX (span+29) 32 :=
  preparedRecordsProgram (.wm (stackPrepare span hp))
    (kernelSite span stackRecordPrinter.program hp) (kernelLocal span 21) 18

/-- `prop:time`, paper/paper.tex: Stack input
formatting and the actual raw output call have one additive local clock. -/
def stackPhaseCost (sr : StagePrint.StackRequest) : ℕ :=
  10000*stackInputMagnitude sr+1+callRecordsCost sr.word.length (2*sr.budget+2)

/-- `lem:print` and `prop:time`, paper/paper.tex: the complete physical Stack stage preserves the original
source, measured support cache and tuple history, appending precisely
the signed cut records of the actual current monomial. -/
theorem stackPhase_spec (span cap : ℕ)
    (hp : stackRecordPrinter.program.tapeCount ≤ span) (r : TermCutRequest)
    (data : MonomialData (17*(Builder.allGates r.header.call).length))
    (t : Finset (Fin (17*(Builder.allGates r.header.call).length))×ℤ)
    (ht : t∈r.terms) (horder : data.order=t.1.sort (·≤·)) (hcoeff : data.coefficient=t.2)
    (hinput : 400*stackInputMagnitude (r.stackRequest t ht)≤cap)
    (hcall : 2*(r.stackRequest t ht).word.length+2+(2*(r.stackRequest t ht).budget+2)≤cap)
    (hout : data.output.length+(r.stackRequest t ht).output.length+1≤cap) :
    ∃τ,WXExec cap (stackPhase span hp) (data.reverseState r span data.order.length) τ
      (stackPhaseCost (r.stackRequest t ht)) ∧
      SimW (appendO (data.reverseState r span data.order.length)
        (kernelLocal span 21) 18 (r.stackRequest t ht).output) τ := by
  have e := preparedRecordsProgram_spec stackRecordPrinter (r.stackRequest t ht)
    (stackRecords_nonempty _) cap (kernelSite span stackRecordPrinter.program hp)
    (kernelLocal span 21) 18
    (kernelSite_out span _ hp 21 (by decide) (by decide))
    (kernelSite_ruler_ne span _ hp 21 (by decide))
    (by simp [kernelSite,kernelCallRegisters])
    (.wm (stackPrepare span hp)) (10000*stackInputMagnitude (r.stackRequest t ht))
    (data.reverseState r span data.order.length)
    (data.reverseState_blank r span data.order.length _ hp)
    (WXExec.wm (stackPrepare_spec span cap hp r data t ht horder hcoeff hinput))
    (by simp [MonomialData.reverseState,MonomialData.reverseData,KernelData.state,kernelLocal])
    hcall (by simpa [MonomialData.reverseState,MonomialData.reverseData,KernelData.state,
      ←stack_output_records] using hout)
  simpa only [stackPhase,stackPhaseCost,stack_output_records] using e

end NearQuarticWires.StageTupleMonomialFinish
