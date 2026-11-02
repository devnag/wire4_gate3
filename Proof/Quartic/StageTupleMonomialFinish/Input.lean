import Proof.Quartic.StageTupleMonomialFinish.Data
import Proof.Quartic.StageStackInput.Program

set_option autoImplicit false

namespace NearQuarticWires.StageTupleMonomialFinish

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.TabMachine NearCubicGates.Close.WordPrograms
open StageTuple

/-- `lem:print`, paper/paper.tex: the complete
post-reverse formatter reads the literal final tuple segment and the
three genuine constant/coefficient fields into the Stack call bank. -/
noncomputable def stackPrepare (span : ℕ)
    (hp : stackRecordPrinter.program.tapeCount ≤ span) : WM (span+29) 32 :=
  StageStackInput.stackInputProgram
    (kernelPacketMap span kernelStackSources stackRecordPrinter.program hp) kernelStackRegisters

/-- `lem:print` and `prop:time`, paper/paper.tex: the actual reverse-loop boundary physically produces
the genuine Stack source, preserving all other tapes and counters. -/
theorem stackPrepare_spec (span cap : ℕ)
    (hp : stackRecordPrinter.program.tapeCount ≤ span) (r : TermCutRequest)
    (data : MonomialData (17*(Builder.allGates r.header.call).length))
    (t : Finset (Fin (17*(Builder.allGates r.header.call).length))×ℤ)
    (ht : t∈r.terms) (horder : data.order=t.1.sort (·≤·))
    (hcoeff : data.coefficient=t.2) (hcap : 400*stackInputMagnitude (r.stackRequest t ht)≤cap) :
    WExec cap (stackPrepare span hp) (data.reverseState r span data.order.length)
      ((data.reverseState r span data.order.length).sets
        (kernelSite span stackRecordPrinter.program hp).input (frame (r.stackRequest t ht).word))
      (10000*stackInputMagnitude (r.stackRequest t ht)) := by
  let P := kernelPacketMap span kernelStackSources stackRecordPrinter.program hp
  let R := kernelStackRegisters
  let σ := data.reverseState r span data.order.length
  have hb := data.reverseState_blank r span data.order.length stackRecordPrinter.program hp
  have he := StageStackInput.stackInputProgram_spec cap P R (r.stackRequest t ht)
    (finalHistoryPrefix r data) σ
  apply he
  · exact complete_history r data t ht horder span
  · exact complete_history_head r data span
  · change σ.st (kernelLocal span 7)=_
    simp [σ,MonomialData.reverseState,MonomialData.reverseData,KernelData.state,kernelLocal,
      TermCutRequest.preparedLoadedSource,TermCutRequest.preparedFields,
      CoefficientRequest.output,TermCutRequest.stackRequest]
  · change σ.st (kernelLocal span 16)=_
    simp [σ,MonomialData.reverseState,MonomialData.reverseData,KernelData.state,kernelLocal,
      CoefficientRequest.output,TermCutRequest.stackRequest,hcoeff]
  · change σ.st (kernelLocal span 8)=_
    simp [σ,MonomialData.reverseState,KernelData.state,kernelLocal,
      TermCutRequest.preparedLoadedSource,TermCutRequest.preparedFields,
      CoefficientRequest.output,TermCutRequest.stackRequest,
      NearCubicGates.Close.WordPrograms.SInt.encS]
  · intro i
    fin_cases i
    · change σ.sh (kernelLocal span 7)=0
      simp [σ,MonomialData.reverseState,KernelData.state,kernelLocal]
    · change σ.sh (kernelLocal span 16)=0
      simp [σ,MonomialData.reverseState,MonomialData.reverseData,KernelData.state,kernelLocal]
    · change σ.sh (kernelLocal span 8)=0
      simp [σ,MonomialData.reverseState,KernelData.state,kernelLocal]
    · exact hb.heads (NearCubicGates.Close.WorkerArith.inTape stackRecordPrinter.program)
  · exact hb.bank (NearCubicGates.Close.WorkerArith.inTape stackRecordPrinter.program)
  · intro i
    fin_cases i <;> simp [R,kernelStackRegisters,σ,MonomialData.reverseState,KernelData.state]
  · simp [R,kernelStackRegisters,σ,MonomialData.reverseState,MonomialData.reverseData,
      KernelData.state,processedSupport,horder,TermCutRequest.stackRequest,
      TermCutRequest.monomialTuples,tupleFields]
  · exact hcap

end NearQuarticWires.StageTupleMonomialFinish
