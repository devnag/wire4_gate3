import Proof.Quartic.StagePrintTuple.KernelSupport
import Proof.Quartic.StagePrintTuple.KernelFinish
import Proof.Quartic.StagePrintTuple.ReverseBudget
import Proof.Quartic.StagePrintTuple.ReverseExact
import Proof.Quartic.StageTupleNativePhase.Final

set_option autoImplicit false

namespace NearQuarticWires.StageTuple

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.CheckedPCPP
open NearQuarticWires.Control

/-- `lem:print` and `prop:time`, paper/paper.tex: one complete physical reverse-support iteration
selects the original atom, constructs its actual native pool, performs
the genuine Cartesian call and returns the exact next reusable boundary. -/
theorem reverseBody_run {B : StageNativeKids.NativeKidsRequest→ℕ}
    (native : WordFunction StageNativeKids.NativeKidsRequest StageNativeKids.NativeKidsRequest.word
      StageNativeKids.NativeKidsRequest.output B)
    (r : TermCutRequest)
    (data : MonomialData (17*(Builder.allGates r.header.call).length))
    (span done cap : ℕ) (hd : done<data.order.length)
    (hn : native.program.tapeCount ≤ span)
    (hs : supportIndexWordFunction.program.tapeCount ≤ span)
    (ht : tupleRecordPrinter.program.tapeCount ≤ span)
    (hcap : reverseStepCapacity B r data done hd ≤ cap) :
    ∃τ,WXExec cap
      (kernelReverseBody StageTupleNativePhase.nativePhaseProgram native span hn hs ht)
      ((data.reverseState r span done).setv 15 (data.order.length-(done+1))) τ
      (reverseStepCost B r data done hd) ∧
        SimW (data.reverseState r span (done+1)) τ := by
  have hc := hcap
  dsimp only [reverseStepCapacity,RowContext.tupleStepRequest] at hc
  obtain ⟨a,ea,ha⟩ := kernelSupport_run r data span done cap hd hs
    (by
      try dsimp only [RowContext.tupleStepRequest]
      omega) (by
      try dsimp only [RowContext.tupleStepRequest]
      omega) (by
      try dsimp only [RowContext.tupleStepRequest]
      omega)
  obtain ⟨b,eb,hb⟩ := kernelNative_run StageTupleNativePhase.nativePhaseProgram
    StageTupleNativePhase.nativePhaseProgram_spec native r data span done cap hd hn (by
      try dsimp only [RowContext.tupleStepRequest]
      omega)
  obtain ⟨b',eb',hb'⟩ := wxexec_sim eb a ha
  have sb := SimW.trans hb hb'
  obtain ⟨c,ec,hc'⟩ := kernelCartesian_run r data span done cap hd ht
    (by
      try dsimp only [RowContext.tupleStepRequest]
      omega) (by
      try dsimp only [RowContext.tupleStepRequest]
      omega) (by
      try dsimp only [RowContext.tupleStepRequest]
      omega)
  obtain ⟨c',ec',hc''⟩ := wxexec_sim ec b' sb
  have sc := SimW.trans hc' hc''
  obtain ⟨d,ed,hd'⟩ := kernelFinish_run r data span done cap hd
    (by
      try dsimp only [RowContext.tupleStepRequest]
      omega) (by
      try dsimp only [RowContext.tupleStepRequest]
      omega) (by
      try dsimp only [RowContext.tupleStepRequest]
      omega) (by
      try dsimp only [RowContext.tupleStepRequest]
      omega) (by
      try dsimp only [RowContext.tupleStepRequest]
      omega) (by
      try dsimp only [RowContext.tupleStepRequest]
      omega) (by
      try dsimp only [RowContext.tupleStepRequest]
      omega)
  obtain ⟨d',ed',hd''⟩ := wxexec_sim ed c' sc
  have sd := SimW.trans hd' hd''
  have se : SimW (data.reverseState r span (done+1)) d' := by
    simpa only [reverseExact r data span done hd] using sd
  refine ⟨d',?_,se⟩
  simpa only [kernelReverseBody,reverseStepCost] using ea.seq (eb'.seq (ec'.seq ed'))

end NearQuarticWires.StageTuple
