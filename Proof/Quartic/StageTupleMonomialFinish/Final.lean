import Proof.Quartic.StageTupleMonomialFinish.State
import Proof.Quartic.StageTupleMonomialFinish.Bounds

set_option autoImplicit false

namespace NearQuarticWires.StageTupleMonomialFinish

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.CheckedPCPP
open StageTuple

/-- `lem:print`, paper/paper.tex: the actual
post-reverse monomial program formats and invokes Stack, appends its
raw signed cuts, erases the finite caches and selects the next real
empty tuple segment with all local counters cleared. -/
noncomputable def monomialFinishProgram (span : ℕ)
    (hp : stackRecordPrinter.program.tapeCount ≤ span) : WMX (span+29) 32 :=
  .seq (stackPhase span hp) (.seq (cachesProgram span) (resetProgram span))

/-- `lem:print` and `prop:time`, paper/paper.tex: the genuine post-reverse finish satisfies the exact
monomial boundary and fixed local clock, without an external Stack
supplier or a runtime dependence on earlier source/history/output. -/
theorem monomialFinishProgram_spec : StageTuple.MonomialFinishSpec monomialFinishProgram := by
  intro span hp cap r data t ht horder hcoeff hcap
  obtain ⟨hinput,hcall,hout,hc,hr,hs,hcount,hfields⟩ := finish_capacity r data t ht cap hcap
  obtain ⟨a,ea,ha⟩ := stackPhase_spec span cap hp r data t ht horder hcoeff hinput hcall hout
  obtain ⟨b,eb,hb⟩ := kernelCaches_spec span cap r data t ht hc hr hs
  obtain ⟨b',eb',hb'⟩ := wxexec_sim eb a ha
  have hbb := SimW.trans hb hb'
  have ec := kernelReset_spec span cap r data t ht horder hcount hfields
  obtain ⟨c,ec',hc'⟩ := wxexec_sim ec b' hbb
  refine ⟨c,(ea.seq (eb'.seq ec')).mono (finishCost_le r data t ht),?_⟩
  simpa only [finishState_eq] using hc'

end NearQuarticWires.StageTupleMonomialFinish
