import Proof.Quartic.StagePrintTuple.Calls
import Proof.Quartic.StagePrintTuple.HistoryClose
import Proof.Quartic.StagePrintTuple.RecordOutputs
import Proof.Quartic.Control.Round

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageTuple

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicGates.Close NearCubicGates.Close.WordPrograms NearCubicGates.Close.CheckedPCPP
open NearQuarticWires.Control

variable {ns nr : ℕ}

/-- `lem:print`, paper/paper.tex: the genuine
Cartesian child machine appends its actual new tuple records to the
retained history, cleans its complete work bank, then selects the new
segment with its physically emitted-byte counter. -/
noncomputable def cartesianReplyProgram (s : Site tupleRecordPrinter.program ns nr)
    (history : Fin (ns+1)) (OP : Fin nr) : WMX ns nr :=
  .seq (callRecordsProgram s history OP) (.wm (closeRecordHistory history OP))

/-- `prop:time`, paper/paper.tex: the genuine
Cartesian call, raw record copy, work-bank cleanup and new-segment
rewind have one additive physical clock. -/
def cartesianReplyCost (r : StagePrint.ChildTupleRequest) : ℕ :=
  callRecordsCost r.word.length (2*r.budget+2)+
    10*(((tupleRecords r).flatMap frame).length+1)+21

/-- `lem:print` and `prop:time`, paper/paper.tex: one actual cold Cartesian call returns exactly the
new child-first tuple segment, preserving its original signed fields
and retaining the entire older history without recopying it. -/
theorem cartesianReplyProgram_spec (cap : ℕ) (r : StagePrint.ChildTupleRequest)
    (s : Site tupleRecordPrinter.program ns nr) (history : Fin (ns+1)) (OP : Fin nr)
    (hout : s.Out history) (hL : history≠s.ruler) (hOS : OP≠s.regs 0)
    (σ : WState ns nr) (ready : CallReady tupleRecordPrinter.program s r.word σ)
    (hh : σ.sh history=(σ.st history).length) (ho : σ.val OP=0)
    (hcap : 2*r.word.length+2+(2*r.budget+2)≤cap)
    (hcapOut : ((tupleRecords r).flatMap frame).length+1≤cap) :
    ∃τ,WXExec cap (cartesianReplyProgram s history OP) σ τ (cartesianReplyCost r) ∧
      SimW
        (closedHistory
          (appendO (cleanState s σ) history OP ((tupleRecords r).flatMap frame))
          history OP (σ.st history) ((tupleRecords r).flatMap frame)) τ := by
  obtain ⟨a,ea,ha⟩ := recordsCall_ready tupleRecordPrinter r (tupleRecords_nonempty r) cap s history OP
    hout.1 hout.2.1 hout.2.2 hL hOS σ ready hh hcap (by simpa only [ho,Nat.zero_add] using hcapOut)
  let ideal := appendO (cleanState s σ) history OP ((tupleRecords r).flatMap frame)
  have hclean := cleanState_out s σ history hout
  have ec := closeRecordHistory_spec cap history OP (σ.st history) ((tupleRecords r).flatMap frame) ideal
    (by simp only [ideal,appendO_st,Function.update_self,hclean.1])
    (by simp only [ideal,appendO_sh,appendO_st,Function.update_self,hclean.1,hclean.2,hh,List.length_append])
    (by simp [ideal,appendO,cleanState,ho]) hcapOut
  obtain ⟨τ,et,hτ⟩ := wxexec_sim (WXExec.wm ec) a ha
  refine ⟨τ,(ea.seq et).mono ?_,hτ⟩
  unfold cartesianReplyCost
  omega

end NearQuarticWires.StageTuple
