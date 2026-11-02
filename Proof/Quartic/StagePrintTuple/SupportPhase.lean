import Proof.Quartic.StagePrintTuple.PreparedCall
import Proof.Quartic.StagePrintTuple.InputContracts
import Proof.Quartic.StagePrintTuple.SupportIndexMachine
import Proof.Quartic.StageTupleInputs.SupportProgram

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageTuple

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close NearCubicGates.Close.WordPrograms NearCubicGates.Close.CheckedPCPP
open NearCubicGates.Close.Interfaces
open NearQuarticWires.Control

variable {ns nr : ℕ}

/-- `lem:print`, paper/paper.tex: support selection
constructs the genuine small request, calls the actual selector and
rewinds its copied variable codec by the measured copy counter. -/
noncomputable def supportPhaseProgram (P : Fin 2 ↪ Fin (ns+1))
    (R : Fin 9 ↪ Fin nr) (J M : Fin nr)
    (s : Site supportIndexWordFunction.program ns nr)
    (dst : Fin (ns+1)) (OP : Fin nr) : WMX ns nr :=
  .seq (preparedCallProgram (.wm (StageTupleInputs.supportInputProgram P R J M)) s dst OP)
    (.wm (WM.rewind dst OP))

/-- `prop:time`, paper/paper.tex: the genuine
selection phase pays its small source formatter, actual callee and
linear reply rewind, independently of the complete Terms stream. -/
def supportPhaseCost (r : SupportIndexRequest) : ℕ :=
  10000*(supportInputMagnitude r)^2+1+
    StagePrint.callAppendCost r.word.length r.budget+1+
      (5*(frame r.output).length+1)

/-- `lem:print` and `prop:time`, paper/paper.tex: the exact selected atom comes from the actual cached
support and physical reverse index. The public phase has neither a
selected-variable nor a preformatted-request premise. -/
theorem supportPhaseProgram_spec (cap : ℕ) (P : Fin 2 ↪ Fin (ns+1))
    (R : Fin 9 ↪ Fin nr) (J M : Fin nr)
    (s : Site supportIndexWordFunction.program ns nr)
    (dst : Fin (ns+1)) (OP : Fin nr) (hi : P 1=s.input)
    (r : SupportIndexRequest) (σ : WState ns nr)
    (blank : CallBlank supportIndexWordFunction.program s σ)
    (hRJ : ∀i,R i≠J) (hRM : ∀i,R i≠M)
    (hs : σ.st (P 0)=frame (listWord natWord r.support))
    (hh : σ.sh (P 0)=(marks (natWord r.support.length)).length)
    (hz : ∀i,σ.val (R i)=0) (hj : σ.val J=r.index.val)
    (hm : σ.val M=r.support.length)
    (hout : s.Out dst) (hL : dst≠s.ruler) (hOS : OP≠s.regs 0)
    (hd : σ.st dst=[]) (hdh : σ.sh dst=0) (hop : σ.val OP=0)
    (hinput : 1000*supportInputMagnitude r ≤ cap)
    (hcall : 2*r.word.length+2+r.budget ≤ cap)
    (houtput : (frame r.output).length+1 ≤ cap) :
    ∃τ,WXExec cap (supportPhaseProgram P R J M s dst OP) σ τ (supportPhaseCost r) ∧
      SimW (σ.sets dst (frame r.output)) τ := by
  have ep := StageTupleInputs.supportInputProgram_spec cap P R J M r σ hRJ hRM hs hh
    (by rw [hi];exact blank.bank (WorkerArith.inTape supportIndexWordFunction.program))
    (by rw [hi];exact blank.heads (WorkerArith.inTape supportIndexWordFunction.program))
    hz hj hm hinput
  have ep' : WXExec cap (.wm (StageTupleInputs.supportInputProgram P R J M)) σ
      (σ.sets s.input (frame r.word)) (10000*(supportInputMagnitude r)^2) := by
    simpa only [hi] using WXExec.wm ep
  obtain ⟨a,ea,ha⟩ := preparedCallProgram_spec supportIndexWordFunction r cap s dst OP
    hout hL hOS (.wm (StageTupleInputs.supportInputProgram P R J M))
    (10000*(supportInputMagnitude r)^2) σ blank ep'
    (by simp [hdh,hd]) hcall (by simpa [hop] using houtput)
  let b := appendO σ dst OP (frame r.output)
  have hbval : b.val OP=(frame r.output).length := by
    simp only [b,appendO_val,Function.update_self,hop,Nat.zero_add]
  have eb := wrewind_spec cap dst OP (frame r.output).length b
    hbval (by rw [hbval];omega)
  obtain ⟨c,ec,hc⟩ := wxexec_sim (WXExec.wm eb) a ha
  have heq : (b.setv OP 0).seth dst (b.sh dst-(frame r.output).length)=
      σ.sets dst (frame r.output) := by
    apply WState.eq
    · funext i
      by_cases h:i=dst
      · subst i;simp [b,appendO,hdh]
      · simp [b,appendO,Function.update_of_ne h]
    · simp [b,appendO,hd]
    · funext i
      by_cases h:i=OP
      · subst i;simp [hop]
      · simp [b,appendO,Function.update_of_ne h]
    · rfl
  refine ⟨c,?_,?_⟩
  · exact (ea.seq ec).mono (by unfold supportPhaseCost;omega)
  · simpa only [heq] using hc

end NearQuarticWires.StageTuple
