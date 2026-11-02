import Proof.Quartic.StagePrintTuple.CallInput

set_option autoImplicit false

namespace NearQuarticWires.StageTupleMonomialFinish

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicGates.Close NearCubicGates.Close.WordPrograms
open NearQuarticWires.Control StageTuple

variable {ns nr : ℕ}

/-- `lem:print`, paper/paper.tex: the actual
Stack input formatter is followed by a raw-record call and complete
callee cleanup, retaining the preceding signed cut stream. -/
noncomputable def preparedRecordsProgram {p : Program} (prepare : WMX ns nr)
    (s : Site p ns nr) (dst : Fin (ns+1)) (OP : Fin nr) : WMX ns nr :=
  .seq prepare (callRecordsProgram s dst OP)

/-- `lem:print` and `prop:time`, paper/paper.tex: an exact physically prepared input invokes its genuine
raw-record machine and appends its actual reply, with every call,
record copy and finite work-bank cleanup charged. -/
theorem preparedRecordsProgram_spec {Request : Type} {input : Request→List Bool}
    {records : Request→List (List Bool)} {budget : Request→ℕ}
    (f : WordFunction Request input (fun r=>(records r).flatMap frame) budget) (req : Request)
    (hne : ∀ record∈records req,record≠[]) (cap : ℕ)
    (s : Site f.program ns nr) (dst : Fin (ns+1)) (OP : Fin nr)
    (hout : s.Out dst) (hL : dst≠s.ruler) (hOS : OP≠s.regs 0)
    (prepare : WMX ns nr) (prepareCost : ℕ) (σ : WState ns nr)
    (blank : CallBlank f.program s σ)
    (he : WXExec cap prepare σ (σ.sets s.input (frame (input req))) prepareCost)
    (hd : σ.sh dst=(σ.st dst).length)
    (hcap : 2*(input req).length+2+budget req≤cap)
    (hOut : σ.val OP+((records req).flatMap frame).length+1≤cap) :
    ∃τ,WXExec cap (preparedRecordsProgram prepare s dst OP) σ τ
      (prepareCost+1+callRecordsCost (input req).length (budget req)) ∧
      SimW (appendO σ dst OP ((records req).flatMap frame)) τ := by
  let a := σ.sets s.input (frame (input req))
  have hdi : dst≠s.input := by
    intro hh
    exact hout.1 (NearCubicGates.Close.WorkerArith.inTape f.program) hh.symm
  obtain ⟨τ,et,hτ⟩ := recordsCall_ready f req hne cap s dst OP hout.1 hout.2.1 hout.2.2
    hL hOS a (blank.ready (input req)) (by simpa [a,hdi] using hd) hcap hOut
  have hc : cleanState s a=σ := by
    unfold a Site.input
    rw [StagePrint.cleanState_set_bank]
    exact blank.clean
  rw [hc] at hτ
  exact ⟨τ,he.seq et,hτ⟩

end NearQuarticWires.StageTupleMonomialFinish
