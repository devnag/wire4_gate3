import Proof.Quartic.StagePrintTuple.CallInput

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageTuple

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicGates.Close NearCubicGates.Close.WordPrograms
open NearQuarticWires.Control

variable {ns nr : ℕ}

/-- `lem:print`, paper/paper.tex: a real source
packet constructor is immediately followed by its genuine ordinary
callee, finite framed-reply copy and complete work-bank cleanup. -/
noncomputable def preparedCallProgram {p : Program} (prepare : WMX ns nr)
    (s : Site p ns nr) (dst : Fin (ns+1)) (OP : Fin nr) : WMX ns nr :=
  .seq prepare (StagePrint.callAppendProgram s dst OP)

/-- `lem:print` and `prop:time`, paper/paper.tex: a physically constructed exact input invokes the actual
callee and leaves only its real framed reply and measured output-byte
counter outside the now blank work bank. -/
theorem preparedCallProgram_spec {Request : Type} {input cache : Request→List Bool}
    {budget : Request→ℕ}
    (f : WordFunction Request input (fun r=>frame (cache r)) budget) (req : Request)
    (cap : ℕ) (s : Site f.program ns nr) (dst : Fin (ns+1)) (OP : Fin nr)
    (hout : s.Out dst) (hL : dst≠s.ruler) (hOS : OP≠s.regs 0)
    (prepare : WMX ns nr) (prepareCost : ℕ) (σ : WState ns nr)
    (blank : CallBlank f.program s σ)
    (he : WXExec cap prepare σ (σ.sets s.input (frame (input req))) prepareCost)
    (hd : σ.sh dst=(σ.st dst).length)
    (hcap : 2*(input req).length+2+budget req≤cap)
    (hOut : σ.val OP+(frame (cache req)).length+1≤cap) :
    ∃τ,WXExec cap (preparedCallProgram prepare s dst OP) σ τ
      (prepareCost+1+StagePrint.callAppendCost (input req).length (budget req)) ∧
      SimW (appendO σ dst OP (frame (cache req))) τ := by
  let a := σ.sets s.input (frame (input req))
  have hdi : dst≠s.input := by
    intro hh
    exact hout.1 (NearCubicGates.Close.WorkerArith.inTape f.program) hh.symm
  obtain ⟨τ,et,hτ⟩ := framedCall_ready f req cap s dst OP hout.1 hout.2.1 hout.2.2 hL hOS a
    (blank.ready (input req)) (by simpa [a,hdi] using hd) hcap hOut
  have hc : cleanState s a=σ := by
    unfold a Site.input
    rw [StagePrint.cleanState_set_bank]
    exact blank.clean
  rw [hc] at hτ
  exact ⟨τ,he.seq et,hτ⟩

end NearQuarticWires.StageTuple
