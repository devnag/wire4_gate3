import Proof.Quartic.StagePrintTuple.PreparedCall
import Proof.Gates.Codec.Unframe

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

/-- `lem:print`, paper/paper.tex: a genuine
finite cached packet is copied and rewound, passed to its actual cold
callee, then its copied framed reply is rewound by the real byte count. -/
noncomputable def cachedCallProgram {p : Program} (s : Site p ns nr)
    (src dst : Fin (ns+1)) (OP T D : Fin nr) : WMX ns nr :=
  .seq (preparedCallProgram (.wm (Codec.copyRW src s.input OP T D)) s dst OP)
    (.wm (WM.rewind dst OP))

/-- `prop:time`, paper/paper.tex: cached small
source calls have additive actual copying, callee and reply-rewind cost;
neither earlier Terms nor history prefixes enter the packet clock. -/
def cachedCallCost (inputLength budget replyLength : ℕ) : ℕ :=
  100*(inputLength+1)+1+StagePrint.callAppendCost inputLength budget+1+5*replyLength+1

/-- `lem:print` and `prop:time`, paper/paper.tex: actual finite source copying establishes the real cold
input and yields exactly the cached framed reply, preserving all other
source bytes, cursors and registers after genuine call-bank cleanup. -/
theorem cachedCallProgram_spec {Request : Type} {input cache : Request→List Bool}
    {budget : Request→ℕ}
    (f : WordFunction Request input (fun r=>frame (cache r)) budget) (r : Request)
    (cap : ℕ) (s : Site f.program ns nr) (src dst : Fin (ns+1)) (OP T D : Fin nr)
    (hsi : src≠s.input) (hOT : OP≠T) (hOD : OP≠D) (hTD : T≠D)
    (hout : s.Out dst) (hL : dst≠s.ruler) (hOS : OP≠s.regs 0)
    (σ : WState ns nr) (blank : CallBlank f.program s σ)
    (hs : σ.st src=frame (input r)) (hsh : σ.sh src=0)
    (hd : σ.st dst=[]) (hdh : σ.sh dst=0)
    (ho : σ.val OP=0) (ht : σ.val T=0) (hdv : σ.val D=0)
    (hcopy : 4*(input r).length+4 ≤ cap)
    (hcall : 2*(input r).length+2+budget r ≤ cap)
    (houtput : (frame (cache r)).length+1 ≤ cap) :
    ∃τ,WXExec cap (cachedCallProgram s src dst OP T D) σ τ
      (cachedCallCost (input r).length (budget r) (frame (cache r)).length) ∧
      SimW (σ.sets dst (frame (cache r))) τ := by
  have ep := Codec.copyRW_spec cap src s.input hsi OP T D hOT hOD hTD (input r) [] σ
    (by simpa using hs) hsh (blank.bank (WorkerArith.inTape f.program))
    (blank.heads (WorkerArith.inTape f.program)) ho ht hdv hcopy
  have ep' : WXExec cap (.wm (Codec.copyRW src s.input OP T D)) σ
      (σ.sets s.input (frame (input r))) (100*((input r).length+1)) :=
    (WXExec.wm ep).mono (by omega)
  obtain ⟨a,ea,ha⟩ := preparedCallProgram_spec f r cap s dst OP hout hL hOS
    (.wm (Codec.copyRW src s.input OP T D)) (100*((input r).length+1)) σ blank ep'
    (by simp [hdh,hd]) hcall (by simpa [ho] using houtput)
  let b := appendO σ dst OP (frame (cache r))
  have hv : b.val OP=(frame (cache r)).length := by
    simp only [b,appendO_val,Function.update_self,ho,Nat.zero_add]
  have eb := wrewind_spec cap dst OP (frame (cache r)).length b hv (by rw [hv];omega)
  obtain ⟨c,ec,hc⟩ := wxexec_sim (WXExec.wm eb) a ha
  have heq : (b.setv OP 0).seth dst (b.sh dst-(frame (cache r)).length)=
      σ.sets dst (frame (cache r)) := by
    apply WState.eq
    · funext i
      by_cases hi:i=dst
      · subst i;simp [b,appendO,hdh]
      · simp [b,appendO,Function.update_of_ne hi]
    · simp [b,appendO,hd]
    · funext i
      by_cases hi:i=OP
      · subst i;simp [ho]
      · simp [b,appendO,Function.update_of_ne hi]
    · rfl
  exact ⟨c,(ea.seq ec).mono (by unfold cachedCallCost;omega),by simpa only [heq] using hc⟩

end NearQuarticWires.StageTuple
