import Proof.Quartic.StageTupleNativePhase.Packet

set_option autoImplicit false

namespace NearQuarticWires.StageTupleNativePhase

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicGates.Close NearCubicGates.Close.WordPrograms
open NearQuarticWires.Control
open StageTuple StageNativeKids

variable {B : NativeKidsRequest → ℕ}

/-- `prop:time`, paper/paper.tex: the
genuine native computation's finite framed reply is bounded by its own
physical runtime, without installing an output-length observation. -/
theorem reply_length (f : WordFunction NativeKidsRequest NativeKidsRequest.word NativeKidsRequest.output B)
    (r : NativeKidsRequest) : (frame (nativePhasePayload r)).length ≤ B r+1 :=
  Cells.wf_out_len f r

/-- `lem:print`, paper/paper.tex: the
physical source formatter precedes the genuine native call, literal
framed-reply copy and complete reusable-bank cleanup. -/
noncomputable def callProgram
    (f : WordFunction NativeKidsRequest NativeKidsRequest.word NativeKidsRequest.output B)
    (span : ℕ) (hf : f.program.tapeCount ≤ span) : WMX (span+29) 32 :=
  preparedCallProgram (packetProgram f.program span hf)
    (kernelSite span f.program hf) (kernelLocal span 18) 0

/-- `prop:time`, paper/paper.tex: source
formatting and the actual ordinary call have their complete additive clocks. -/
def callClock (B : NativeKidsRequest → ℕ) (r : NativeKidsRequest) : ℕ :=
  10000*nativeKidsInputMagnitude (nativePhaseSource r 0) (nativePhaseSource r 1)
    (nativePhaseSource r 2) (nativePhaseSource r 3) (nativePhaseSource r 4)+1+
      StagePrint.callAppendCost r.word.length (B r)

/-- `lem:print` and `prop:time`, paper/paper.tex: the actual five source frames produce the
real native reply and its physically measured byte counter, preserving
all exterior state while restoring the complete call bank. -/
theorem callProgram_spec
    (f : WordFunction NativeKidsRequest NativeKidsRequest.word NativeKidsRequest.output B)
    (span : ℕ) (hf : f.program.tapeCount ≤ span) (cap : ℕ) (r : NativeKidsRequest)
    (σ : WState (span+29) 32) (blank : CallBlank f.program (kernelSite span f.program hf) σ)
    (hs : ∀ i, σ.st (kernelLocal span (kernelNativeSources i)) = frame (nativePhaseSource r i))
    (hh : ∀ i, σ.sh (kernelLocal span (kernelNativeSources i)) = 0)
    (hd : σ.st (kernelLocal span 18)=[]) (hdh : σ.sh (kernelLocal span 18)=0)
    (hz : ∀ i : Fin 10, σ.val ⟨i.val, by omega⟩=0)
    (hcap : 10000*nativePhaseMagnitude B r ≤ cap) :
    ∃ τ, WXExec cap (callProgram f span hf) σ τ (callClock B r) ∧
      SimW (appendO σ (kernelLocal span 18) 0 (frame (nativePhasePayload r))) τ := by
  have hl := reply_length f r
  have h0 : σ.val (0 : Fin 32)=0 := hz 0
  have ep := packetProgram_spec f.program span hf cap r σ blank hs hh hz (by
    unfold nativePhaseMagnitude at hcap
    omega)
  have hout := kernelSite_out span f.program hf (18 : Fin 30) (by decide) (by decide)
  have hL := kernelSite_ruler_ne span f.program hf (18 : Fin 30) (by decide)
  have hOS : (0 : Fin 32)≠(kernelSite span f.program hf).regs 0 := by
    change (0 : Fin 32)≠20
    decide
  exact preparedCallProgram_spec (cache:=nativePhasePayload) f r cap (kernelSite span f.program hf) (kernelLocal span 18) 0
    hout hL hOS (packetProgram f.program span hf) _ σ blank ep (by simp [hdh, hd])
    (by unfold nativePhaseMagnitude at hcap; omega)
    (by rw [h0]; unfold nativePhaseMagnitude at hcap; omega)

end NearQuarticWires.StageTupleNativePhase
