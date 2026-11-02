import Proof.Quartic.StageTupleNativePhase.Cost

set_option autoImplicit false

namespace NearQuarticWires.StageTupleNativePhase

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close NearCubicGates.Close.WordPrograms
open StageTuple StageNativeKids

/-- `lem:print`, paper/paper.tex: five
genuine source frames are physically formatted, passed to the genuine
native machine, copied with complete call cleanup, measured, unframed
and parsed into the actual child count and ordered raw native pool. -/
noncomputable def nativePhaseProgram {B : NativeKidsRequest → ℕ}
    (f : WordFunction NativeKidsRequest NativeKidsRequest.word NativeKidsRequest.output B)
    (span : ℕ) (hf : f.program.tapeCount ≤ span) : WMX (span+29) 32 :=
  .seq (callProgram f span hf) (.wm (postProgram span))

/-- `lem:print` and `prop:time`, paper/paper.tex: the complete native source/call/count
phase satisfies the exact controller state, fixed capacity and fixed
clock contract, preserving every other exterior state component. -/
theorem nativePhaseProgram_spec : StageTuple.NativePhaseSpec nativePhaseProgram := by
  intro B f span hf cap r σ blank hs hh h18 hh18 h19 hh19 hz h13 h24 h25 hcap
  have hl := reply_length f r
  have hlen : (frame (nativePhasePayload r)).length ≤ cap := by
    unfold nativePhaseMagnitude at hcap
    omega
  obtain ⟨a, ea, ha⟩ := callProgram_spec f span hf cap r σ blank hs hh h18 hh18 hz hcap
  have ep := postProgram_spec span cap r σ h18 hh18 h19 hh19 hz h13 h24 h25 hlen
    ((parse_capacity B r).trans hcap)
  obtain ⟨τ, et, ht⟩ := CheckedPCPP.wxexec_sim (WXExec.wm ep) a ha
  exact ⟨τ, (ea.seq et).mono (phase_clock_le f r), ht⟩

end NearQuarticWires.StageTupleNativePhase
