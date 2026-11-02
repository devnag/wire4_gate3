import Proof.Quartic.StageTupleNativePhase.Decode

set_option autoImplicit false

namespace NearQuarticWires.StageTupleNativePhase

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.TabMachine
open StageTuple StageNativeKids

/-- `lem:print`, paper/paper.tex: the
genuine copied native reply is measured, unframed and parsed using only
its actual bytes and the existing finite controller registers. -/
def postProgram (span : ℕ) : WM (span+29) 32 :=
  .seq (measureProgram (kernelLocal span 18))
    (decodeProgram (kernelLocal span 18) (kernelLocal span 19))

/-- `prop:time`, paper/paper.tex: actual
reply measurement and decoding contribute their complete additive clocks. -/
def postClock (r : NativeKidsRequest) : ℕ :=
  100*(frame (nativePhasePayload r)).length+100+1+
    decodeClock (r.toRowContext.nativeKids r.atom).length
      (fieldsRecs r.outputWidth (r.toRowContext.nativeKids r.atom))

/-- `lem:print` and `prop:time`, paper/paper.tex: the physical reply-copy counter gives
both exact byte counts, and the actual raw count codec determines the
child count and final pool cursor; every other state component remains. -/
theorem postProgram_spec (span cap : ℕ) (r : NativeKidsRequest) (σ : WState (span+29) 32)
    (h18 : σ.st (kernelLocal span 18)=[]) (hh18 : σ.sh (kernelLocal span 18)=0)
    (h19 : σ.st (kernelLocal span 19)=[]) (hh19 : σ.sh (kernelLocal span 19)=0)
    (hz : ∀ i : Fin 10, σ.val ⟨i.val, by omega⟩=0)
    (h13 : σ.val 13=0) (h24 : σ.val 24=0) (h25 : σ.val 25=0)
    (hlen : (frame (nativePhasePayload r)).length ≤ cap)
    (hpow : 2^(natBitLength (r.toRowContext.nativeKids r.atom).length+1) ≤ cap) :
    WExec cap (postProgram span)
      (appendO σ (kernelLocal span 18) 0 (frame (nativePhasePayload r)))
      (nativePhaseState span r σ) (postClock r) := by
  have em := measureProgram_spec cap (kernelLocal span 18) (nativePhasePayload r) σ
    h18 hh18 (hz 0) (hz 1) (hz 6) h24 h25 hlen
  have ed := decodeProgram_spec cap (kernelLocal span 18) (kernelLocal span 19)
    ((kernelLocal span).injective.ne (by decide))
    (r.toRowContext.nativeKids r.atom).length
    (fieldsRecs r.outputWidth (r.toRowContext.nativeKids r.atom)) σ hh18 h19 hh19
    (by intro i; exact hz ⟨i.val, by have := i.isLt; omega⟩) h13
    (by change (nativePhasePayload r).length ≤ cap; rw [frame_length] at hlen; omega) hpow
  exact em.seq ed

end NearQuarticWires.StageTupleNativePhase
