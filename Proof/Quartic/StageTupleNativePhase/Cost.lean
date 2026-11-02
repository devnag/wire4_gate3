import Proof.Quartic.StageTupleNativePhase.Post

set_option autoImplicit false

namespace NearQuarticWires.StageTupleNativePhase

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.WordPrograms
open StageTuple StageNativeKids

/-- `prop:time`, paper/paper.tex: the
actual binary count parser's power workspace is linear in that count. -/
theorem count_power_le (k : ℕ) : 2^(natBitLength k+1) ≤ 4*(k+1) := by
  unfold natBitLength
  have h := Nat.pow_log_le_add_one 2 k
  simp only [pow_succ]
  nlinarith only [h]

/-- `prop:time`, paper/paper.tex: the
exact native magnitude supplies the parser's physical register capacity,
with only its permitted additive squared-count resource. -/
theorem parse_capacity (B : NativeKidsRequest → ℕ) (r : NativeKidsRequest) :
    2^(natBitLength (r.toRowContext.nativeKids r.atom).length+1) ≤
      10000*nativePhaseMagnitude B r := by
  have hp := count_power_le (r.toRowContext.nativeKids r.atom).length
  have hs : (r.toRowContext.nativeKids r.atom).length+1 ≤
      ((r.toRowContext.nativeKids r.atom).length+1)^2 := Nat.le_self_pow (by decide) _
  unfold nativePhaseMagnitude
  omega

/-- `prop:time`, paper/paper.tex: all
physical source, real native call, measured reply and count-decoding
clocks fit the fixed linear native-phase magnitude. -/
theorem phase_clock_le {B : NativeKidsRequest → ℕ}
    (f : WordFunction NativeKidsRequest NativeKidsRequest.word NativeKidsRequest.output B)
    (r : NativeKidsRequest) :
    callClock B r+1+postClock r ≤ 1000000*nativePhaseMagnitude B r := by
  have hi := input_magnitude r
  have hf := reply_length f r
  have hr := natural_count_readCost_le (r.toRowContext.nativeKids r.atom).length
  have hb : (nativePhasePayload r).length ≤ B r+1 := by rw [frame_length] at hf; omega
  change 10000*nativeKidsInputMagnitude (nativePhaseSource r 0) (nativePhaseSource r 1)
      (nativePhaseSource r 2) (nativePhaseSource r 3) (nativePhaseSource r 4)+1+
      300*(r.word.length+B r+1)+1+
      (100*(frame (nativePhasePayload r)).length+100+1+
        (23*(nativePhasePayload r).length+5+1+
          (natBitLength (r.toRowContext.nativeKids r.atom).length+2)*
            (40*2^natBitLength (r.toRowContext.nativeKids r.atom).length+40))) ≤
    1000000*(r.word.length+B r+((r.toRowContext.nativeKids r.atom).length+1)^2+1)
  omega

end NearQuarticWires.StageTupleNativePhase
