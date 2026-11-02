import Proof.Quartic.StagePrintTuple.NativePhaseContract
import Proof.Quartic.StagePrintTuple.PreparedCall
import Proof.Quartic.StageTupleInputs.NativeProgram
import Proof.Gates.Cells.OutLen

set_option autoImplicit false

namespace NearQuarticWires.StageTupleNativePhase

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close NearCubicGates.Close.WordPrograms NearCubicGates.Close.Interfaces
open NearQuarticWires.Control
open StageTuple StageNativeKids

/-- `lem:print`, paper/paper.tex: the five
retained original fields encode exactly the existing native child request. -/
theorem input_word (r : NativeKidsRequest) :
    nativeKidsInputWord (nativePhaseSource r 0) (nativePhaseSource r 1)
      (nativePhaseSource r 2) (nativePhaseSource r 3) (nativePhaseSource r 4) = r.word := by
  simp [nativeKidsInputWord, nativePhaseSource, NativeKidsRequest.word,
    NativeKidsRequest.sourceFields]

/-- `prop:time`, paper/paper.tex: the source
formatter's actual magnitude is bounded by the literal complete request. -/
theorem input_magnitude (r : NativeKidsRequest) :
    nativeKidsInputMagnitude (nativePhaseSource r 0) (nativePhaseSource r 1)
      (nativePhaseSource r 2) (nativePhaseSource r 3) (nativePhaseSource r 4) ≤ r.word.length := by
  have hh := StageTupleInputs.nativeInput_length (nativePhaseSource r 0)
    (nativePhaseSource r 1) (nativePhaseSource r 2) (nativePhaseSource r 3) (nativePhaseSource r 4)
  rw [input_word, frame_length] at hh
  have h0 : 1 ≤ (frame (nativePhaseSource r 0)).length := by rw [frame_length]; omega
  have h1 : 1 ≤ (frame (nativePhaseSource r 1)).length := by rw [frame_length]; omega
  unfold nativeKidsInputMagnitude
  omega

/-- `lem:print`, paper/paper.tex: one fixed
physical packet formatter reads only the five retained source frames. -/
noncomputable def packetProgram (p : Program) (span : ℕ) (hp : p.tapeCount ≤ span) :
    WMX (span+29) 32 :=
  .wm (StageTupleInputs.nativeKidsInputProgram
    (kernelPacketMap span kernelNativeSources p hp) kernelNativeRegisters)

/-- `lem:print` and `prop:time`, paper/paper.tex: the actual blank call input receives the
exact native request through paid physical source-field copying. -/
theorem packetProgram_spec (p : Program) (span : ℕ) (hp : p.tapeCount ≤ span)
    (cap : ℕ) (r : NativeKidsRequest) (σ : WState (span+29) 32)
    (blank : CallBlank p (kernelSite span p hp) σ)
    (hs : ∀ i, σ.st (kernelLocal span (kernelNativeSources i)) = frame (nativePhaseSource r i))
    (hh : ∀ i, σ.sh (kernelLocal span (kernelNativeSources i)) = 0)
    (hz : ∀ i : Fin 10, σ.val ⟨i.val, by omega⟩ = 0)
    (hcap : 400*r.word.length ≤ cap) :
    WXExec cap (packetProgram p span hp) σ
      (σ.sets (kernelSite span p hp).input (frame r.word))
      (10000*nativeKidsInputMagnitude (nativePhaseSource r 0) (nativePhaseSource r 1)
        (nativePhaseSource r 2) (nativePhaseSource r 3) (nativePhaseSource r 4)) := by
  let P := kernelPacketMap span kernelNativeSources p hp
  have hsrc (i : Fin 5) : P (Fin.castAdd 1 i) = kernelLocal span (kernelNativeSources i) :=
    kernelPacketMap_source span kernelNativeSources p hp i
  have hi : P 5 = (kernelSite span p hp).input := kernelPacketMap_input span kernelNativeSources p hp
  have hdata (i : Fin 5) : σ.st (P (Fin.castAdd 1 i)) = frame (nativePhaseSource r i) := by
    rw [hsrc]
    exact hs i
  have hheads : ∀ i, σ.sh (P i) = 0 := by
    intro i
    refine Fin.addCases (fun j => ?_) (fun j : Fin 1 => ?_) i
    · rw [hsrc]
      exact hh j
    · have hj : j=0 := Fin.eq_zero j
      subst j
      change σ.sh (P 5)=0
      rw [hi]
      exact blank.heads (WorkerArith.inTape p)
  have e := StageTupleInputs.nativeKidsInputProgram_spec cap P kernelNativeRegisters
    (nativePhaseSource r 0) (nativePhaseSource r 1) (nativePhaseSource r 2)
    (nativePhaseSource r 3) (nativePhaseSource r 4) σ
    (hdata 0) (hdata 1) (hdata 2) (hdata 3) (hdata 4)
    (by rw [hi]; exact blank.bank (WorkerArith.inTape p)) hheads
    (by intro i; fin_cases i
        · simpa [kernelNativeRegisters] using hz (0 : Fin 10)
        · simpa [kernelNativeRegisters] using hz (1 : Fin 10))
    ((Nat.mul_le_mul_left 400 (input_magnitude r)).trans hcap)
  simpa only [packetProgram, hi, input_word] using WXExec.wm e

end NearQuarticWires.StageTupleNativePhase
