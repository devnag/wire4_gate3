import Proof.Quartic.StageTupleNativePhase.Measure
import Proof.Quartic.StagePrintTuple.TermsCount
import Proof.Wire_3_5.PrimAsmParseNat

set_option autoImplicit false

namespace NearQuarticWires.StageTupleNativePhase

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat
open NearCubicGates.Close.WordPrograms

variable {ns : ℕ}

/-- `lem:print`, paper/paper.tex: both
literal reply caches, their measured lengths and the physically parsed
original child count remain after decoding. -/
def decodedState (σ : WState ns 32) (src dst : Fin (ns+1)) (k : ℕ)
    (rows : List Bool) : WState ns 32 :=
  let bits := natWord k++rows
  ((((((σ.sets src (frame bits)).seth src (frame bits).length).sets dst bits).seth dst
    (natWord k).length).setv 13 k).setv 24 (frame bits).length).setv 25 bits.length

/-- `lem:print`, paper/paper.tex: actual
reply bytes are unframed and their real leading binary child count is
read from the resulting raw pool tape. -/
def decodeProgram (src dst : Fin (ns+1)) : WM ns 32 :=
  .seq (StageGamma.unframeRecord src dst 0) (readNatM false dst 0 1 13 2 3)

/-- `prop:time`, paper/paper.tex: reply
decoding pays a linear unframe scan and the actual natural-number parser. -/
def decodeClock (k : ℕ) (rows : List Bool) : ℕ :=
  23*(natWord k++rows).length+5+1+(natBitLength k+2)*(40*2^natBitLength k+40)

/-- `lem:print` and `prop:time`, paper/paper.tex: the leading count is physically parsed
from the genuine unframed reply; all unrelated state is preserved. -/
theorem decodeProgram_spec (cap : ℕ) (src dst : Fin (ns+1)) (hsd : src≠dst)
    (k : ℕ) (rows : List Bool) (σ : WState ns 32)
    (hsrc : σ.sh src=0) (hdst : σ.st dst=[]) (hdsh : σ.sh dst=0)
    (hz : ∀ i : Fin 4, σ.val ⟨i.val, by omega⟩=0) (h13 : σ.val 13=0)
    (hlen : (natWord k++rows).length ≤ cap) (hpow : 2^(natBitLength k+1) ≤ cap) :
    WExec cap (decodeProgram src dst) (measuredState σ src (natWord k++rows))
      (decodedState σ src dst k rows) (decodeClock k rows) := by
  let bits := natWord k++rows
  let a := measuredState σ src bits
  have a0 : a.val (0 : Fin 32)=0 := by simpa [a, measuredState] using hz 0
  have ad : a.st dst=[] := by simp [a, measuredState, Function.update_of_ne hsd.symm, hdst]
  have ea := StageGamma.unframeRecord_run cap src dst hsd 0 bits [] [] a
    (by simp [a, measuredState]) (by simp [a, measuredState, hsrc])
    (by change σ.sh dst=(a.st dst).length; rw [hdsh, ad]; rfl) a0 hlen
  let b := (a.sets dst bits).seth src (frame bits).length
  have eu : WExec cap (StageGamma.unframeRecord src dst 0) a b (23*bits.length+5) := by
    simpa only [b, List.length_nil, Nat.zero_add, ad, List.nil_append, frame_length] using ea
  have eb := readNatM_spec cap false dst (0 : Fin 32) 1 13 2 3
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    k [] rows b
    (by simp [b, bits, WireExponent3_5.PrimAsm.ParseNat.enc])
    (by simp [b, a, measuredState, Function.update_of_ne hsd.symm, hdsh])
    (by simp [b, a0]) (by simpa [b, a, measuredState] using hz (1 : Fin 4))
    (by simpa [b, a, measuredState] using hz (2 : Fin 4))
    (by simpa [b, a, measuredState] using hz (3 : Fin 4))
    (by simpa [b, a, measuredState, h13] using hpow)
  refine (eu.seq eb).cast cap ?_ ?_
  · apply WState.eq
    · funext i
      by_cases hi : i=dst
      · subst i
        simp [decodedState, b, a, measuredState, bits, stp]
      · by_cases his : i=src
        · subst i
          simp [decodedState, b, a, measuredState, bits, stp, hi]
        · simp [decodedState, b, a, measuredState, bits, stp, hi, his]
    · simp [decodedState, b, a, measuredState, bits]
    · funext i
      by_cases hi : i=13
      · subst i
        simp [decodedState, b, a, measuredState, h13]
      · by_cases h24 : i=24
        · subst i
          simp [decodedState, b, a, measuredState, bits]
        · by_cases h25 : i=25
          · subst i
            simp [decodedState, b, a, measuredState, bits]
          · simp [decodedState, b, a, measuredState, hi, h24, h25]
    · rfl
  · rfl

end NearQuarticWires.StageTupleNativePhase
